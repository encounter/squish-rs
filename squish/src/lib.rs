// Copyright (c) 2006 Simon Brown <si@sjbrown.co.uk>
// Copyright (c) 2018-2021 Jan Solanti <jhs@psonet.com>
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to	deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
// OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
// SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

//! A pure Rust BC1/2/3 compressor and decompressor based on Simon Brown's
//! **libsquish**

#![no_std]

#[cfg(feature="rayon")]
use rayon::prelude::*;

use crate::colourfit::{ClusterFit, ColourFit, RangeFit, SingleColourFit};
use crate::colourset::ColourSet;

mod alpha;
mod colourblock;
mod colourfit;
mod colourset;
mod math;

/// Defines a compression format
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Format {
    Bc1,
    /// CMPR format used on GameCube & Wii
    /// Essentially standard BC1 with big-endian byte order
    /// and small changes to color blocks
    Bc1Gcn,
    Bc2,
    Bc3,
    Bc4,
    Bc5,
}

/// Defines a compression algorithm
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Algorithm {
    /// Fast, low quality
    RangeFit,

    /// Slow, high quality
    ClusterFit,

    /// Very slow, very high quality
    IterativeClusterFit,
}

impl Default for Algorithm {
    fn default() -> Self {
        Algorithm::ClusterFit
    }
}

/// RGB colour channel weights for use in block fitting
pub type ColourWeights = [f32; 3];

/// Uniform weights for each colour channel
pub const COLOUR_WEIGHTS_UNIFORM: ColourWeights = [1.0, 1.0, 1.0];

/// Weights based on the perceived brightness of each colour channel
pub const COLOUR_WEIGHTS_PERCEPTUAL: ColourWeights = [0.2126, 0.7152, 0.0722];

/// Perceptual weights used for GCN/CMPR encoding
pub const COLOUR_WEIGHTS_PERCEPTUAL_GCN: ColourWeights = [0.3086, 0.6094, 0.0820];

#[derive(Clone, Copy)]
pub struct Params {
    /// The compression algorithm to be used
    pub algorithm: Algorithm,

    /// Weigh the relative importance of each colour channel when fitting
    /// (defaults to perceptual weights)
    pub weights: ColourWeights,

    /// Weigh colour by alpha during cluster fit (defaults to false)
    ///
    /// This can significantly increase perceived quality for images that are rendered
    /// using alpha blending.
    pub weigh_colour_by_alpha: bool,
}

impl Default for Params {
    fn default() -> Self {
        Params {
            algorithm: Algorithm::default(),
            weights: COLOUR_WEIGHTS_PERCEPTUAL,
            weigh_colour_by_alpha: false,
        }
    }
}

/// Returns number of blocks needed for an image of given dimension
pub fn num_blocks(size: usize) -> usize {
    (size + 3) / 4
}

/// BCn formats are laid out in 8-byte blocks of the following types:
/// * BC1: colour with optional 1-bit alpha
/// * BC2: paletted alpha, colour
/// * BC3: gradient alpha, colour
/// * BC4: gradient alpha
/// * BC5: gradient alpha, gradient alpha
///
/// BC4 and BC5 reuse the alpha compression scheme for arbitrary one- and two-channel images.
/// Graphics APIs commonly refer to them as "grayscale", "luminance" or simply "red" for BC4 and
/// "rg" or "luminance + alpha" for BC5 respectively.
impl Format {
    /// Decompresses an image in memory
    ///
    /// * `data`   - The compressed image data
    /// * `width`  - The width of the source image
    /// * `height` - The height of the source image
    /// * `output` - Space to store the decompressed image
    pub fn decompress(self, data: &[u8], width: usize, height: usize, output: &mut [u8]) {
        let blocks_wide = num_blocks(width);
        let block_size = self.block_size();

        #[cfg(feature="rayon")]
        let output_rows = output.par_chunks_mut(width * 4 * 4);
        #[cfg(not(feature="rayon"))]
        let output_rows = output.chunks_mut(width * 4 * 4);

        // loop over blocks
        output_rows.enumerate().for_each(|(y, output_row)| {
            for x in 0..blocks_wide {
                // decompress the block
                let bidx = (x + y * blocks_wide) * block_size;
                let rgba = self.decompress_block(&data[bidx..bidx + block_size]);

                // write the decompressed pixels to the correct image location
                for py in 0..4 {
                    for px in 0..4 {
                        // get target location
                        let sx = 4 * x + px;
                        let sy = py;

                        if sx < width && sy < height {
                            for i in 0..4 {
                                output_row[4 * (sx + sy * width) + i] = rgba[px + py * 4][i];
                            }
                        }
                    }
                }
            }
        });
    }

    /// Returns how many bytes a 4x4 block of pixels will compress into
    pub fn block_size(self) -> usize {
        // Compressed block size in bytes
        match self {
            Format::Bc1 | Format::Bc1Gcn => 8,
            Format::Bc2 => 16,
            Format::Bc3 => 16,
            Format::Bc4 => 8,
            Format::Bc5 => 16,
        }
    }

    /// Computes the amount of space in bytes needed for an image of given size,
    /// accounting for padding to a multiple of 4x4 pixels
    ///
    /// * `width`  - Width of the uncompressed image
    /// * `height` - Height of the uncompressed image
    pub fn compressed_size(self, width: usize, height: usize) -> usize {
        // Number of blocks required for image of given dimensions
        let blocks = num_blocks(width) * num_blocks(height);
        blocks * self.block_size()
    }

    /// Compresses a 4x4 block of pixels, masking out some pixels e.g. for padding the
    /// image to a multiple of the block size.
    ///
    /// * `rgba`   - The uncompressed block of pixels
    /// * `mask`   - The valid pixel mask
    /// * `params` - Additional compressor parameters
    /// * `output` - Storage for the compressed block
    pub fn compress_block_masked(
        self,
        rgba: [[u8; 4]; 16],
        mask: u32,
        params: Params,
        output: &mut [u8],
    ) {
        // compress alpha block(s)
        match self {
            Format::Bc1 | Format::Bc1Gcn => {},
            Format::Bc2 => alpha::compress_bc2(&rgba, mask, &mut output[..8]),
            Format::Bc3 => alpha::compress_bc3(&rgba, 3, mask, &mut output[..8]),
            Format::Bc4 => alpha::compress_bc3(&rgba, 0, mask, &mut output[..8]),
            Format::Bc5 => {
                alpha::compress_bc3(&rgba, 0, mask, &mut output[0..8]);
                alpha::compress_bc3(&rgba, 1, mask, &mut output[8..16]);
            },
        }

        // compress colour block if the format has one
        match self {
            Format::Bc1 | Format::Bc1Gcn | Format::Bc2 | Format::Bc3 => {
                // create the minimal point set
                let colours = ColourSet::new(&rgba, mask, self, params.weigh_colour_by_alpha);

                let colour_offset = if self == Format::Bc1 || self == Format::Bc1Gcn { 0 } else { 8 };
                let colour_block = &mut output[colour_offset..colour_offset + 8];

                // compress with appropriate compression algorithm
                if colours.count() == 1 {
                    // Single colour fit can't handle fully transparent blocks, hence the
                    // set has to contain at least 1 colour. It's also not very useful for
                    // anything more complex so we only use it for blocks of uniform colour.
                    let mut fit = SingleColourFit::new(&colours, self);
                    fit.compress(colour_block);
                } else if (params.algorithm == Algorithm::RangeFit) || (colours.count() == 0) {
                    let mut fit = RangeFit::new(&colours, self, params.weights);
                    fit.compress(colour_block);
                } else {
                    let iterate = params.algorithm == Algorithm::IterativeClusterFit;
                    let mut fit = ClusterFit::new(&colours, self, params.weights, iterate);
                    fit.compress(colour_block);
                }
            },
            Format::Bc4 | Format::Bc5 => {},
        }
    }

    /// Decompresses a 4x4 block of pixels
    ///
    /// * `block`  - The compressed block of pixels
    /// * `output` - Storage for the decompressed block of pixels
    pub fn decompress_block(self, block: &[u8]) -> [[u8; 4]; 16] {
        let mut rgba;
        // decompress colour block
        match self {
            Format::Bc1 | Format::Bc1Gcn | Format::Bc2 | Format::Bc3 => {
                // get reference to the actual colour block
                let colour_offset = if self == Format::Bc1 || self == Format::Bc1Gcn { 0 } else { 8 };
                let colour_block = &block[colour_offset..colour_offset + 8];

                // decompress colour block
                rgba = colourblock::decompress(colour_block, self);
            },
            _ => {
                rgba = [[0, 0, 0, 0xFF]; 16];
            },
        }

        // decompress alpha block(s)
        match self {
            Format::Bc1 | Format::Bc1Gcn => (),
            Format::Bc2 => alpha::decompress_bc2(&mut rgba, &block[..8]),
            Format::Bc3 => alpha::decompress_bc3(&mut rgba, 3, &block[..8]),
            Format::Bc4 => {
                alpha::decompress_bc3(&mut rgba, 0, &block[..8]);
                // splat decompressed value into g and b channels
                for ref mut pixel in rgba {
                    pixel[1] = pixel[0];
                    pixel[2] = pixel[0];
                }
            },
            Format::Bc5 => {
                alpha::decompress_bc3(&mut rgba, 0, &block[..8]);
                alpha::decompress_bc3(&mut rgba, 1, &block[8..16]);
            },
        }

        rgba
    }

    /// Compresses an image in memory
    ///
    /// * `rgba`   - The uncompressed pixel data
    /// * `width`  - The width of the source image
    /// * `height` - The height of the source image
    /// * `params` - Additional compressor parameters
    /// * `output` - Output buffer for the compressed image. Ensure that this has
    /// at least as much space available as `compute_compressed_size` suggests.
    pub fn compress(
        self,
        rgba: &[u8],
        width: usize,
        height: usize,
        params: Params,
        output: &mut [u8],
    ) {
        assert!(output.len() >= self.compressed_size(width, height));

        let block_size = self.block_size();
        let blocks_wide = num_blocks(width);

        #[cfg(feature="rayon")]
        let output_rows = output.par_chunks_mut(blocks_wide * block_size);
        #[cfg(not(feature="rayon"))]
        let output_rows = output.chunks_mut(blocks_wide * block_size);

        output_rows.enumerate().for_each(|(y, output_row)| {
            let mut source_rgba = [[0u8; 4]; 16];
            let output_blocks = output_row.chunks_mut(block_size);

            output_blocks.enumerate().for_each(|(x, output_block)| {
                // build the 4x4 block of pixels
                let mut mask = 0u32;
                for py in 0..4 {
                    for px in 0..4 {
                        let index = 4 * py + px;

                        // get position in source image
                        let sx = 4 * x + px;
                        let sy = 4 * y + py;

                        // enable pixel if within bounds
                        if sx < width && sy < height {
                            // copy pixel value
                            let src_index = 4 * (width * sy + sx);
                            source_rgba[index].copy_from_slice(&rgba[src_index..src_index + 4]);

                            // enable pixel
                            mask |= 1 << index;
                        }
                    }
                }

                self.compress_block_masked(source_rgba, mask, params, output_block);
            });
        });
    }
}

//--------------------------------------------------------------------------------
// Unit tests
//--------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_storage_requirements() {
        assert_eq!(Format::Bc1.compressed_size(16, 32), 256);
        assert_eq!(Format::Bc1.compressed_size(15, 32), 256);
        assert_eq!(Format::Bc1Gcn.compressed_size(16, 32), 256);
        assert_eq!(Format::Bc1Gcn.compressed_size(15, 32), 256);
        assert_eq!(Format::Bc2.compressed_size(16, 32), 512);
        assert_eq!(Format::Bc2.compressed_size(15, 32), 512);
        assert_eq!(Format::Bc3.compressed_size(16, 32), 512);
        assert_eq!(Format::Bc3.compressed_size(15, 32), 512);
        assert_eq!(Format::Bc4.compressed_size(16, 32), 256);
        assert_eq!(Format::Bc4.compressed_size(15, 32), 256);
        assert_eq!(Format::Bc5.compressed_size(16, 32), 512);
        assert_eq!(Format::Bc5.compressed_size(15, 32), 512);
    }

    // The test-pattern is a gray-scale checkerboard of size 4x4 with 0xFF in the top-left.
    // On top of that, the four middle pixels are set to 0x7F.
    static DECODED_BLOCK_GRAY_4X4: &[u8] = &[
        0xFF, 0x00, 0xFF, 0x00, // row 0
        0x00, 0x7F, 0x7F, 0xFF, // row 1
        0xFF, 0x7F, 0x7F, 0x00, // row 2
        0x00, 0xFF, 0x00, 0xFF, // row 3
    ];

    fn decoded_block_gray_4x4_as_rgba() -> [u8; 4 * 4 * 4] {
        let mut output = [0u8; 4 * 4 * 4];
        for i in 0..DECODED_BLOCK_GRAY_4X4.len() {
            output[i * 4 + 0] = DECODED_BLOCK_GRAY_4X4[i]; // R
            output[i * 4 + 1] = DECODED_BLOCK_GRAY_4X4[i]; // G
            output[i * 4 + 2] = DECODED_BLOCK_GRAY_4X4[i]; // B
            output[i * 4 + 3] = 0xFF; //A
        }
        output
    }

    #[test]
    fn test_bc1_decompression_gray() {
        // BC1 data created with AMD Compressonator v4.1.5083
        let encoded: [u8; 8] = [0x00, 0x00, 0xFF, 0xFF, 0x11, 0x68, 0x29, 0x44];
        let mut output_actual = [0u8; 4 * 4 * 4];
        Format::Bc1.decompress(&encoded, 4, 4, &mut output_actual);
        assert_eq!(output_actual, decoded_block_gray_4x4_as_rgba());
    }

    #[test]
    fn test_bc1_compression_gray() {
        fn test(algorithm: Algorithm) {
            let mut output_actual = [0u8; 8];
            Format::Bc1.compress(
                &decoded_block_gray_4x4_as_rgba(),
                4,
                4,
                Params {
                    algorithm,
                    weights: COLOUR_WEIGHTS_UNIFORM,
                    weigh_colour_by_alpha: false,
                },
                &mut output_actual,
            );
            // BC1 data created with AMD Compressonator v4.1.5083
            let output_expected = [0x00, 0x00, 0xFF, 0xFF, 0x11, 0x68, 0x29, 0x44];
            assert_eq!(output_actual, output_expected);
        }

        // all algorithms should result in the same expected output
        test(Algorithm::ClusterFit);
        test(Algorithm::RangeFit);
        test(Algorithm::IterativeClusterFit);
    }

    // A colour test-pattern (RGB) with the first row in one colour,
    // the second in another and the third and last row in a third colour.
    static DECODED_BLOCK_COLOUR_4X4: [u8; 4 * 4 * 3] = [
        255, 150, 74, 255, 150, 74, 255, 150, 74, 255, 150, 74, // row 0
        255, 120, 52, 255, 120, 52, 255, 120, 52, 255, 120, 52, // row 1
        255, 105, 41, 255, 105, 41, 255, 105, 41, 255, 105, 41, // row 2
        255, 105, 41, 255, 105, 41, 255, 105, 41, 255, 105, 41, // row 3
    ];
    static DECODED_BLOCK_COLOUR_4X4_GCN: [u8; 4 * 4 * 3] = [
        255, 150, 74, 255, 150, 74, 255, 150, 74, 255, 150, 74, // row 0
        255, 121, 53, 255, 121, 53, 255, 121, 53, 255, 121, 53, // row 1
        255, 105, 41, 255, 105, 41, 255, 105, 41, 255, 105, 41, // row 2
        255, 105, 41, 255, 105, 41, 255, 105, 41, 255, 105, 41, // row 3
    ];

    // BC1 data created with AMD Compressonator v4.1.5083 and is the same as libsquish
    static ENCODED_BLOCK_COLOUR_4X4: [u8; 8] = [0xA9, 0xFC, 0x45, 0xFB, 0x00, 0xFF, 0x55, 0x55];
    static ENCODED_BLOCK_COLOUR_4X4_GCN: [u8; 8] = [0xFC, 0xA9, 0xFB, 0x45, 0x00, 0xFF, 0x55, 0x55];

    fn rgb_to_rgba(block: &[u8; 4 * 4 * 3]) -> [u8; 4 * 4 * 4] {
        let mut output = [0u8; 4 * 4 * 4];
        for i in 0..4 * 4 {
            output[i * 4 + 0] = block[i * 3 + 0]; // R
            output[i * 4 + 1] = block[i * 3 + 1]; // G
            output[i * 4 + 2] = block[i * 3 + 2]; // B
            output[i * 4 + 3] = 0xFF; // A
        }
        output
    }

    #[test]
    fn test_bc1_decompression_colour() {
        let encoded: [u8; 8] = ENCODED_BLOCK_COLOUR_4X4;
        let mut output_actual = [0u8; 4 * 4 * 4];
        Format::Bc1.decompress(&encoded, 4, 4, &mut output_actual);
        assert_eq!(output_actual, rgb_to_rgba(&DECODED_BLOCK_COLOUR_4X4));
    }

    #[test]
    fn test_bc1_compression_colour() {
        fn test(algorithm: Algorithm) {
            let mut output_actual = [0u8; 8];
            Format::Bc1.compress(
                &rgb_to_rgba(&DECODED_BLOCK_COLOUR_4X4),
                4,
                4,
                Params {
                    algorithm,
                    weights: COLOUR_WEIGHTS_UNIFORM,
                    weigh_colour_by_alpha: false,
                },
                &mut output_actual,
            );
            let output_expected = ENCODED_BLOCK_COLOUR_4X4;
            assert_eq!(output_actual, output_expected);
        }

        // all algorithms should result in the same expected output
        test(Algorithm::ClusterFit);
        test(Algorithm::RangeFit);
        test(Algorithm::IterativeClusterFit);
    }

    #[test]
    fn test_bc1gcn_decompression_colour() {
        let encoded: [u8; 8] = ENCODED_BLOCK_COLOUR_4X4_GCN;
        let mut output_actual = [0u8; 4 * 4 * 4];
        Format::Bc1Gcn.decompress(&encoded, 4, 4, &mut output_actual);
        assert_eq!(output_actual, rgb_to_rgba(&DECODED_BLOCK_COLOUR_4X4_GCN));
    }

    #[test]
    fn test_bc1gcn_compression_colour() {
        fn test(algorithm: Algorithm) {
            let mut output_actual = [0u8; 8];
            Format::Bc1Gcn.compress(
                &rgb_to_rgba(&DECODED_BLOCK_COLOUR_4X4_GCN),
                4,
                4,
                Params {
                    algorithm,
                    weights: COLOUR_WEIGHTS_UNIFORM,
                    weigh_colour_by_alpha: false,
                },
                &mut output_actual,
            );
            let output_expected = ENCODED_BLOCK_COLOUR_4X4_GCN;
            assert_eq!(output_actual, output_expected);
        }

        // only RangeFit implemented for GCN
        test(Algorithm::RangeFit);
    }
}
