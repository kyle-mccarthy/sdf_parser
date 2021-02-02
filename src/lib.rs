use std::str::FromStr;

pub mod parser;
pub use parser::{parse_record, parse_records, Atom, Bond, Header, Property, Record};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("{0}")]
    Utf8(#[from] std::str::Utf8Error),
    #[error("{0}")]
    ParseInt(#[from] std::num::ParseIntError),
    #[error("{0}")]
    ParseFloat(#[from] std::num::ParseFloatError),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error("nom encountered error while parsing {0:?}")]
    NomError(String),
    #[error("Failed to parse the value {0:?}")]
    Lexer(lexical::ErrorCode),
    #[error("Early EOF encountered {0}")]
    UnexpectedEof(&'static str),
    #[error(transparent)]
    EncodeMessagePack(#[from] rmp_serde::encode::Error),
}

pub type Result<T, E = Error> = std::result::Result<T, E>;

impl Into<nom::Err<Error>> for Error {
    fn into(self) -> nom::Err<Self> {
        nom::Err::Failure(self)
    }
}

pub mod io {
    use std::{
        fs::File,
        io::{BufRead, BufReader, BufWriter, Read},
    };

    use bstr::{io::BufReadExt, ByteSlice};
    use flate2::{write::GzEncoder, Compression};
    use memmap::{Mmap, MmapOptions};
    use rayon::prelude::*;
    use rmp_serde as rmp;

    use crate::{Error, Result};

    pub fn open_file_mmap(path: &str) -> Result<Mmap> {
        let file = std::fs::File::open(&path)?;

        let data = unsafe { MmapOptions::new().map(&file)? };

        Ok(data)
    }

    pub fn open_archive(path: &str) -> Result<Vec<u8>> {
        // let mmap = open_file_mmap(path)?;
        let file = File::open(path)?;
        let mut gz = flate2::read::GzDecoder::new(&file);
        // let mut buffer = Vec::with_capacity(mmap.len() * 4);
        let mut buffer = vec![];

        gz.read_to_end(&mut buffer).unwrap();
        Ok(buffer)
    }

    pub fn read_file(path: &str) -> Result<()> {
        let file = std::fs::File::open(&path)?;

        let data = unsafe { MmapOptions::new().map(&file)? };
        let bytes: &[u8] = &data;

        // Need to advance the indexes by 5 since it's returning the start of the
        // delimiter and we want to include it in the record
        let mut indexes: Vec<usize> = bytes.find_iter("$$$$\n").map(|pos| pos + 5).collect();

        // Insert 0 to the front since it's the first record.
        indexes.insert(0, 0);

        let results = indexes
            .par_windows(2)
            .map(|bounds| {
                let (start, end) = (bounds[0], bounds[1]);
                let len = end - start;
                let record_bytes = &bytes[start..end];
                crate::parse_record(record_bytes)
                    .map_err(|e| crate::Error::NomError(format!("{:?}", e)))
            })
            .collect::<Result<Vec<crate::Record>>>()?;

        println!("parsed {} records", results.len());

        Ok(())
    }
}
