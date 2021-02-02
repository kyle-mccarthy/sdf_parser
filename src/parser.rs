use std::{collections::HashMap, str::FromStr};

use bstr::ByteSlice;
use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::{Error, Result};

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Header<'a> {
    pub title_line: &'a str,
    pub program_line: &'a str,
    pub comment_line: &'a str,
}
//   9  8  0     0  0  0  0  0  0999 V2000
// ___---___---___---___---___---___------
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Counts<'a> {
    pub num_atoms: u16,
    pub num_bonds: u16,
    // pub obsolete: &'a [u8; 27],
    pub version: &'a str,
}

/// # Atoms Line
#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Atom<'a> {
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub element: &'a str,
    /// Mass difference from the monoisotope. Falls between -3 and +4.
    pub mass_diff: f64,
    /// Charge code interpreted as follows:
    /// | Code | Meaning        |
    /// | ---- | -------------- |
    /// | 7    | -3             |
    /// | 6    | -2             |
    /// | 5    | -1             |
    /// | 0    | Neutral        |
    /// | 3    | +1             |
    /// | 2    | +2             |
    /// | 1    | +3             |
    /// | 4    | double radical |
    pub charge_code: u8,
    // pub obsolete: &'a [u8],
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Bond {
    pub from: u16,
    pub to: u16,
    /// Bond type interpreted as follows:
    /// | Code | Meaning            |
    /// | ---- | ------------------ |
    /// | 1    | single             |
    /// | 2    | double             |
    /// | 3    | triple             |
    /// | 4    | aromatic           |
    /// | 5    | single or double   |
    /// | 6    | single or aromatic |
    /// | 7    | double or aromatic |
    /// | 8    | any                |
    pub bond_type: u8,
    /// Bond stereo interpreted as follows:
    /// | Code | Meaning |
    /// | ---- | ------- |
    /// | 1    | Up      |
    /// | 4    | Either  |
    /// | 6    | Down    |
    pub bond_stereo: u8,
    // pub obsolete: &'a [u8],
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Property<'a> {
    pub property: &'a str,
    pub num_values: u16,
    pub values: Vec<(u16, i16)>,
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Record<'a> {
    #[serde(borrow)]
    pub header: Header<'a>,
    #[serde(borrow)]
    pub counts: Counts<'a>,
    #[serde(borrow)]
    pub atoms: Vec<Atom<'a>>,
    pub bonds: Vec<Bond>,
    #[serde(borrow)]
    pub properties: Vec<Property<'a>>,
    #[serde(borrow)]
    pub data: HashMap<&'a str, Vec<&'a str>>,
}

pub trait FromStrRadix: Sized {
    fn from_str_radix(s: &str, radix: u32) -> Result<Self>;
}

impl FromStrRadix for u8 {
    fn from_str_radix(s: &str, radix: u32) -> Result<Self> {
        Self::from_str_radix(s, radix).map_err(|e| Error::ParseInt(e))
    }
}

impl FromStrRadix for u16 {
    fn from_str_radix(s: &str, radix: u32) -> Result<Self> {
        Self::from_str_radix(s, radix).map_err(|e| Error::ParseInt(e))
    }
}

impl FromStrRadix for i16 {
    fn from_str_radix(s: &str, radix: u32) -> Result<Self> {
        Self::from_str_radix(s, radix).map_err(|e| Error::ParseInt(e))
    }
}

impl FromStrRadix for u32 {
    fn from_str_radix(s: &str, radix: u32) -> Result<Self> {
        Self::from_str_radix(s, radix).map_err(|e| Error::ParseInt(e))
    }
}

/// This operation calls from_utf8_unchecked which is an unsafe operation.
/// However, due to the size of the files and total amount of data that needs to
/// be parsed we need it to be as quick as possible.
fn from_utf8(bytes: &[u8]) -> &str {
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

/// Transforms the byte string to a base 10 integer
pub fn bytes_to_int<T: FromStrRadix>(bytes: &[u8]) -> Result<T> {
    let out = T::from_str_radix(from_utf8(&bytes), 10)?;
    Ok(out)
}

/// Transforms the byte string to a float
pub fn bytes_to_float(bytes: &[u8]) -> Result<f32> {
    let out = f32::from_str(from_utf8(&bytes))?;
    Ok(out)
}

/// Parse an unsigned integer <T> from a byte string padded with zero or more
/// spaces
pub fn parse_padded_int<T: FromStrRadix>(bytes: &[u8]) -> Result<T> {
    bytes_to_int::<T>(bytes.trim())
}

/// Parse a float from a byte string padded with zero or more spaces
pub fn parse_padded_float(bytes: &[u8]) -> Result<f64> {
    lexical::parse(bytes.trim()).map_err(|e| Error::Lexer(e.code))
}

pub fn parse_counts_line(bytes: &[u8]) -> Result<Counts> {
    let num_atoms = parse_padded_int(&bytes[0..3])?;
    let num_bonds = parse_padded_int(&bytes[3..6])?;
    let version = from_utf8(&bytes[bytes.len() - 6..].trim());

    Ok(Counts {
        num_atoms,
        num_bonds,
        version,
    })
}

pub fn parse_header<'a>(iter: &mut impl Iterator<Item = &'a [u8]>) -> Result<Header<'a>> {
    let title_line = from_utf8(
        iter.next()
            .ok_or_else(|| Error::UnexpectedEof("title line"))?,
    );

    let program_line = from_utf8(
        iter.next()
            .ok_or_else(|| Error::UnexpectedEof("program line"))?,
    );

    let comment_line = from_utf8(
        iter.next()
            .ok_or_else(|| Error::UnexpectedEof("comment line"))?,
    );

    Ok(Header {
        title_line,
        program_line,
        comment_line,
    })
}

pub fn parse_atom_line(bytes: &[u8]) -> Result<Atom> {
    // [0-10][10-20][20-30][30][31-34][34-36][36-39]
    let x = parse_padded_float(&bytes[0..10])?;
    let y = parse_padded_float(&bytes[10..20])?;
    let z = parse_padded_float(&bytes[20..30])?;
    let element = from_utf8(&bytes[31..34].trim());
    let mass_diff = parse_padded_float(&bytes[34..36])?;
    let charge_code = parse_padded_int::<u8>(&bytes[36..39])?;

    Ok(Atom {
        x,
        y,
        z,
        element,
        mass_diff,
        charge_code,
    })
}

pub fn parse_bond_line(bytes: &[u8]) -> Result<Bond> {
    let from = parse_padded_int::<u16>(&bytes[0..3]).unwrap();
    let to = parse_padded_int::<u16>(&bytes[3..6]).unwrap();
    let bond_type = parse_padded_int::<u8>(&bytes[6..9]).unwrap();
    let bond_stereo = parse_padded_int::<u8>(&bytes[9..12]).unwrap();

    Ok(Bond {
        from,
        to,
        bond_type,
        bond_stereo,
        // obsolete,
    })
}

pub fn parse_property_line(bytes: &[u8]) -> Result<Property> {
    // "M**ISO**1***1***2" -> (M  ISO, 1, [(1, 2)])
    let property = from_utf8(&bytes[0..6]);
    let num_values = parse_padded_int::<u16>(&bytes[6..9])?;
    let values = (&bytes[9..])
        .chunks(4)
        .tuples::<(&[u8], &[u8])>()
        .map(|(k, v)| Ok((parse_padded_int::<u16>(k)?, parse_padded_int::<i16>(v)?)))
        .collect::<Result<Vec<(u16, i16)>>>()?;
    Ok(Property {
        property,
        num_values,
        values,
    })
}

pub fn parse_property_block<'a>(
    iter: &mut impl Iterator<Item = &'a [u8]>,
) -> Result<Vec<Property<'a>>> {
    iter.take_while(|b| b != b"M  END")
        .map(parse_property_line)
        .collect()
}

pub fn parse_data_item_name(bytes: &[u8]) -> &str {
    from_utf8(&bytes[3..bytes.len() - 1])
}

pub fn parse_data_item(bytes: &[u8]) -> (&str, Vec<&str>) {
    let mut lines = bytes.lines();
    let name = lines.next();

    let name = name.unwrap();
    let name = from_utf8(&name[3..name.len() - 1]);

    let data_vec: Vec<&str> = lines.take_while(|v| v.len() != 0).map(from_utf8).collect();
    (&name, data_vec)
}

pub fn parse_data_items_block<'a>(
    iter: &mut impl Iterator<Item = &'a [u8]>,
) -> HashMap<&'a str, Vec<&'a str>> {
    // use nom::Finish;
    // use rayon::prelude::*;

    let mut records = HashMap::new();

    loop {
        let name = iter.next();

        if name.is_none() {
            break;
        }

        let name = name.unwrap().trim();

        if name.len() < 4 || name == b"$$$$" {
            break;
        }
        let parsed_name = from_utf8(&name[3..name.len() - 1]);

        let values: Vec<&str> = iter.take_while(|v| v.len() != 0).map(from_utf8).collect();

        records.insert(parsed_name, values);
    }

    records
}

pub fn parse_record(bytes: &[u8]) -> Result<Record> {
    let mut iter = bytes.lines().peekable();

    let header = parse_header(&mut iter)?;
    let counts = parse_counts_line(
        iter.next()
            .ok_or_else(|| Error::UnexpectedEof("counts line"))?,
    )?;

    let atoms: Vec<Atom> = iter
        .by_ref()
        .take(counts.num_atoms as usize)
        .map(parse_atom_line)
        .collect::<Result<Vec<Atom>>>()?;

    let bonds: Vec<Bond> = iter
        .by_ref()
        .take(counts.num_bonds as usize)
        .map(parse_bond_line)
        .collect::<Result<Vec<Bond>>>()?;

    let properties = parse_property_block(&mut iter)?;

    // TODO: fix this unwrap
    let data = parse_data_items_block(&mut iter);

    let record = Record {
        header,
        counts,
        atoms,
        bonds,
        properties,
        data,
    };

    Ok(record)
}

/// Parse the records in parallel.
///
/// # How
/// This differs from the normal [`parse_records`] by using a "pre-parse" step
/// that produces an iterator of the start and end positions for each record.
/// This allows for us to leverage Rayon (specifically, [`rayon::par_windows`])
/// to produce the list of [`Record`] in parallel.
pub fn parse_records(bytes: &[u8]) -> Result<Vec<Record>> {
    use rayon::prelude::*;

    // Need to advance the indexes by 5 since it's returning the start of the
    // delimiter and we want to include it in the record
    let mut indexes: Vec<usize> = bytes.find_iter("$$$$\n").map(|pos| pos + 5).collect();

    // Insert 0 to the front since it's the first record.
    indexes.insert(0, 0);

    indexes
        .par_windows(2)
        .map(|bounds| {
            let (start, end) = (bounds[0], bounds[1]);
            let record_bytes = &bytes[start..end];
            crate::parse_record(record_bytes)
                .map_err(|e| crate::Error::NomError(format!("{:?}", e)))
        })
        .collect::<Result<Vec<crate::Record>>>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_parses_samples_without_panicing() {
        let bytes = include_bytes!("../assets/sample.sdf");

        let records = parse_records(bytes).unwrap();
        assert_eq!(records.len(), 3);
    }

    #[test]
    fn it_parses_single() {
        let bytes = include_bytes!("../assets/single.sdf");

        let record = parse_record(bytes).unwrap();
        assert_eq!(record.atoms.len(), 31);
        assert_eq!(record.bonds.len(), 30);
        assert_eq!(record.properties.len(), 1);
        assert_eq!(record.data.len(), 34);
    }

    #[test]
    fn it_parses_property_line() {
        let output = parse_property_line(b"M  CHG  2   2  -1   5   1").unwrap();
        assert_eq!(
            output,
            Property {
                property: "M  CHG",
                num_values: 2,
                values: vec![(2, -1), (5, 1)]
            }
        );

        let output = parse_property_line(
            b"M  ISO  8  17   2  18   2  19   2  20   2  21   2  22   2  23   2  24   2",
        )
        .unwrap();

        assert_eq!(
            output,
            Property {
                property: "M  ISO",
                num_values: 8,
                values: vec![
                    (17, 2),
                    (18, 2),
                    (19, 2),
                    (20, 2),
                    (21, 2),
                    (22, 2),
                    (23, 2),
                    (24, 2)
                ],
            }
        );

        let output = parse_property_line(b"M  RAD  3  24   2  25   2  26  2").unwrap();

        assert_eq!(
            output,
            Property {
                property: "M  RAD",
                num_values: 3,
                values: vec![(24, 2), (25, 2), (26, 2),],
            }
        );
    }

    #[test]
    fn it_parses_property_block() {
        let bytes = b"M  CHG  1   4   1\n\
        M  CHG  1   4   1\n\
        M  CHG  1   4   1\n\
        M  END\n";
        let mut lines = bytes.lines();

        let output = parse_property_block(&mut lines).unwrap();
        assert_eq!(output.len(), 3);
    }

    #[test]
    fn it_parses_empty_property_block() {
        let bytes = b"M  END\n";
        let mut iter = bytes.lines();

        let output = parse_property_block(&mut iter).unwrap();
        assert_eq!(output.len(), 0);
    }

    #[test]
    fn it_parses_data_item_names() {
        let output = parse_data_item_name(b"> <PUBCHEM_COMPOUND_CANONICALIZED>");
        assert_eq!(output, "PUBCHEM_COMPOUND_CANONICALIZED");
    }

    #[test]
    fn it_pases_single_data_item() {
        let bytes = b"> <PUBCHEM_IUPAC_OPENEYE_NAME>\n3-acetoxy-4-(trimethylammonio)butanoate\n\n";

        let (name, values) = parse_data_item(bytes);

        assert_eq!(values.len(), 1);
        assert_eq!(name, "PUBCHEM_IUPAC_OPENEYE_NAME");
        assert_eq!(values[0], "3-acetoxy-4-(trimethylammonio)butanoate");
    }

    #[test]
    fn it_pases_data_items_block() {
        let bytes = b"> <PUBCHEM_COMPOUND_CID>\n1\n\n> <PUBCHEM_IUPAC_OPENEYE_NAME>\n3-acetoxy-4-(trimethylammonio)butanoate\n\n";
        let mut iter = bytes.lines();

        let items = parse_data_items_block(&mut iter);

        assert_eq!(items.len(), 2);

        assert_eq!(items["PUBCHEM_COMPOUND_CID"][0], "1");
        assert_eq!(
            items["PUBCHEM_IUPAC_OPENEYE_NAME"][0],
            "3-acetoxy-4-(trimethylammonio)butanoate"
        );
    }

    #[test]
    fn it_parses_atom_line() {
        let bytes = b"1111.111142222.222243333.33334 O   0  0  0  0  0  0  0  0  0  0  0  0";
        let line = parse_atom_line(bytes as &[u8]).unwrap();

        assert_eq!(line.x, 1111.11114);
        assert_eq!(line.y, 2222.22224);
        assert_ne!(line.x, 3333.33334);
    }
}
