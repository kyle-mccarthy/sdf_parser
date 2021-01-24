use nom::{
    bytes::complete::{is_a, is_not, tag, take, take_until},
    character::complete::{digit1, line_ending, multispace0, space0},
    combinator::{eof, map, map_parser, map_res},
    multi::{many0, many1, separated_list0, separated_list1},
    number::complete::float,
    sequence::{delimited, pair, preceded, terminated, tuple},
    IResult,
};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("{0}")]
    Utf8(#[from] std::str::Utf8Error),
    #[error("{0}")]
    ParseInt(#[from] std::num::ParseIntError),
    #[error("{0}")]
    ParseFloat(#[from] std::num::ParseFloatError),
}

pub type Result<T> = std::result::Result<T, Error>;

impl Into<nom::Err<Error>> for Error {
    fn into(self) -> nom::Err<Self> {
        nom::Err::Failure(self)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Header<'a> {
    pub title_line: &'a str,
    pub initials: &'a str,
    pub program: &'a str,
    pub date: &'a str,
    pub comment_line: &'a str,
}
//   9  8  0     0  0  0  0  0  0999 V2000
// ___---___---___---___---___---___------
#[derive(Debug, PartialEq, Eq)]
pub struct Counts<'a> {
    pub num_atoms: u16,
    pub num_bonds: u16,
    pub obsolete: &'a [u8; 27],
    pub version: &'a str,
}

/// # Atoms Line
#[derive(Debug, PartialEq)]
pub struct Atom<'a> {
    pub x: f32,
    pub y: f32,
    pub z: f32,
    pub element: &'a str,
    /// Mass difference from the monoisotope. Falls between -3 and +4.
    pub mass_diff: f32,
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
    pub obsolete: &'a [u8],
}

#[derive(Debug, PartialEq, Eq)]
pub struct Bond<'a> {
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
    pub obsolete: &'a [u8],
}

#[derive(Debug, PartialEq, Eq)]
pub struct Property<'a> {
    pub property: &'a str,
    pub num_values: u16,
    pub values: Vec<(u16, i16)>,
}

#[derive(Debug, PartialEq)]
pub struct Record<'a> {
    pub header: Header<'a>,
    pub counts: Counts<'a>,
    pub atoms: Vec<Atom<'a>>,
    pub bonds: Vec<Bond<'a>>,
    pub properties: Vec<Property<'a>>,
    pub data: Vec<(&'a str, Vec<&'a str>)>,
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

/// Stream the bytes until the end of record marker is reached. Advance the
/// remaining bytes by the length of the marker.
pub fn take_record(bytes: &[u8]) -> IResult<&[u8], &[u8]> {
    let (i, o) = take_until("$$$$")(bytes)?;
    let (i, _) = take(4usize)(i)?;

    Ok((i, o))
}

pub fn take_line(bytes: &[u8]) -> IResult<&[u8], &[u8]> {
    let (i, o) = take_until("\n")(bytes)?;
    let (i, _) = take(1usize)(i)?;

    Ok((i, o))
}

/// Transforms the byte string to a base 10 integer
pub fn bytes_to_int<T: FromStrRadix>(bytes: &[u8]) -> Result<T> {
    let out = T::from_str_radix(std::str::from_utf8(&bytes)?, 10)?;
    Ok(out)
}

/// Transforms the byte string to a float
pub fn bytes_to_float(bytes: &[u8]) -> Result<f32> {
    use std::str::FromStr;
    let out = f32::from_str(std::str::from_utf8(&bytes)?)?;
    Ok(out)
}

/// Parse an unsigned integer <T> from a byte string padded with zero or more
/// spaces
pub fn parse_padded_int<T: FromStrRadix>(bytes: &[u8]) -> IResult<&[u8], T> {
    map_res(preceded(space0, digit1), bytes_to_int::<T>)(bytes)
}

/// Parse a signed integer <T> from a byte string padded with zero or more
/// spaces
pub fn parse_padded_signed_int<T: FromStrRadix>(bytes: &[u8]) -> IResult<&[u8], T> {
    map_res(preceded(space0, is_a("-0123456789")), bytes_to_int::<T>)(bytes)
}

/// Parse a float from a byte string padded with zero or more spaces
pub fn parse_padded_float(bytes: &[u8]) -> IResult<&[u8], f32> {
    map_parser(preceded(space0, is_a("1234567890.-")), float)(bytes)
}

pub fn parse_counts_line(bytes: &[u8]) -> IResult<&[u8], Counts> {
    let (rest, (num_atoms, num_bonds, obsolete, version, _)) = tuple((
        map_parser(take(3usize), parse_padded_int),
        map_parser(take(3usize), parse_padded_int),
        take(27usize),
        map_res(take(6usize), |s| std::str::from_utf8(s).map(|s| s.trim())),
        eof,
    ))(bytes)?;

    assert_eq!(obsolete.len(), 27);
    // assert_eq!(rest.len(), 0);
    // # Safety
    // 1. We assert that the length of the slice is 27
    let obsolete: &[u8; 27] = unsafe { &*(obsolete.as_ptr() as *const [u8; 27]) };

    Ok((
        rest,
        Counts {
            num_atoms,
            num_bonds,
            obsolete,
            version,
        },
    ))
}

pub fn parse_line_to_str(bytes: &[u8]) -> IResult<&[u8], &str> {
    map_res(take_line, std::str::from_utf8)(bytes)
}

pub fn parse_header(bytes: &[u8]) -> IResult<&[u8], Header> {
    let (rest, (title_line, program_line, comment_line)) =
        tuple((parse_line_to_str, take_line, parse_line_to_str))(bytes)?;

    let (_, (initials, program, date)) = tuple((
        map_res(take(2usize), std::str::from_utf8),
        map_res(take(8usize), std::str::from_utf8),
        map_res(take(10usize), std::str::from_utf8),
    ))(program_line)?;
    // let (_, (num_atoms, num_bonds, obsolete, version)) =
    // parse_counts_line(count_line)?;

    Ok((
        rest,
        Header {
            title_line,
            initials,
            program,
            date,
            comment_line,
        },
    ))
}

pub fn parse_atom_line(bytes: &[u8]) -> IResult<&[u8], Atom> {
    // fn parse_pos(bytes: &[u8]) -> IResult<&[u8], f32> {
    //     map_parser(take(10usize), parse_padded_float)
    // }
    let (rest, (x, y, z, _, element, mass_diff, charge_code, obsolete)) = tuple((
        map_parser(take(10usize), parse_padded_float),
        map_parser(take(10usize), parse_padded_float),
        map_parser(take(10usize), parse_padded_float),
        take(1usize),
        map_res(take(3usize), |s| std::str::from_utf8(s).map(|s| s.trim())),
        map_parser(take(2usize), parse_padded_float),
        map_parser(take(3usize), parse_padded_int::<u8>),
        nom::combinator::rest,
    ))(bytes)?;

    Ok((
        rest,
        Atom {
            x,
            y,
            z,
            element,
            mass_diff,
            charge_code,
            obsolete,
        },
    ))
}

pub fn parse_bond_line(bytes: &[u8]) -> IResult<&[u8], Bond> {
    let (rest, (from, to, bond_type, bond_stereo, obsolete)) = tuple((
        map_parser(take(3usize), parse_padded_int::<u16>),
        map_parser(take(3usize), parse_padded_int::<u16>),
        map_parser(take(3usize), parse_padded_int::<u8>),
        map_parser(take(3usize), parse_padded_int::<u8>),
        nom::combinator::rest,
    ))(bytes)?;

    Ok((
        rest,
        Bond {
            from,
            to,
            bond_type,
            bond_stereo,
            obsolete,
        },
    ))
}

// fn parse_property_pair<T: FromStrRadix>(bytes: &[u8]) -> IResult<&[u8], (u16,
// T)> {     pair(
//         map_parser(take(4usize), parse_padded_int::<u16>),
//         map_parser(take(4usize), parse_padded_int::<T>),
//     )(bytes)
// }

pub fn parse_property_line(bytes: &[u8]) -> IResult<&[u8], Property> {
    // "M**ISO**1***1***2" -> (M  ISO, 1, [(1, 2)])
    let parse_pair = pair(
        map_parser(take(4usize), parse_padded_int::<u16>),
        map_parser(take(4usize), parse_padded_signed_int::<i16>),
    );

    let num_pairs = map_parser(take(3usize), parse_padded_int::<u16>);

    let (rest, (property, num_values, values)) = tuple((
        map_res(take(6usize), std::str::from_utf8),
        num_pairs,
        many1(parse_pair),
    ))(bytes)?;

    Ok((
        rest,
        Property {
            property,
            num_values,
            values,
        },
    ))
}

pub fn parse_property_block(bytes: &[u8]) -> IResult<&[u8], (Vec<Property>, &[u8])> {
    tuple((
        separated_list0(line_ending, parse_property_line),
        preceded(multispace0, tag("M  END\n")),
    ))(bytes)
}

pub fn parse_data_item_name(bytes: &[u8]) -> IResult<&[u8], &str> {
    map_res(delimited(tag("> <"), is_not(">"), tag(">")), |name| {
        std::str::from_utf8(name)
    })(bytes)
}

pub fn parse_data_item(bytes: &[u8]) -> IResult<&[u8], (&str, Vec<&str>)> {
    map(
        tuple((
            parse_data_item_name,
            line_ending,
            map_parser(
                terminated(take_until("\n\n"), tag("\n\n")),
                separated_list1(line_ending, map_res(is_not("\n"), std::str::from_utf8)),
            ),
        )),
        |(name, _, values)| (name, values),
    )(bytes)
}

pub fn parse_data_items_block(bytes: &[u8]) -> IResult<&[u8], Vec<(&str, Vec<&str>)>> {
    many0(parse_data_item)(bytes)
}

pub fn parse_record(bytes: &[u8]) -> IResult<&[u8], Record> {
    let (rest, header) = terminated(take_until("$$$$"), tuple((tag("$$$$"), multispace0)))(bytes)?;

    let (record, header) = parse_header(header)?;
    let (record, line) = take_line(record)?;
    let (_, counts) = parse_counts_line(line)?;

    let mut record = record;
    let mut atoms = vec![];

    for _ in 0..counts.num_atoms {
        let (next_record, line) = take_line(record)?;
        record = next_record;

        let (_, atom) = parse_atom_line(line)?;
        atoms.push(atom);
    }

    let mut bonds = vec![];
    for _ in 0..counts.num_bonds {
        let (next_record, line) = take_line(record)?;
        record = next_record;

        let (_, bond) = parse_bond_line(line)?;
        bonds.push(bond);
    }

    let (record, (properties, _)) = parse_property_block(record)?;

    let (_, (data, _)) = tuple((parse_data_items_block, eof))(record)?;

    let record = Record {
        header,
        counts,
        atoms,
        bonds,
        properties,
        data,
    };
    Ok((rest, record))
}

// pub fn parse_counts(slice: &[u8]) -> IResult<&[u8], (&str, &str, &[u8],
// &str)> {     use nom::bits::{bits, bytes};
//     use nom::bytes::streaming::take;

//     // tuple((take(3usize), take(3usize), take(33usize), rest))(slice)
// }

pub fn parse_records(bytes: &[u8]) -> IResult<&[u8], Vec<Record>> {
    many1(parse_record)(bytes)

    // let test_str: &[u8] = b"123\n456";

    // fn til_new_line(bytes: &[u8]) -> IResult<&[u8], &[u8]> {
    //     take_until("\n")(bytes)
    // }

    // let consumed_til_new_line: IResult<&[u8], &[u8]> =
    //     nom::combinator::flat_map(is_not("\n"), take)(test_str);
    // dbg!(consumed_til_new_line);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_parses_samples_without_panicing() {
        let bytes = include_bytes!("../assets/sample.sdf");
        let (rest, records) = parse_records(bytes).unwrap();
        assert_eq!(records.len(), 3);
        assert_eq!(rest.len(), 0);
    }

    #[test]
    fn it_parses_property_line() {
        let (_, output) = parse_property_line(b"M  CHG  2   2  -1   5   1").unwrap();
        assert_eq!(
            output,
            Property {
                property: "M  CHG",
                num_values: 2,
                values: vec![(2, -1), (5, 1)]
            }
        );

        let (_, output) = parse_property_line(
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

        let (_, output) = parse_property_line(b"M  RAD  3  24   2  25   2  26   2").unwrap();

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

        let output = parse_property_block(bytes);
        assert!(output.is_ok());
        let (_, output) = output.unwrap();
        assert_eq!(output.0.len(), 3);
    }

    #[test]
    fn it_parses_empty_property_block() {
        let bytes = b"M  END\n";

        let output = parse_property_block(bytes);
        assert!(output.is_ok());
        let (_, output) = output.unwrap();
        assert_eq!(output.0.len(), 0);
    }

    #[test]
    fn it_parses_data_item_names() {
        let (_, output) = parse_data_item_name(b"> <PUBCHEM_COMPOUND_CANONICALIZED>").unwrap();
        assert_eq!(output, "PUBCHEM_COMPOUND_CANONICALIZED");
    }

    #[test]
    fn it_pases_single_data_item() {
        let bytes = b"> <PUBCHEM_IUPAC_OPENEYE_NAME>\n3-acetoxy-4-(trimethylammonio)butanoate\n\n";

        let (_, (name, values)) = parse_data_item(bytes).unwrap();

        assert_eq!(values.len(), 1);
        assert_eq!(name, "PUBCHEM_IUPAC_OPENEYE_NAME");
        assert_eq!(values[0], "3-acetoxy-4-(trimethylammonio)butanoate");
    }

    #[test]
    fn it_pases_data_items_block() {
        let bytes = b"> <PUBCHEM_COMPOUND_CID>\n1\n\n> <PUBCHEM_IUPAC_OPENEYE_NAME>\n3-acetoxy-4-(trimethylammonio)butanoate\n\n";

        let (_, items) = parse_data_items_block(bytes).unwrap();

        assert_eq!(items.len(), 2);

        assert_eq!(items[0].0, "PUBCHEM_COMPOUND_CID");
        assert_eq!(items[0].1[0], "1");

        assert_eq!(items[1].0, "PUBCHEM_IUPAC_OPENEYE_NAME");
        assert_eq!(items[1].1[0], "3-acetoxy-4-(trimethylammonio)butanoate");
    }
}
