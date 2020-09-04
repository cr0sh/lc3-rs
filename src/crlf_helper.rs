#![cfg(all(target_os = "windows", not(feature = "disable-crlf-compat-windows")))]

use std::io::{Read, Result as IOResult};

/// A helper struct to handle windows CRLF newline incompatibility.
pub(crate) struct CrlfToLf<T>(pub(crate) T);

impl<T> Read for CrlfToLf<T>
where
    T: Read,
{
    fn read(&mut self, buf: &mut [u8]) -> IOResult<usize> {
        let size = self.0.read(buf);
        let newbuf = std::str::from_utf8(buf).unwrap().replace("\x0D", "");
        buf[0..newbuf.len()].copy_from_slice(newbuf.as_bytes());
        size.and(Ok(newbuf.len()))
    }
}
