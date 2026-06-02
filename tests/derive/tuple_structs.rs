use hecs::{Bundle, Query};

#[derive(Bundle)]
struct Foo(i32);

#[derive(Bundle)]
struct Bar(i32, String);

#[derive(Bundle)]
struct Baz(i32, String, Vec<u8>);

#[derive(Query)]
struct Quux<'a>(&'a i32);

fn main() {}
