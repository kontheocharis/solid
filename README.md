# Unboxed IDR

A compiler for a dependently typed programming language featuring unboxed types and staged computation.

The language features staged compilation with dependent types that track memory
layouts and other computational information.

## Building

Uses Idris2 with [pack](https://github.com/stefan-hoeck/idris2-pack/tree/main/src/Pack).

```bash
pack build
pack install
```

## Testing

Run the test suite:

```bash
# Build and run tests
pack test
```

Test cases are organized in `test/cases/` with passing and failing examples.
