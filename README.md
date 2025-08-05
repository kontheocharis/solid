# Solid

A compiler for a dependently typed programming language.

The language features staged compilation with dependent types that track memory
layouts and other computational information. As a result, data is unboxed by default.

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
