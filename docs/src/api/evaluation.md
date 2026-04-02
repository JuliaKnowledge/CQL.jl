# Parsing & Evaluation

## String Macro

```@docs
@cql_str
```

## Program Evaluation

```@docs
run_program
parse_program
```

## Options

```@docs
default_options
```

## Current Limitations

- `pivot` on instances is not implemented; only pivot-derived schemas and
  mappings are currently available.
- `pi` and `pi_transform` are implemented only for identity mappings.
- `rext` does not yet support attribute-bearing targets when the left query is
  non-identity.
