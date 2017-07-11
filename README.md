redex-models
===

Some Redex models, FOR FREE


### Install

```
    $ git clone https://github.com/bennn/redex-models
    $ raco pkg install --skip-installed mf-apply rackunit-abbrevs
```


### Testing

To test any model `<FILE.RKT>`, run:

```
    raco test <FILE.RKT>
```

This will:
- run the unit tests
- contained the the `test` submodule (marked with `module+ test`)
- in the file `<FILE.RKT>`


### Conventions

- metafunction names usually suffixed with a `#`
