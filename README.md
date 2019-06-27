# flocq-quickchick

Flocq binary float generators for QuickChick

## Installation
### From OPAM
```
opam install coq-flocq-quickchick
```

### From source
Install dependencies:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq coq-quickchick coq-flocq
```

Then:
```
coq_makefile -f _CoqProject -o Makefile 
make && make install
```

## Simple Example
[Example.v](Example.v)

## Documentation
All generators and sub-generators have comments
with documentation and `Example.v` has usage examples.
