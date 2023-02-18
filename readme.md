# Formal Proof of Type Preservation of the Dictionary Passing Transform for System F

[Thesis](https://mari-w.github.io/bsc-thesis/thesis/thesis.pdf) | [Presentation](https://mari-w.github.io/bsc-thesis/presentation/presentation.pdf)

# 

## Overview

### Abstract

Most popular strongly typed programming languages support function overloading. In combination with polymorphism this leads to essential language constructs, for example type classes in Haskell or traits in Rust. We introduce System Fo, a minimal language extension to System F, with support for overloading. We show that the Dictionary Passing Transform from System Fo to System F is type preserving.

### Examples

tbd.

## Structure

```
├── presentation                          # latex code for presentation
├── proofs                                # contains formalized proofs
│   ├── SystemF.agda                      # specification for System F
│   ├── SystemFo.agda                     # specification for System Fo
│   └── DictionaryPassingTransform.agda   # transform + type preservation proof
└── thesis                                # latex code for thesis 
```