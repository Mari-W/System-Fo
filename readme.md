# Formal Proof of Type Preservation of the Dictionary Passing Transform for System F

[Thesis](https://mari-w.github.io/System-Fo/thesis/thesis.pdf) | [Presentation](https://mari-w.github.io/System-Fo/presentation/presentation.pdf)

# 

## Overview

### Abstract

Most popular strongly typed programming languages support function overloading. 
In combination with polymorphism this leads to essential language constructs, for example typeclasses in Haskell or traits in Rust.  
We introduce System Fo, a minimal language extension to System F, with support for overloading and polymorphism.
Furthermore, we prove the Dictionary Passing Transform from System Fo to System F to be type preserving using Agda.

## Structure

```
├── presentation                          # latex code for presentation
├── proofs                                # contains formalized proofs
│   ├── SystemF.agda                      # specification for System F
│   ├── SystemFo.agda                     # specification for System Fo
│   └── DictionaryPassingTransform.agda   # transform + type preservation proof
└── thesis                                # latex code for thesis 
```