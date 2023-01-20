# Title

[Thesis](https://mari-w.github.io/bsc-thesis/thesis.pdf) [Slides](https://mari-w.github.io/bsc-thesis/slides.pdf)
# Sources

- https://dl.acm.org/doi/pdf/10.1145/227699.227700
- https://link.springer.com/chapter/10.1007/3-540-19027-9_9
- https://www.ioc.ee/~cneste/files/system-f-fun-and-profit.pdf
- https://dl.acm.org/doi/pdf/10.1145/582153.582176
- https://www.microsoft.com/en-us/research/wp-content/uploads/1997/01/henk.pdf

# Translation

```
decl eq in                                          S = [],                     Γ(S) = []
inst Nat -> Nat -> Bool  = λx. λy.                  S = [ o ]                   Γ(S) = [ [] ]
  .. in                                             S = [ e, e, o ]             Γ(S) = [ Nat, Nat, [] ]
let _ = unit in                                     S = [ i, o ]                Γ(S) = [ Nat->Nat->Bool, [Nat->Nat->Bool] ] 
inst ∀α. (eq : α -> α -> bool). [α] -> [α] -> Bool  S = [ e, i, o ]             Γ(S) = [ Unit, Nat->Nat->Bool, [Nat->Nat->Bool] ]
  = λ_eq. λxs. λys. .. eq α α .. in                 S = [ e, e, i, e, i, o ]    Γ(S) = [ [Nat], [Nat], α->α->Bool, Unit, Nat->Nat->Bool, [Nat->Nat->Bool] ]
let is_eq = eq [0] [0]                              S = [ i, e, i, o ]          Γ(S) = [ ∀α. eq : α->α->Bool => [α]->[α]->Bool, Unit, Nat->Nat->Bool, [∀α. eq : α->α->Bool => [α]->[α]->Bool, Nat->Nat->Bool] ]
```

```
let eq = () in                                      S = [],                     Γ(S) = []
let eq1 = λx. λy.                                   S = [ e ]                   Γ(S) = [ Unit ]
  .. in                                             S = [ e, e, e ]             Γ(S) = [ Nat, Nat, Unit ]
let _ = () in                                       S = [ e, e ]                Γ(S) = [ Nat->Nat->Bool, Unit ]
let eq2 = λ_eq. λxs λys.                            S = [ e, e, e ]             Γ(S) = [ Unit, Nat->Nat->Bool, Unit ]
  .. _eq [0] [0] .. in                              S = [ e, e, e, e, e, e ]    Γ(S) = [ [α], [α], α->α->Bool, Unit, Nat->Nat->Bool, Unit ]
let is_eq = eq2 eq1 [0] [0]                         S = [ e, e, e, e ]          Γ(S) = [ ∀α. (α->α->Bool)->[α]->[α], Unit, Nat->Nat->Bool, Unit ]
```

Γ(o)+α->τ,  ⊢ e : σ
-----------------------------
Γ ⊢ e : ∀α. (o : α -> τ) => σ


λ_c.λ_c'.λ_c''.λa.λb. ... : ∀α. (o : α -> τ) => ∀β. (o' : β -> τ') => ∀γ. (o'' : γ -> τ'') => α -> β -> γ
------->

-------> 
λ_c.λ_c'.λ_c''.λa.λb. ... : ∀α. ∀β. ∀γ. (α -> τ) -> (β -> t') -> (γ -> τ''') -> α -> β -> γ

λxs.λys. .. eq x y .. : [α] -> [β] -> Bool
------------------------------------------------------------------------------
Γ ⊢ λeq2.λxs.λys. .. eq x y .. : ∀β. (eq : β -> β -> Bool) => [α] -> [β] -> Bool
-----------------------------------------------------------------------------------------------------------------
Γ ⊢ λeq.λeq2.λxs.λys. .. eq x y .. : ∀α. (eq : α -> α -> Bool) => ∀β. (eq : β -> β -> Bool) => [α] -> [β] -> Bool

=================================================================================================================

λxs.λys. .. eq x y .. : [α] -> [β] -> Bool > Γ : λxs.λys. .. eq x y .. : [α] -> [β] -> Bool
------------------------------------------------------------------------------
Γ ⊢ λeq2.λxs.λys. .. eq x y .. : ∀β. (eq : β -> β -> Bool) => [α] -> [β] -> Bool > Γ ⊢ λeq2.λxs.λys. .. eq x y .. : ∀β. (β -> β -> Bool) -> [α] -> [β]
-----------------------------------------------------------------------------------------------------------------
Γ ⊢ λeq.λeq2.λxs.λys. .. eq x y .. : ∀α. (eq : α -> α -> Bool) => ∀β. (eq : β -> β -> Bool) => [α] -> [β] -> Bool