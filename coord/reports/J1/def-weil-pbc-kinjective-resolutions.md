## Worker report

The module defines `CochainComplex.IsKInjectiveHomComplex`, the predicate that for every
acyclic cochain complex `A` of sheaves of `R`-modules on `T`'s small étale site, the
cochain Hom complex `HomComplex A I` is acyclic. It also defines
`CochainComplex.IsKInjectiveHomComplexResolution f` as the conjunction of `QuasiIso f`
and this predicate for the target complex.

The node's hypotheses and clauses are rendered as follows. `T` is
`T : Scheme.{u}` and `R` is `R : Type (u + 1)` with `[CommRing R]`. The category
`Mod(T_et,R)` is represented by `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)`.
The complexes `A`, `I`, and `K` are `CochainComplex` objects in that category. The
Hom complex is Mathlib's `HomComplex A I`; its degreewise product and differential
are supplied by that construction. K-injectivity is the universal implication
`A.Acyclic → (HomComplex A I).Acyclic`. A resolution is
`QuasiIso f ∧ IsKInjectiveHomComplex T R I` for `f : K ⟶ I`.
The final source clause “for etale abelian sheaves, take R = Z” is covered by the
binder allowing the specialization `R = ℤ`.

Dependencies used: `def-weil-pbc-derived-categories` via
`Sheaf.AlgebraicGeometry.DerivedCategories` (which supplies the etale sheaf/module
encoding and the abelian and homology instances); `def-pc-cochain-complex-modules`
via Mathlib `CochainComplex`; `def-pc-acyclic-complex-modules` via
`HomologicalComplex.Acyclic`; and `def-pc-quasi-iso-modules` via Mathlib `QuasiIso`.

Edge cases checked: arbitrary integer degrees (including degree zero and negative
indices), empty/zero complexes (the universal predicate is meaningful and the zero
Hom complex is acyclic), arbitrary universes through `u`, and the specialization
`R = ℤ`.

Searches made: `msearch.py ... leanfinder 'K-injective resolution HomComplex acyclic
sheaf modules'` found Mathlib's null-homotopy `CochainComplex.IsKInjective` and
related injective-resolution declarations, but no full Hom-complex criterion;
`msearch.py ... loogle 'CochainComplex.IsKInjective, HomComplex, QuasiIso'` returned
no hit; `msearch.py ... grep 'IsKInjective|HomComplex' Mathlib/Algebra/Homology/HomotopyCategory`
returned no additional declaration. Repository `rg` found no project declaration of
this Hom-complex predicate. Mathlib's `HomComplex` and `QuasiIso` are used directly;
the existing `IsKInjective` was not reused because its definition is the null-homotopy
form and Mathlib documents the equivalence as TODO.

No `STATEMENT-DISPUTED` issue.

## Earlier second reading (a previous round; superseded)

Reading the node and module together: the scheme, commutative ring, three complexes,
Hom-complex degree formula and signed differential are represented by the stated
Mathlib constructions; acyclicity is required for every acyclic `A`; and the
resolution clause has exactly a quasi-isomorphism into a K-injective `I`. No
hypothesis or conclusion was added or omitted.

## Second reading by J1

I read the node, its Stacks source (Definition 070H and Lemma 070K), the blueprint
formulation, and the Lean module line by line. The objects and clauses match as follows:

* `T : Scheme.{u}` is the node's scheme, and `R : Type (u + 1)` with `[CommRing R]`
  is its commutative coefficient ring in the dependency's universe convention.
* `Mod(T_{Et},R)` is exactly
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)`.
* `A`, `I`, and `K` are `CochainComplex` objects in that category with shape `ℤ`.
* Mathlib's `HomComplex A I` supplies the node's degreewise product and signed
  differential; its source confirms the stated Hom-complex construction.
* K-injectivity is exactly `∀ A, A.Acyclic → (HomComplex A I).Acyclic`, using the
  recorded `HomologicalComplex.Acyclic` declaration.
* A resolution is exactly `QuasiIso f ∧ IsKInjectiveHomComplex T R I` for
  `f : K ⟶ I`, the node's quasi-isomorphism followed by K-injectivity. The source
  convention for etale abelian sheaves is included by the specialization `R = ℤ`.

No mismatch was found and no node or statement text was changed. Empty index/product,
zero complexes, degree `n = 0` and negative degrees, the empty scheme, and `R = ℤ`
are all admitted. Universes are explicit and no variable is auto-bound.

I repeated the H4 searches with LeanFinder (K-injective Hom-complex criterion), Loogle
(`IsKInjective`/`HomComplex`), and `rg` over Mathlib and `WeilConjectures`. They found
Mathlib's null-homotopy `CochainComplex.IsKInjective` and `HomComplex`, but no
declaration of this Hom-complex criterion; Mathlib marks the equivalence as TODO. The
project source has no matching declaration. The dependency declarations were opened
and used directly; no private copy or dependency module was needed. `scompile.py`
compiled the module cleanly.

## Review fix by R-kir1302 (H4)

The delivered `CochainComplex.IsKInjectiveHomComplex` is a second definition of K-injectivity:
Mathlib's `CochainComplex.IsKInjective` (Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean)
is the same notion, literally Stacks Definition 070H (every map from an acyclic complex is
null-homotopic, i.e. Hom_K(A, I) = 0), and its source comment records the Hom-complex form of
this node as the equivalent Spaltenstein formulation (H^n Hom^•(A, I) = Hom_K(A, I[n]) and the
acyclic complexes are closed under shifts). The project already uses Mathlib's class for this notion
(def-pur-kinjective-complex, status mathlib; the consumers lem-weil-pbc-kinjective-shift,
lem-weil-pbc-kinjective-hom-derived, lem-weil-pbc-bounded-below-injectives-kinjective,
lem-weil-pbc-kinjective-functorial-existence, prop-weil-pbc-cohomology-resolution-independent,
lem-weil-pbc-right-adjoint-preserves-kinjective all state it with `IsKInjective`). The module now
declares only `CochainComplex.IsKInjectiveResolution T R f := QuasiIso f ∧ I.IsKInjective` for
`f : K ⟶ I` in `CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ` (R = ℤ for
étale abelian sheaves), with Mathlib's `CochainComplex.IsKInjective` and `QuasiIso` cited in the
record. Checked with `#check` and compiled in an L sandbox.
