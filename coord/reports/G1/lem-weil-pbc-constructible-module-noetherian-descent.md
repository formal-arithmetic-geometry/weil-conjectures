## Worker report

The module states the Noetherian descent assertion for a constructible sheaf of modules. The
hypotheses are: a finite commutative coefficient ring `Λ`; a scheme `X` with
`[CompactSpace X]` and `[QuasiSeparatedSpace X]`, rendering quasi-compact and quasi-separated;
a sheaf `F : Sheaf X.smallEtaleTopology (ModuleCat (u+1) Λ)`; and its constructibility
predicate `Scheme.IsConstructibleEtaleModuleSheaf F`. The conclusion introduces a scheme `X'`,
with `IsNoetherian X'` (the Mathlib class bundling locally Noetherian and quasi-compact), a
morphism `ν : X ⟶ X'`, and a sheaf `F'` on `X'`. It requires `F'` constructible and a
`Nonempty` isomorphism from the inverse-image functor
`(ν)^*[ModuleCat (u+1) Λ]` applied to `F'` to `F`.

The dependency declarations used are `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
(`AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`) for constructibility,
`AlgebraicGeometry.Etale.upperStar` from
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` for inverse image, and Mathlib's
`AlgebraicGeometry.IsNoetherian` for the Noetherian scheme notion. The scheme convention node
is rendered by `CompactSpace` and `QuasiSeparatedSpace`; the sheaf-module category is rendered
by `Sheaf` with `ModuleCat`.

Edge cases checked: `Λ` is allowed to be any finite commutative ring (including the zero ring);
`F` may be the zero sheaf; no nonemptiness, connectedness, or finiteness assumption is imposed
on `X`; and the isomorphism is existential (`Nonempty`) as in the source. Universe `u+1` is
used for coefficient modules and the sheaf value category, while schemes and morphisms remain
in `Scheme.{u}`.

Searches for an existing declaration: `msearch.py leanfinder` queried “constructible sheaf on a
qcqs scheme is the inverse image of one on a Noetherian scheme” and found only generic sheaf
pullback constructions; `msearch.py loogle` queried `IsNoetherian, upperStar, constructible
etale sheaf` and found no matching theorem; `msearch.py grep` and `rg` searched Mathlib,
`WeilConjectures/`, and `lean/Sheaf` for `noetherian descent`, `constructible` and
`upperStar`. The only relevant declarations were the dependency predicate and generic
`Etale.upperStar`; no existing statement was found.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, the binders match the node's quasi-compact,
quasi-separated `X`, finite commutative `Λ`, constructible module sheaf `F`, and the conclusion's
Noetherian `X'`, morphism `ν`, constructible `F'`, and inverse-image isomorphism. `IsNoetherian`
combines the node's locally Noetherian and quasi-compact qualifications. The source's optional
remark that one may choose finite type over `Spec ℤ` is explanatory and is not an additional
hypothesis or required conclusion in the node's formal sentence. No mismatch found.

## Second reading by G1

I read the node statement, its Stacks source, and the Lean declaration item by item.

* The node introduces a qcqs scheme `X`; Lean renders this as
  `{X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]`. These are exactly the
  two scheme properties in `def-weil-pbc-scheme-conventions`.
* It introduces a finite commutative coefficient ring `Λ`; Lean has
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. `Finite` permits the zero ring and
  imposes no stronger algebraic condition.
* It introduces a constructible module sheaf `F` on `X_ét`; Lean uses
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and the hypothesis
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F`, exactly the dependency
  `def-weil-pbc-etale-constructible-sheaf`. The etale-sheaf and module-category
  dependencies are represented by this stated sheaf category, with no private copy.
* The conclusion introduces `X'`; Lean has `∃ X' : Scheme.{u}, IsNoetherian X'`.
  Mathlib's `IsNoetherian` extends `IsLocallyNoetherian` and `CompactSpace`, matching
  the node's locally Noetherian and quasi-compact qualifications.
* It introduces `ν : X ⟶ X'` and `F'` on `X'_ét`; Lean has the nested
  `∃ (ν : X ⟶ X') (F' : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  It requires `Scheme.IsConstructibleEtaleModuleSheaf F'`, exactly as in the node.
* Finally, Lean states
  `Nonempty (((ν)^*[ModuleCat.{u + 1} Λ]).obj F' ≅ F)`. This is the recorded
  `AlgebraicGeometry.Etale.upperStar` inverse image (`def-weil-pbc-inverse-image`),
  with the same direction and existential isomorphism as the node.

No mismatch was found. The optional source remark that `X'` may be finite type over
`Spec ℤ` is not a separate conclusion in the node and is therefore not added. Empty
index sets do not occur in this existential statement; the zero ring and zero sheaf are
allowed, and no connectedness, nonemptiness, or finiteness of `X` is assumed. The
universe `u` is shared by both schemes and `u + 1` by `Λ` and module sheaves, so no
universe restriction removes a source case. The characteristic is unrestricted.

I searched Mathlib, `WeilConjectures/`, and `lean/Sheaf` with `msearch.py` LeanFinder,
Loogle, and grep/rg for Noetherian descent, constructible étale module sheaves, and
`upperStar`; only the dependency declarations and generic pullback constructions were
found. No existing theorem states this result. The only change in this second reading
was to expand the theorem docstring with the five proof steps from the node; the Lean
signature and node statement remain verbatim unchanged.
