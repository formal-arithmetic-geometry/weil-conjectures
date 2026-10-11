## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProperFiniteFibreFiniteNeighbourhood.lean`
states `AlgebraicGeometry.exists_open_isFinite_restrict_of_isProper_of_finite_fibre`.
It binds schemes `X S : Scheme.{u}`, assumes the base is locally Noetherian via
`[IsLocallyNoetherian S]`, takes a morphism `f : X ⟶ S` with properness
`[IsProper f]`, and a point `s : S`. The finite-fibre hypothesis is rendered by
`(f ⁻¹' ({s} : Set S)).Finite`, exactly the inverse image of the singleton fibre.
The conclusion `∃ U : S.Opens, s ∈ U ∧ IsFinite (f ∣_ U)` gives an open neighbourhood
of `s` and finiteness of the restricted morphism.

The dependency declarations used are `AlgebraicGeometry.IsProper` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper` and
`AlgebraicGeometry.IsLocallyNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`.
The restriction notation `f ∣_ U` and `IsFinite` are Mathlib definitions.

Edge cases checked include an empty fibre (the finite-set hypothesis allows it), a
singleton fibre, and arbitrary universe `u`; no nonemptiness or separation hypothesis
was added. The statement compiles with the expected `sorry` warning only.

Searches made: `msearch.py leanfinder` and `loogle` for proper finite-fibre neighbourhood
statements (no exact declaration); grep of Mathlib AlgebraicGeometry found no Tag 02OH
statement. `rg` over the project found no existing declaration for this node; the
project's `QuasiFiniteMorphism` module defines a related all-fibres predicate but not
this theorem.

## Earlier second reading (a previous round; superseded)

I reread the node statement and matched each part to the declaration. The objects `X`,
`S`, and `f` are the same schemes and morphism. The node's properness hypothesis is
`[IsProper f]`; its locally Noetherian base hypothesis is `[IsLocallyNoetherian S]`.
The point is `s : S`, and “the fibre is finite” is exactly the set-finiteness clause
`(f ⁻¹' ({s} : Set S)).Finite`. The existential open `U : S.Opens` contains `s`, and
`IsFinite (f ∣_ U)` is precisely finiteness of the restricted morphism. No hypothesis
or conclusion clause was added or omitted.

## Second reading by F1

I independently read the node statement, its source (Stacks Project, Tag 02OH, Lemma 30.21.2), the two statement dependencies, and the Lean module.

- Objects: the node's schemes $X,S$ are Lean `{X S : Scheme.{u}}`; the morphism $f:X\to S$ is `(f : X ⟶ S)`; the base-local-Noetherian hypothesis is `[IsLocallyNoetherian S]`; the point $s\in S$ is `(s : S)`.
- Hypotheses: properness is `[IsProper f]`, the Mathlib realization recorded for `[def-weil-proper-morphism]`; finite fibre is `(f ⁻¹' ({s} : Set S)).Finite`, the finite underlying point-set fibre over `s`. No separation, finite-type, quasi-compactness, nonemptiness, or field hypothesis is added.
- Conclusion: `∃ U : S.Opens, s ∈ U ∧ IsFinite (f ∣_ U)` gives an open neighbourhood of `s` and finiteness of the restriction to its inverse image, exactly the node's `f⁻¹(U) → U`.

The Lean declaration is `AlgebraicGeometry.exists_open_isFinite_restrict_of_isProper_of_finite_fibre` in `Sheaf.AlgebraicGeometry.ProperFiniteFibreFiniteNeighbourhood.lean`; its signature is verbatim the node's `lean.statement`. The source lemma says precisely that a proper morphism with finite fibre over a point is finite over an open neighbourhood; its proof route through the quasi-finite locus and proper-plus-quasi-finite finiteness agrees with the declaration docstring.

Edge cases: the finite-set predicate permits an empty fibre; singleton and larger finite fibres are included. An empty scheme and empty opens are handled by the ordinary `Scheme`/`Opens` quantifiers, while `s ∈ U` prevents an empty chosen neighbourhood. The universe is a single arbitrary `u`, so no case is excluded. No characteristic, integer, index, or nonzero assumption occurs.

Searches: `msearch.py`/LeanFinder and Loogle searches for proper finite-fibre neighbourhood statements found no exact declaration; `rg` in Mathlib AlgebraicGeometry and `WeilConjectures` found no duplicate theorem. The related `QuasiFiniteMorphism` declarations only provide consequences for an already finite morphism and are not this statement. The dependency declarations are Mathlib `AlgebraicGeometry.IsProper` (`Mathlib.AlgebraicGeometry.Morphisms.Proper`) and `AlgebraicGeometry.IsLocallyNoetherian` (`Mathlib.AlgebraicGeometry.Noetherian`), as recorded by their nodes.

Mismatches found: none. No source, node, or Lean repair was needed. The module compiles with only the permitted `sorry` warning.
