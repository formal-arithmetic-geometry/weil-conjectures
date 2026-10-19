## Worker report

The node is already stated exactly by Mathlib's
`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton`
in `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`.  The declaration is tagged
`@[stacks 02UP]` and has no Noetherian hypothesis.

The Lean statement renders every clause of the node as follows:

- `f : X ⟶ Y` is the scheme morphism, with `X Y : Scheme` implicit in the
  declaration's surrounding variables.
- `[IsProper f]` is the properness hypothesis.
- `y : Y` is the chosen point `s ∈ S`.
- `(f ⁻¹' {y}).Finite` is finiteness of the underlying set-theoretic fibre.
- `∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V)` gives an open neighbourhood of
  `y` and finiteness of the restricted morphism.

The dependency notions are Mathlib's `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.IsProper`, and `AlgebraicGeometry.IsFinite`, recorded by the
three statement dependencies.  No module is added because the complete
statement already exists in Mathlib.

Edge cases checked: the theorem permits an empty finite fibre, imposes no
Noetherian assumption on the target, and uses an arbitrary scheme point and
arbitrary open neighbourhood.  The restriction notation `f ∣_ V` is the
canonical scheme morphism restriction.

Searches made:

- `msearch.py ... leanfinder` for a proper morphism with finite fibre finite near
  a point: found the Mathlib theorem and related proper/finite declarations.
- `msearch.py ... loogle` for `IsProper`, `IsFinite`: found the exact theorem's
  Stacks 02UP counterpart among related results.
- `msearch.py ... grep` and `rg` through Mathlib and `WeilConjectures`: found the
  exact declaration only in `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`.
- `scompile.py` probe with `#check` and `#print`: confirmed the full signature
  and declaration path.

No `STATEMENT-DISPUTED` flag or node fault.

## Second reading by Q72

The existing Mathlib declaration was independently checked with `#print`. Its
hypotheses and conclusion match the node clause by clause, including the empty
fibre case and absence of a Noetherian hypothesis. No mismatch was found.
