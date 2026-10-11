## Worker report

The module states `AlgebraicGeometry.lft_over_field_isolated_point_residue_finite`.
It binds a field `k`, a scheme `Y` over the same universe, a morphism
`g : Y ⟶ Spec (CommRingCat.of k)` with the Mathlib `LocallyOfFiniteType g`
instance, a point `y : Y`, and the hypothesis `IsOpen ({y} : Set Y)` expressing
that the singleton is open.  The conclusion is `FiniteDimensional k
(Y.residueField y)`.  The `Algebra k (Y.residueField y)` instance is explicitly
induced by the residue-field map of `g`, after composing the canonical map from
`k` into the residue field of `Spec k` using
`Scheme.Spec.residueFieldIso`; this renders the field extension induced by `g`.
The proof is `sorry`, as required for stage 2.

The dependency declarations used are Mathlib's `AlgebraicGeometry.Scheme` and
`Scheme.Hom` (the `def-pc-scheme` and `def-weil-affine-spectrum` records),
`AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.Scheme.residueField`,
and `Algebra`/`FiniteDimensional` for the field extension and finiteness notion.

Edge cases checked: the universe of `k` and `Y` is shared so that `Spec k` is a
scheme in the same category; the point may be any point (including an empty or
zero-dimensional scheme case); openness is stated for the singleton itself;
`FiniteDimensional` allows dimension zero and all finite degrees.

Searches made: `msearch.py leanfinder` for “scheme locally of finite type over a
field, isolated point, residue field finite extension” found only component
lemmas (`isClosed_singleton_iff_locallyOfFiniteType`, ring-level residue-field
finiteness); `msearch.py loogle` for `IsOpen {_} → Module.Finite _
(Scheme.residueField _ _)` found no match; `msearch.py grep` over Mathlib's
AlgebraicGeometry, RingTheory, and Topology found only ring-level and
quasi-finite ingredients; `rg` over `WeilConjectures` and `lean/Sheaf` found no
existing theorem with this statement.  The dependency records were inspected;
none gives the complete scheme-level statement.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, every node hypothesis has a direct Lean
binder: field, scheme, morphism with locally finite type, point, and open
singleton.  The residue-field algebra instance is the map induced by `g` after
the canonical `Spec` residue-field identification, and the conclusion is exactly
finite-dimensionality over `k`.  No mismatch was found.

## Second reading by K1

The node introduces, in order: a field `k`; a scheme `Y`; a morphism
`g : Y ⟶ Spec k` that is locally of finite type; a point `y : Y`; and the
hypothesis that `{y}` is open. Its conclusion is that the residue field at `y`,
with the residue-field map from `g` (the residue field of `Spec k` identified
with `k`), is finite dimensional over `k`. The Lean renders these as
`(k : Type u) [Field k]`, `(Y : Scheme.{u})`,
`(g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]`,
`(y : Y)`, and `(hy : IsOpen ({y} : Set Y))`; the `letI` algebra is the composite
of `algebraMap k _`, the inverse of `Scheme.Spec.residueFieldIso` at `g y`, and
`(g.residueFieldMap y).hom`, and the conclusion is
`FiniteDimensional k (Y.residueField y)`. Every object, hypothesis, and clause
matches the node; the shared universe is sufficient and does not exclude any
case.

I checked the empty scheme (there is then no `y`), an arbitrary isolated point,
zero-dimensional schemes, and the characteristic and `n = 0` edge cases (none
adds a hypothesis; finite dimensionality includes dimension zero). The singleton
openness is exactly the node's isolated-point condition. Searches with
`msearch.py` LeanFinder and Loogle, and `rg` over Mathlib, `WeilConjectures`, and
`lean/Sheaf`, found only component lemmas such as
`isClosed_singleton_iff_locallyOfFiniteType`, ring-level residue-field finiteness,
and the separate fibre theorem
`Scheme.Hom.finiteDimensional_residueField_of_isOpen_singleton_asFiber`; no exact
scheme-over-a-field statement exists. The existing dependency declarations were
opened and are used only for the notions named by the node.

The worker statement was mathematically aligned and compiled. I found no
statement mismatch and changed no binders or definitions. I strengthened the
module docstring to record the source and all four proof steps required by the
node; the theorem remains an unproved stage-2 statement with only `sorry`.

## Reviewer fix (R-lfi1115)

The hand-built `letI : Algebra k (Y.residueField y) := RingHom.toAlgebra (...)` was a second
spelling of the source's `Scheme.Hom.residueFieldAlgebraMap` (WeilConjectures/ZetaSeries.lean,
used by landed ClosedPointField and EtaleSupport; the same H4 fix was made on M1
lem-kun-closed-point-field). It is replaced by `(g.residueFieldAlgebraMap y).toAlgebra`
(import `WeilConjectures.ZetaSeries`), checked definitionally equal (`rfl`) to the delivered
composite, and the `letI` is parenthesised for the stage-2 sorry check. Otherwise the
statement matches the node unchanged.
