## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleTwistOpenRestriction` defines
`invertibleTwistOpenRestrictionIso`, then states
`invertible_twist_open_restriction` with proof `sorry`. The theorem has explicit
binders for schemes `X,Y`, a morphism `f`, invertible modules `L,M`, and a natural
number `a`. Its first three conjuncts render invertibility of `M.tensorPow a`, its
pullback, and `L ⊗ f^*(M.tensorPow a)`. For each open `U : Y.Opens`, the nested
existentials render invertibility of the restricted left and right modules, the
specified isomorphism, equality with the displayed composite, and the equivalence
of their `IsAmple` predicates. No quasi-compactness, affine, finite-type, or
ampleness hypothesis is added.

The existing `boundaryPullbackPowIso` uses the adjunction comparison with Mathlib
pullback and its unit isomorphism in degree zero, then the canonical tensor
comparison at each successor. It is reused without a duplicate power construction.
`invertibleTwistOpenRestrictionIso` composes the pullback tensor
comparison, the inverse of `tensorPullbackSectionComp` for `j` and `f`, the equality
`morphismRestrict_ι f U`, the comparison for `f ∣_ U` and `U.ι`, and the pulled-back
power comparison. Thus the order and objects are the ones in the node. The
separate statement `invertibleTwistOpenRestriction_power_zero` records that the
zero-degree comparison is the canonical structure-sheaf map; its docstring records
the tensor formula `b ⊗ c ↦ b * h♯(c)` and inverse `b ↦ b ⊗ 1`.

Dependency declarations used: `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom` (Mathlib); `AlgebraicGeometry.Scheme.Modules.IsInvertible`
from `WeilConjectures.AlgebraicGeometry.Modules.Invertible`;
`AlgebraicGeometry.Scheme.Modules.tensorPullback` from
`WeilConjectures.AlgebraicGeometry.TensorPullback`; `AlgebraicGeometry.Scheme.Modules.tensorObj`
and `tensorPow` from `WeilConjectures.AlgebraicGeometry.Modules.Invertible`;
`AlgebraicGeometry.Scheme.Modules.IsAmple` from
`WeilConjectures.AlgebraicGeometry.Ample`; `boundaryPullbackTensorIso` and `boundaryPullbackPowIso` from
`WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`; canonical structure-sheaf
map from `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`;
`tensorPullbackSectionComp` and `morphismRestrict_ι` from their recorded modules;
and `isAmple_iff_of_iso` from `WeilConjectures.AlgebraicGeometry.AmpleIso`.

Edge cases checked in the statement design: `a = 0` uses the unit comparison;
`a = 1` uses the successor branch; `U = ⊥` and `U = ⊤` are allowed; empty `X`
and `Y` are allowed; no morphism finiteness or quasi-compactness is assumed.
The module was compiled with the required `scompile.py` wrapper and had no errors
or warnings.

Searches made: `msearch.py leanfinder` for restriction of invertible sheaf twists
(no full match; hits were generic pullback/restriction declarations);
`msearch.py loogle '"tensorPow", "pullback"'` (zero hits);
`msearch.py grep 'invertible.*restrict|restrict.*invertible|pullback.*tensorPow|twist.*restriction' AlgebraicGeometry`
(no matching full statement); `rg` over `lean/WeilConjectures` and `lean/Sheaf`
(found only generic tensor-power restriction modules and no duplicate declaration).

No `STATEMENT-DISPUTED` flag or node fault.

## Second reading by Q99

I reread the node and module line by line. The hypotheses are exactly `f`, `L`,
`M`, their invertibility instances, and `a : ℕ`; the clauses are the three global
invertibility claims and, for every open `U`, both restricted invertibility claims,
the explicitly named composite isomorphism, and simultaneous ampleness. The empty
open/scheme and zero-power cases remain admitted. The canonical comparison
interfaces are imported from the recorded modules, and no private replacement of a
notion is introduced. The source's degree-zero multiplication/insertion formulas
are recorded in the dedicated zero-power statement and its docstring.

The two added statement dependencies are the landed definition owners:
`def-sc-tensor-pullback-power-comparison` records `boundaryPullbackComparison`,
`boundaryPullbackTensorIso`, and `boundaryPullbackPowIso` in
`WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`;
`def-sfb-tensor-pullback-structure-sheaf-map` records
`tensorPullbackObjUnitToUnit` in
`WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`.
Their full definition signatures and source docstrings were checked. Both interfaces
apply to arbitrary scheme morphisms, with no invertibility, immersion, or square-zero
hypotheses on these definitions.

## Repair of returned delivery 745a6dd6de3b

H2 repaired: replaced the statement-dependency citations
`lem-sc-square-zero-ideal-tensor-unit` and
`lem-weil-pbc-module-pullback-structure-sheaf` by
`def-sc-tensor-pullback-power-comparison` and
`def-sfb-tensor-pullback-structure-sheaf-map`, respectively. The definitions used in
the statement belong to these landed definition nodes; neither owning theorem is
used to construct the statement. The original structure-sheaf isomorphism theorem
remains in `proof_deps`, as required by the unchanged proof plan. The Lean module
is unchanged from the returned head, whose mathematics was accepted clause by clause.
The node copy was refreshed from the current read clone before applying the Lean
record and these two additions. The report now names the actual definition owners.
