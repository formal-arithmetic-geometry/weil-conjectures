## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_tensorPullback_affine_sections`
with its original signature. Constructed the map by `TensorProduct.lift` from the
restricted unit, proved its pure-tensor formula and second-factor B-linearity,
and proved naturality by tensor induction from the unit's naturality and the
pulled-back morphism's compatibility with restriction.

Added two proved helper modules:
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSectionsBijective` and
`Sheaf.AlgebraicGeometry.ModulePullbackAffineChartUnit`.
The bijectivity proof uses the existing source-library `pullbackSpecΓEquiv` and
`pullbackSpecΓEquiv_one_tmul` from
`WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde`, and
`sectionsRestrictFromSpecLinearEquiv` from
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`.
It constructs the comparison of the two chart routes by uniqueness of left
adjoints, composes the resulting section equivalences, and checks their formula
on pure tensors. The specified tensor pullback is compared with the standard
pullback by the unit equation for uniqueness of left adjoints.

The chart helper proves the corresponding unit equation on sections, without
quasi-coherence: restrict the composite-adjunction unit equation to the top open,
use naturality to move the two transports through the unit and the comparison,
and compose the remaining restrictions. All inclusion morphisms agree by
proof irrelevance in the category of opens.

The original node's proof now describes the actual tensor construction and
naturality argument. The two helper nodes carry the geometric part of the old
plan. No unit statement or realized step is bypassed.

The elaboration-option change record is
`coord/changes/module-pullback-affine-sections-elaboration.md`.

## Proved and sorry left

Proved the one original sorry:
`AlgebraicGeometry.Scheme.Modules.exists_tensorPullback_affine_sections`
(node `lem-weil-pbc-module-pullback-affine-sections`).

Also proved:
`AlgebraicGeometry.Scheme.Modules.tensorPullback_affine_sections_bijective`
(node `lem-weil-pbc-module-pullback-affine-sections-bijective`) and
`AlgebraicGeometry.Scheme.Modules.affineChart_pullback_unit`
(node `lem-weil-pbc-module-pullback-affine-chart-unit`).

No sorry remains in any delivered module; none is split off.
The existing dependency `exists_tensorPullbackAdjunction` is still used as the
specified adjunction and remains an item elsewhere. Its proof is outside this delivery.

## No longer needed

Removed proof imports from the original module:

- `Sheaf.AlgebraicGeometry.TensorPullbackTilde`: the proved standard-pullback
  implementation of affine tilde base change is reused, with the unit-preserving
  comparison to tensor pullback proved explicitly. This route does not need
  `Sheaf.AlgebraicGeometry.AssociatedModulePullback`, the proof dependency imported
  by the removed module.
- `Sheaf.AlgebraicGeometry.TensorPullback`: a redundant direct import, already
  available through the unchanged public import `TensorPullbackAdjunction`.
  The tensor-pullback definitions themselves are still needed.

The mathematical node `lem-weil-pbc-tilde-pullback-base-change` remains a dependency
of the geometric helper, realized here through the already-proved source-library
standard-pullback version and the explicit uniqueness-of-adjoints comparison.
This proof also no longer uses the node
`lem-weil-pbc-open-immersion-module-pullback-restriction`: it compares the two
composite adjunctions directly, instead of first comparing each open-immersion
pullback with restriction. This is pruning below the unit level. The other
geometric dependencies move to the helper nodes. No claim is made that another
target's proof cannot still need the removed node. The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned imported tilde theorem is unnecessary: the source library already
proves the standard-pullback affine comparison and its unit formula.
Its difference from the specified tensor-formula pullback is handled in Lean
by `leftAdjointUniq` and `unit_leftAdjointUniq_hom_app`, rather than assumed.
No statement was disputed or changed.

The local literature .tex files and blueprint _section.md path were absent on
this machine; the unit record was read, and Stacks Tags 00A0 and 0097 were checked
on their public pages. Their restriction and composition statements agree with
the constructions used here.

The new chart lemma was checked on identity morphisms, empty affine opens and
zero modules: it is an equality of canonical restrictions and transports, needs
no nonempty assumption, and all maps in the zero cases are unique. The
bijectivity proof requires precisely quasi-coherence to invoke the existing
`pullbackSpecΓEquiv`; no finiteness, separation or flatness is assumed.

## New nodes

`lem-weil-pbc-module-pullback-affine-chart-unit` records the proved unit compatibility
for restriction and pullback through the affine-chart square (old plan steps 3–4).
It has no quasi-coherence or tensor-product hypothesis.

`lem-weil-pbc-module-pullback-affine-sections-bijective` records the proved bijectivity
part of the affine comparison. It combines the existing source affine equivalence,
the chart-unit equation and the tensor/standard-pullback unit comparison (old
plan steps 1–6). Both new statements are fully proved.

## Second reading by T2

1. Compared the delivered module with the repository version. The existing theorem signature is byte-for-byte unchanged; only the two helper modules, three node records, and the recorded elaboration option change are added. Verdict: passed.
2. Compiled all three Lean files locally. No `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations remain. Verdict: passed.
3. Checked the helper statements on identity, empty-open, and zero-module cases and searched for duplicate declarations. Both are true and strictly intermediate. Verdict: passed.
4. Read proofs from the target downward. The affine comparison uses the existing standard pullback equivalence and uniqueness of left adjoints; unused imports and the pruned open-immersion dependency are listed above. Verdict: passed.
5. Matched every Lean proof step and helper use to the node `proof` and `proof_deps`; the unit's realized route remains represented by the helper nodes. Verdict: passed.

I changed only this second-reading report section; no Lean proof or statement needed repair.
