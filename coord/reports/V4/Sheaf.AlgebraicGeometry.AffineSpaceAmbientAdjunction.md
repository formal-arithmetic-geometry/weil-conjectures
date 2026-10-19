## What changed

Retained and checked the earlier explicit coordinate-tower construction against the current
sources. Added three modules: AffineSpaceAmbientTower defines actual recursive composites and
proves their adjunction; AffineSpaceAmbientLeftComparison identifies the left tower with
ordinary compact supports by induction; AffineSpaceAmbientRightComparison proves the natural
tensor/pullback/shift comparison. The item transports the composite adjunction across
the two comparisons using `Adjunction.ofNatIsoLeft` and `Adjunction.ofNatIsoRight`.
The original theorem signature and all original public imports are preserved.
The right comparison asserts no adjunction and requires no compact-support comparison, trace,
unit or counit identity. It is strictly the tensor calculation in steps 3--6 of the source.
No definition chooses data from an unproved existence theorem.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.nonempty_affineSpaceAmbientAdjunction`: one old hole closed,
zero holes added, zero sorries left in the four delivered modules. No split-off obligation
remains. The three new modules contain proved constructions and comparisons, not new
unproved statements. The proof uses the existing projective-line adjunction, compact-support
comparison, finite-twist pullback and flatness declarations as permitted stage-3 dependencies.

Proved auxiliaries include `AlgebraicGeometry.Etale.ambientCoordinateEquiv`,
`AlgebraicGeometry.Etale.ambientSuccessorChart_over`,
`AlgebraicGeometry.Etale.nonempty_ambientTowerAdjunction`,
`AlgebraicGeometry.Etale.nonempty_ambientTowerLeftComparison`, and
`AlgebraicGeometry.Etale.nonempty_ambientTowerRightComparison`.

The retained right-comparison draft exceeded the single-file limit. The completed proof
uses generic typed tensor/shift and composite-pullback comparisons, explicit equations for
the recursive tower, and an abstract functor-tower induction. The unit-pullback calculation
is also proved once for an arbitrary scheme morphism: specializing `simp` directly to the
projective-space projection caused expensive unfolding of that concrete morphism.
All four modules pass `lcompile.py --all` again in this resumed session on 2026-10-19:
tower 8.0 seconds, left comparison 7.4 seconds, right comparison 29.8 seconds, and item
10.3 seconds. The calculation stays in the same module; no compilation limit is raised
and no file is split to evade its limit.

## No longer needed

Removed these direct proof imports from the item (some remain used transitively by the
three smaller modules; no whole-library reachability claim is made):

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `WeilConjectures.Compactification.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `Sheaf.Paper.RingedTopoiDerivedTensorPullback`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

Removed the unused `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure` proof import
from the right-comparison module.

The field-specific existence theorem `def-asd-compactifiable` is not used: the standard
relative projective compactification already supplies the required instances.
`Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint` and chosen exceptional adjoints are unused.
The open/etale adjunctions are the already proved derived sum-extension adjunctions in the
source library. The exactness and composition declarations, finite-twist pullback and
flatness facts, projective-line adjunction and unbounded compact-support comparison remain
needed in the tower or the proved right comparison; they are not claimed pruned.
The finite-type, properness, projective-space properness and open-immersion etaleness
nodes also remain used through their existing instances, as recorded in the new nodes.
The only original declared proof dependency unused throughout this proof route is
`def-asd-compactifiable`; it assumes a base field, which this statement does not require.
The six old parent `tool_uses` entries are withdrawn from that parent, whose immediate
proof now uses only the three new tower/comparison nodes. Their mathematical uses are
recorded on the relevant new nodes. The parent statement dependencies are unchanged.

## Where the brief, the DAG or earlier work was wrong

Retained the earlier sandbox and began with the required dry run. Earlier retained
work repaired a right-comparison timeout rather than leaving its former split-off sorry.
The retained attempt checked those proofs against its current sources and recompiled all
four modules successfully. The latest resumption checked the exact theorem signature and
public imports against the current source: both are unchanged. No further Lean changes
were necessary; the stale exceptional-adjoint entry in the removed-import list was dropped. The dry run found a
metadata mismatch in the recursive definition attachment. The tower node now uses its
proved adjunction as the primary declaration, retaining all constructions in its declaration list. Preserved every original public import and the exact
original theorem signature. Updated the new nodes' source paths to the current
main-20261015 blueprint (the affine-space corollary is now under sec-six-functors-basics).
The similarly named source-library theorem
`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace` remains
unproved and uses the `HasTateTwist.IsNormalized` interface, so it does not supply a
shorter proof for this concrete finite-Tate-sheaf interface. The source's chapter and unit route is preserved: standard open chart, projective-line adjunction, zero case, coordinate
tower, compact-support composition, and addition of twists. The actual coordinate-zero
scheme is canonically isomorphic to S; the construction uses its projection rather than
silently treating it as definitionally equal to S. Checked the zero-dimensional case,
the empty base and the zero coefficient ring: the comparisons still express the unit and
composition constraints without nonemptiness assumptions.

## New nodes

`def-amb-affine-space-adjunction-tower`: explicit polynomial-coordinate schemes, open charts,
left and right recursive composites, and the proved inductive composite adjunction.

`lem-amb-affine-space-tower-left-comparison`: proved induction using normalized etale compact
supports at zero and ordinary unbounded compact-support composition at a successor.

`lem-amb-affine-space-tower-right-comparison`: proved functorial Tate tensor and shift
calculation, including the zero case and successor induction. The comparison is natural
on the entire unbounded derived categories and uses no adjunction or trace identity.
No definition, existing statement or target signature is changed, so no change record is needed.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
