## Worker report

Repair of returned immutable head b119d32c4c13, H4. The previous delivery missed
the already landed definition owner `def-sfb-space-dimension-flat-condition` and
introduced duplicate cutoff/map definitions. This repair adds that existing
node to stmt_deps and publicly imports
`Sheaf.AlgebraicGeometry.SpaceDimensionFlatCondition`. The module deletes its
own `dimensionFlatChartMap`, `dimensionFlatTestMap`, `dimensionFlatBaseMap`,
`dimensionFlatBaseCondition`, and the old chart criterion. Every all-chart P_n
occurrence now uses `AlgebraicGeometry.AlgebraicSpace.dimensionFlatCondition`.
Its only helper is the non-colliding `dimensionFlatAtlasCondition`, the body of
that landed predicate with the outer universal chart binder replaced by one
specified chart. It uses the landed `dimensionFlatBaseMap` and
`dimensionFlatChartMap`; no map, module or tensor construction is redefined.

The theorem remains `dimensionFlat_baseChange_fpqc_atlas_sheaf`, with exactly
one `sorry`. Definitions have real data. The natural-language statement, source,
proof and proof_deps are unchanged. No new nodes or dependency modules are added.
The existing definition dependency is added as the return explicitly requests.
The delivery wrapper rebases the repaired packet onto current main; the current
main item has no Lean record. Its non-Lean/non-stmt_deps fields were compared
with the retained returned node and agree.

Source read: Stacks `spaces-flat.tex`, Tags 0CWS, 0CWT, 0CWU, 0CWW(1). Its
finite-presentation clause 0CWW(2) is not asserted here. The theorem's five-step
docstring retains the accepted chart comparison, tensor compatibility,
base-change ascent, fpqc reflection via equality lifts, and sheaf-gluing proof.

Hypothesis and clause correspondence:

| Node | Repaired Lean |
| --- | --- |
| Over Spec Z; universe convention | `Spec (.of (ULift.{u} ℤ))`, explicitly bound `u w`; section rings at u, sites at u+1 |
| Scheme base Y, algebraic space X, f:X→Y | `Y : Over SpecZ`, `X : AlgebraicSpace SpecZ`, `f : X ⟶ schemeSpace Y` |
| Locally finite type chartwise | `hf : MapIsLocally (@LocallyOfFiniteType) f` |
| Finite type quasi-coherent M | `M : X.Modules`, `hMqc : M.IsQuasicoherent`, `hMft : M.IsFiniteType` |
| Integer n≥0 | `n : ℕ` |
| Scheme B→Y | `B : Over SpecZ`, `g : B ⟶ Y`, or `b : B ⟶ Y` |
| Actual X_B and tensor pullback M_B | The landed `dimensionFlatCondition f M n g` uses `enlargedFibreProduct f (dimensionFlatBaseMap g)` and `moduleTensorPullback` of its first projection |
| Every representable etale chart and each point | The landed predicate quantifies over `EtaleSite` and its underlying scheme points |
| Residue transcendence degree at least n | Its `(n : Cardinal.{u}) ≤ @Algebra.trdeg ...` uses the residue-field map of the landed `dimensionFlatChartMap` |
| Chart module stalk flat over O_B,v | Its `schemeRestriction`, `moduleStalkFunctor`, `ModuleCat.restrictScalars` along `stalkMap`, and `Module.Flat` give exactly the actual scalar-restricted stalk |
| Arbitrary scheme base change | First conjunct: every g:B→Y and h:B'→B, `dimensionFlatCondition f M n g → dimensionFlatCondition f M n (h ≫ g)` |
| Every fpqc covering, iff | Second conjunct: arbitrary `I : Type w`, B_i and g_i:B_i→B, membership in `Scheme.fpqcPrecoverage B.left`, and `P_n(b) ↔ ∀ i, P_n(g_i ≫ b)` |
| Any one surjective etale scheme atlas | Third conjunct: arbitrary U in the actual base change's `EtaleSite`, `IsSurjective U.obj.hom`, and iff with `dimensionFlatAtlasCondition f M n g U` |
| Fpqc sheaf of maps to Y satisfying P_n | Fourth conjunct: `F : Sheaf (Scheme.fpqcTopology.over SpecZ) (Type (u+1))` with equivalences `F(B) ≃ {b : B ⟶ Y // dimensionFlatCondition f M n b}` |
| Restriction by composition | Final equation `(e B' (F.obj.map g.op s)).val = g ≫ (e B s).val` for every section; subtype proof irrelevance determines its proof component |

The test-map binders are now morphisms in `Over SpecZ` to match the landed
predicate directly. This is equivalent to the previous `Over Y.left` encoding:
a scheme B→Y acquires its ambient structural map by composition, and every
ambient-compatible morphism B→Y has this composite as B's structural map. No
case or hypothesis is lost. The sheaf remains on the absolute site over Spec Z,
with its exact values and composition-normalized restrictions.

Dependency declarations used (namespace `AlgebraicGeometry.AlgebraicSpace`
unless stated otherwise):

| Module | Declaration |
| --- | --- |
| `Sheaf.AlgebraicGeometry.SpaceDimensionFlatCondition` | `dimensionFlatCondition`, `dimensionFlatBaseMap`, `dimensionFlatChartMap`; the repaired statement's P_n and canonical maps |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties` | `MapIsLocally`, with `AlgebraicGeometry.LocallyOfFiniteType` |
| `Sheaf.AlgebraicGeometry.AlgebraicSpace` | `AlgebraicSpace`, `EtaleSite`, `Modules`, `IsEtale`, `IsSurjective` |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule` | The recorded `QCoh` uses Mathlib's `SheafOfModules.IsQuasicoherent`; the statement uses that same underlying predicate and its slice instances |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations` | `moduleTensorPullback` |
| `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` | `schemeSpace`, `enlargedFibreProduct`, `enlargedFibreProductFst` |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction` | `schemeRestriction` |
| `WeilConjectures.Algebra.Homology.ModuleStalkFunctor` | `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` |
| `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic` | Recorded `Scheme.Modules.IsFlatOver` has the stated equivalent stalkwise meaning; selected-point flatness is its actual stalk condition `Module.Flat`, not all-point flatness as an added hypothesis |
| `Mathlib.AlgebraicGeometry.Scheme` | `Scheme`, `Scheme.Hom`, `Spec` |
| `Mathlib.AlgebraicGeometry.ResidueField` | `Scheme.residueField`, `Scheme.Hom.residueFieldMap` |
| `Mathlib.RingTheory.AlgebraicIndependent.Basic` | `Algebra.trdeg` |
| `Mathlib.AlgebraicGeometry.Sites.Fpqc` | `Scheme.fpqcPrecoverage`, `Scheme.fpqcTopology`, representable subcanonicity |
| `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` | `SheafOfModules.IsFiniteType`, finite local generation |

Available proof dependencies remain imported plainly: etale fibre separable
points, the transcendence-degree tower and algebraicity facts, scheme
Zariski/etale comparison, residue-transcendence lifts, and pointwise flatness
base change. The public fpqc import supplies representable descent. The node
`lem-sfb-space-module-flat-point-chart-independence` had no recorded module in
the original packet, so it remains named in the proof docstring and DAG; no
unavailable proof declaration is manufactured to state the theorem.

Edge cases rechecked: n=0 includes every point; empty schemes have the unique
empty section; empty covering indices are allowed with no Nonempty assumption;
the zero module is retained; cutoffs exceeding every residue degree are
vacuous without a cardinal-to-natural truncation; atlases may be disconnected,
nonaffine or empty; arbitrary nonflat and nonsurjective base changes are
included. No purity, Noetherian, finite-presentation, quasi-compactness,
nonzero-stalk or diagonal assumption is added. Covering indices retain arbitrary
universe w. All variables are bound with `autoImplicit false`.

H4 search correction:

- Read the complete landed `SpaceDimensionFlatCondition.lean` and its node,
  including the signatures/docstrings of all three declarations. Its
  `dimensionFlatCondition` is exactly this node's P_n, and is now reused.
- `rg -n 'dimensionFlatCondition|dimensionFlatChartMap|dimensionFlatBaseMap'`
  in that module and its node finds the owning definition and both maps.
  The previous claim that there was no existing all-chart predicate was wrong.
- The same search in `lean/WeilConjectures` finds no upstream alternative.
  The original broad flat/dimension searches did not reliably find camel-case
  dimensionFlat names and are not evidence against the landed declaration.
- Original prescribed semantic searches: LeanFinder for dimension-filtered
  flatness, base change and fpqc descent returned eight scheme/ring flatness
  facts; LeanSearch for the cutoff fpqc sheaf returned eight unfiltered
  module/scheme facts; Loogle `"flat", "dimension"` and Mathlib grep
  `flat.*dimension|dimension.*flat` returned no hits. They found no theorem
  already proving all four clauses, but do not justify redefining P_n.
- The repaired file declares neither of the two colliding fully qualified map
  names and no replacement all-chart predicate. The only new chart helper has
  the distinct name `dimensionFlatAtlasCondition`.

## Second reading by NK

Single-worker rereading, not an independent second worker. Compared the retained
returned source with the repaired file and read the current main definition
module alongside it. All four clauses now use the landed P_n; the atlas helper
is its exact body for one fixed U, including the same tensor pullback, scalar
restriction, stalk map and residue-field algebra. The sheaf's value equivalence
and composition equation are retained. The duplicate definitions are deleted,
the existing definition owner is added to stmt_deps, and no natural-language
statement or proof is changed. The maintainer performs independent review.

Validation: `scompile.py` compiled the repaired sandbox and library module with
its public `SpaceDimensionFlatCondition` import (2.4 s and 2.0 s), with no errors
or unexpected warnings. Thus the landed map declarations and repaired consumer
load together. `deliver2.py --no-push` then compiled and passed server preflight
on current main (dry-run commit 2964cc06cec). Every delivered Lean line is at
most 100 characters. The sole postponed proof is the named theorem above.
