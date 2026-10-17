## What changed

Repaired the returned direct import by adding the fully proved Sheaf variant
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isAffine_of_dimension_le`
in `Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionBound`.
It accepts an explicit Krull-dimension bound, proves the natural-number comparison, and handles
empty schemes from the existing affine theorem's separate all-degree vanishing clause.
It contains no sorry. Its import of the existing affine theorem is proof-only.

The assigned source module now privately imports this variant instead of
`Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine`.
Its proof installs the given structure morphism, converts the ground-field cohomology bound,
applies the variant, and converts the resulting cohomology bound back to `Sheaf.H` with
`nonempty_sheafH_extDerivedIso`. Its signature, visibility, docstring, and all public imports
are unchanged. This changes the retained delivery's proof and import route; it is not a rebase
or an unchanged re-push. The numerical and empty-case argument is now a separately proved API.

Retained the earlier acyclicity repair in the unclaimed Sheaf affine theorem module: remove
only its unused private proof imports; keep every public import, signature, and proof body.
No existing mathematical statement or definition changes. Updated the existing downstream
wrapper node to record the actual proof route, and added a node for the proved variant.
Change record: `coord/changes/B3-affine-cohomological-dimension-reuse.md`.

Validation: the delivered modules compile together. The original three direct consumers of
the adapted Sheaf module compile successfully against the delivered overlay; no consumer changes.
The required delivery dry run performs the axiom probe and import-cycle/static checks.

## Proved and sorry left

Closed 1 of 1 original holes in the assigned module:
`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`.
The assigned module has zero sorry left. Added zero holes and zero split-offs.

The new variant
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isAffine_of_dimension_le`
is fully proved from the pre-existing affine theorem. It is not a new sorried restatement.

The pre-existing hole remains unchanged:
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isAffine`
(node `thm-sc-affine-torsion-cd`) in
`Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine`.
The source bridge and new variant depend transitively on this hole. This delivery does not
claim to close the geometric affine calculation or its transitive axioms.

## No longer needed

Removed the direct private import of
`Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine`
from the assigned source module. It now imports the proved explicit-dimension variant.
The original affine theorem remains a needed transitive dependency; no mathematical module
or node is claimed to be globally pruned.

Removed these private imports from the Sheaf affine theorem module:

- `Mathlib.RingTheory.NoetherNormalization`
- `WeilConjectures.Mathlib.RingTheory.NoetherNormalization`
- `Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension`
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField`
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel`
- `Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`
- `Sheaf.FieldTheory.OneVariableFieldCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit`
- `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Sheaf.AlgebraicGeometry.GeometricFiberFinite`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve`
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
- `Mathlib.RingTheory.RegularLocalRing.Defs`
- `Sheaf.AlgebraicGeometry.SupportDimensionUnion`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`
- `WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound`
- `Sheaf.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`

No node or module is asserted globally unnecessary: the original geometric proof plan remains
the task of the existing affine theorem. These are unused private imports of its current
statement-only file; they are not inputs to the proved source bridge. No import removed from
the source module's inherited public interface. No new geometric lemmas were needed.

## Where the brief, the DAG or earlier work was wrong

The returned direct upstream import has been removed, and the needed explicit-dimension
variant is stated and proved in a Sheaf module, as the return requested. The current gate also
permits private Sheaf proof imports; the source library's existing statements remain verbatim.
The earlier report's direct-reuse route and its second reading predated this repair; a fresh
independent reading is required for the revised variant and bridge.

The assigned source module has no node whose lean.module exactly names it. Its docstring names
`thm-sc-affine-torsion-cd`, attached to the existing Sheaf theorem. The downstream wrapper node
`new-thm-sc-affine-torsion-cd-bound` now describes the actual bridge through the new variant.
The existing geometric affine node's proof plan and the blueprint unit route remain intact.
Unused private imports of the statement-only affine module caused an import cycle through later
proper-base-change results; their removal is retained and does not change its mathematical API.

Edge cases: the empty case uses no dimension conversion; the nonempty dimension comparison
works for `d = 0` and for larger upper bounds. Quasi-compactness needed by the variant is inferred
for the structure morphism from the affine source and target, so the source theorem gains no
hypothesis. All source universes and binders remain unchanged.

## New nodes

`lem-sc-affine-torsion-cd-explicit-bound` records the new fully proved explicit-dimension
variant. Its proof dependency is the existing `thm-sc-affine-torsion-cd`; the proof combines
its two clauses with `WithBot.unbotD_le_iff`, `ENat.toNat_le_of_le_natCast`, and arithmetic.
It has zero sorry. The Mathlib searches and exact Lean signature are recorded in its node.
No new unfinished mathematical obligation is introduced.

## Second reading by B3

Independent second reader, 2026-10-17, of the revised delivery after the returned
direct import. Read all three delivered Lean modules, both delivered node records,
the original `thm-sc-affine-torsion-cd` node, the source blueprint statement and proof,
the cohomological-dimension definitions, and `nonempty_sheafH_extDerivedIso`.

1. **Existing interfaces: pass.** Diffed both existing delivered modules against
   the shared repository. The source theorem's binders, hypotheses, conclusion,
   visibility and docstring are byte-for-byte unchanged. Its only changes are two
   private proof imports and the replacement of its sorry by the bridge proof.
   The existing Sheaf affine module differs only by deletion of the 36 reported
   private imports; its four public imports and its entire declaration are unchanged.
   No definition or target statement changes. The change record describes this
   unclaimed module's import repair and its users.
2. **Proof and trust: pass, conditional on the existing affine hole.** Compiled all
   three delivered modules together with `lcompile.py --all`. No delivered-file
   errors or warnings. Searched their source for forbidden declarations and holes:
   the only sorry is the unchanged named affine theorem in `OfAffine`; the new
   variant and assigned source theorem contain none. A scratch `#print axioms`
   check of all three theorem names reports exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. Thus the bridge closes its own original hole but
   does not establish the geometric affine theorem independently. There is no
   data definition or witness chosen from an unproved existence statement here:
   elimination of the comparison isomorphism's `Nonempty` stays inside proofs.
3. **New statement and edge cases: pass.** There are zero split-off holes. The
   fully proved new variant keeps precisely the affine finite-type field setting,
   the derived-section cohomology convention, and the explicit upper dimension
   bound. Its empty branch applies the existing all-degree empty clause directly.
   Its nonempty branch uses `WithBot.unbotD_le_iff` (the bottom side condition is
   `0 ≤ d`) and `ENat.toNat_le_of_le_natCast`, then monotonicity of addition.
   These steps work for `d = 0`, `c = 0`, and non-sharp bounds; no excluded empty
   case or hidden finite-dimension premise is introduced. The source morphism
   installs the same `X.Over` structure; quasi-compactness is inferred from affine
   source and target. The field conversion uses the inverse comparison injection;
   the conclusion uses its forward injection, in the correct directions.
   Repeated searches with different terms: LeanFinder for transport of trivial
   cohomology through Ext/derived-section comparison, Loogle for
   `WithBot.unbotD_le_iff`, and local `rg` for affine bounds and dimension-bound
   variants. The existing downstream `Sheaf.H` wrapper calls the source theorem
   and cannot replace this argument without circularity; no independent shorter
   affine bound was found. The new theorem's source and complete word proof are
   in its docstring and its matching node.
4. **Route and pruning: pass.** The proof uses the existing affine theorem rather
   than a new geometric obligation. All new proof-only imports are private;
   the new variant's public imports provide its statement's cohomology, dimension,
   finite-type and affine APIs. Every deleted private import is listed above.
   The old wrapper dependency `thm-sc-affine-torsion-cd` remains transitively needed
   through the explicit-bound lemma; no mathematical node or module is claimed
   pruned. Read `dag/units/sk-prop-sf-cbc.json`: its `realized` lists are unchanged,
   and the geometric affine node and its unit route remain intact. Original copies
   of all three direct consumers of `OfAffine` were compiled against the delivered
   overlay, without source edits.
5. **DAG agreement: pass.** The new node's verbatim Lean signature matches the
   explicit-bound theorem, and its sole proof dependency is the affine theorem
   whose two clauses it actually uses. Its elementary numerical step records both
   order lemmas. The existing downstream wrapper node records the bridge through
   the new variant and the Ext/derived comparison, matching the source proof and
   the wrapper's unchanged call to that source theorem. Its statement, Lean record,
   and maintainer-owned fields are preserved. No old dependency is silently
   declared globally unnecessary.

Second reading changed only this report, adding the independent checks and their
verdicts. No Lean or DAG repair was necessary. The required delivery dry run also
checks every delivered declaration's axioms and the complete import graph.
