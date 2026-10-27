## What changed

The item theorem keeps its exact signature. Its Lean proof now applies the separate
ordered-block equation, proves the Koszul sign using `Even.mul_right` and
`Even.neg_one_pow`, and specializes arbitrary coordinate invariance to the actual
block permutation. The two still-unfinished geometric identifications are separate
public theorem modules, each with its own source, full proof sketch and DAG node.

Moved the existing coordinate and block constructions to
`Sheaf.Paper.AffineSpacePurityCompositionMaps`, retaining all their declaration names,
signatures, attributes and bodies, and publicly reexporting them from the item.
This permits the new theorem modules to share those constructions without a cycle.
There are no definition holes. The extraction is for the dependency structure,
not to avoid any compilation limit.

The canonical maps are not replaced by arbitrary witnesses. In particular
`positiveComparison` remains the uniquely specified HEq endpoint transport, and
`transportedComparison` still uses the actual polynomial coordinate map,
`coordinateSourceIso`, `isoExceptional` and `compositionInverse`. The complete
unchanged construction bodies are in the delivery diff and the change record.

Validation: `lcompile.py --all` successfully compiled all four sandbox modules,
exit code 0, with no errors or warnings. Static audit verified that the original
theorem signature is unchanged, the helper declaration bodies are identical except
for their blueprint owner tags, all node JSON parses, every proof_deps list matches
its proof-step uses union, and no missing dependency or cycle through the delivered
nodes is introduced. The first delivery preflight found two truncated `lean.statement` records: the
initial local extractor stopped at `(hg' := ...)`. Both were regenerated with
`tools/stage2_delivery.py`'s bracket-aware declaration parser. The flagged original
unit-route import was restored. No mathematical statement or proof body changed.
The required rerun of `deliver3.py` compiles and checks the repaired packet before
pushing.

## Proved and sorry left

Original hole closed in the item:
`AlgebraicGeometry.ProEtale.AffineSpacePurity.affineSpacePurityComposition`
(node `prop-pur-affine-space-composition-law`). Its arithmetic sign clause is proved
from Mathlib and its assembly is complete Lean. This is a decomposition, not a
complete mathematical proof of the composition proposition: one upper hole is
replaced by two independent strictly partial arguments.

Added holes (the entire proof of each is exactly `by sorry`):

- `AlgebraicGeometry.ProEtale.AffineSpacePurity.affineSpacePurity_orderedBlockEquation`
  (`lem-pur-affine-comparison-ordered-blocks`,
  `Sheaf.Paper.AffineSpacePurityOrderedBlocks`): only ordered block regrouping, with
  no coordinate-interchange or sign conclusion.
- `AlgebraicGeometry.ProEtale.AffineSpacePurity.affineSpacePurity_coordinateEquation`
  (`lem-pur-affine-comparison-coordinate-invariance`,
  `Sheaf.Paper.AffineSpacePurityCoordinateInvariance`): coordinate transport invariance
  for one ordered comparison, with no consecutive-block equation. It is stated for
  every positive dimension and permutation so that the block swap is a real
  specialization in the assembly.

Item: 1 original hole, 0 remaining. New modules: 2 holes total; maps: 0 holes.
All previously proved helper theorems remain proved with their original bodies.
No other theorem proof is replaced by a hole. Net textual hole change is +1.
The closure ledger, not this decomposition count, determines project progress.

## No longer needed

No mathematical dependency, DAG node or module is claimed pruned. The two new
proof sketches retain the parent's ordered-regrouping and integration-symmetry
route. In particular the generic ordered tower and the actual trace-symmetry
results remain needed by the respective coordinate-identification steps. The
unit record `sk-prop-an` and the parent statements are unchanged.

The following original private proof imports are removed from the item and not
copied into the Maps module; they do not occur in its retained helper proofs or
the final assembly. Their general mathematical roles remain in the two new
nodes, and several are already public prerequisites of AffineSpacePurityComparison.
This is direct-import cleanup, not a claim that their modules disappear from the
targets' transitive closure:

- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.Paper.SfPreservationClass`
- `Sheaf.Paper.TwistPreservesFiniteness`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Sheaf.Paper.AffineLinePurityComparison`
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`

No original public import is removed or made private. The original private
`Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` import is retained to preserve
the explicitly marked unit-route import. The new private proof imports
of the item are its two argument modules and `Mathlib.Algebra.Ring.Parity`.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The item's long docstring describes
an older ten-step plan, whereas the current DAG groups it into five steps. Both
use the same ordered-block and trace-symmetry arguments. The general regrouping
lemma requires coherent interval data; the actual `blockSourceIso`, equality-based
scheme transport and normalized exceptional compositor are not supplied as a
ready-made instance of those data. Likewise the symmetry lemma acts on its
coefficient-first compact-support trace, whereas the item concludes equality of
explicitly transported exceptional comparisons. The new statements isolate those
remaining geometric identifications rather than duplicate the already existing
general lemmas. They are the two separate argument groups allowed by step 4.

Edge cases checked in the statements and proof sketches: d=e=0 represents two
positive one-dimensional blocks; the arbitrary-invariance node includes one
coordinate and its identity permutation; empty bases, all positive coefficient
levels (including ramified levels) and arbitrary supplied etale antecedents are
retained. No nonempty-base, flat-coefficient-quotient, or unrestricted ambient
pro-etale adjunction hypothesis is introduced.

Three kinds of Mathlib search ran through msearch.py: LeanSearch, LeanFinder/Loogle,
and grep. They found generic affine/pullback and mate results, not the concrete
coordinate equations. Repository searches found only the item for blockComposite
and the purity transportedComparison. Blueprint searches found the parent
composition proposition and the already used general regrouping/symmetry nodes;
none of the new nodes is a duplicate of a complete existing declaration.

## New nodes

`def-pur-affine-comparison-coordinate-maps` records the existing coordinate and block
constructions moved verbatim to Maps; it introduces no new mathematical choice or
hole. It owns all the helper declarations formerly attached to the proposition.

`lem-pur-affine-comparison-ordered-blocks` records the ordered regrouping argument
in the actual coordinate system, using the existing general tower lemma and
canonical compact-support/pullback coherence. Its node and docstring explain the
interval construction, units, naturality, recursion identification and block cut.

`lem-pur-affine-comparison-coordinate-invariance` records the separate integration
and transpose argument for arbitrary coordinate permutations, using the existing
product-domain, projection, trace-factorization and symmetry declarations. Its
node and docstring identify the actual maps and explain the final Hom injectivity.

Change record: `coord/changes/A2-affine-purity-composition-coordinate-modules.md`.
No forced adaptation of another group's module occurs; no source-library module
is changed or withdrawn.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
