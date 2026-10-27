## What changed

Completed the assigned retirement repair from coord/retire-items.tsv. Withdrew
lean/Sheaf/AlgebraicGeometry/RawModuleScalarSheafComposition.lean through deleted.txt
and repointed lem-sbc-raw-scalar-sheaf-composition to the existing proved theorem
AlgebraicGeometry.Etale.rawModuleScalar_sheaf_composition in
WeilConjectures.AlgebraicGeometry.RawModuleScalarSheafComposition. Only the node's
lean field changes. Its natural-language statement, proof, dependencies, source,
blueprint references and unit binding remain intact.

The old scalar-forgetting functor RawModuleScalarComparison.forget is an abbreviation
of moduleAbelianForget. Thus the upstream theorem has exactly the required type by
definitional equality, with the same universes, commutative-ring hypothesis, four
scheme arrows/equality binders and arbitrary module sheaf. This also covers the zero
ring, zero sheaf and identity arrows. No target statement, definition or source-library
file is changed. There are no consumer adaptations.

The canonical proof applies the composite inverse-image adjunction's injective Hom
equivalence and uses the upperStarComp unit equation, naturality of lowerStarComp,
naturality of the a-unit and the scalar comparison's defining unit equation. The
upstream implementation supplies that same complete proof. The stage-3 dependency
nodes already name the canonical scalar comparison and the inverse-image composition
API, so no replacement intermediate statements are required.

Validation: the original item compiled through lcompile.py in 8.2 seconds. A scratch
compatibility proof applies the upstream theorem to the former signature verbatim;
it compiled in 5.1 seconds. Both the canonical theorem and this compatibility
proof have exactly the permitted axioms propext, Classical.choice and Quot.sound.
After expanding the abbreviation, the local private helper and public theorem
(signature and full proof) match the upstream text byte for byte. The exact
import scan of lean/Sheaf, lean/WeilConjectures and quarantine/ finds zero imports of
the retired Sheaf path. tools/downstream.py agrees: zero direct importers and zero
external uses of its private scalar_unit helper. All three historically listed
Sheaf consumers were compiled unchanged: RawModuleScalarCoefficientUnshifted in
10.2 seconds, RawModuleScalarSourceClassFormula in 9.7 seconds and the already
withdrawn RawModuleScalarSourceSquare in 1.1 seconds. All passed without warnings.

Searches were actually run through msearch.py: LeanFinder for scalar forgetting and
inverse-image composition returned eight general sheaf/module hits, not the precise
etale identity; Loogle found CategoryTheory.Adjunction.homEquiv_unit; grep for
rawModuleScalar_sheaf_composition returned no indexed hit. Direct local rg located
the exact canonical theorem and its two upstream proof consumers.

Change record: coord/changes/J1-retire-raw-module-scalar-sheaf-composition.md.

## Proved and sorry left

This is a retirement repair with zero original holes. Holes closed: none. Holes
added: none. Holes left in the item: none. No split-off declarations or new nodes.
AlgebraicGeometry.Etale.rawModuleScalar_sheaf_composition was already proved in both
copies; the upstream proof is retained, not counted as a new hole closure. The
private scalar_unit duplicate is retired with the Sheaf file.

## No longer needed

Retired module: Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition. Its public
import of Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso disappears with
the duplicate file. The latter module remains needed elsewhere and is not withdrawn.
No mathematical node or dependency is pruned: lem-sbc-raw-scalar-sheaf-composition,
def-sbc-raw-module-scalar-pullback-comparison and
lem-weil-pbc-inverse-image-composition all stay. The retired copy is the only module
this packet prunes.

The DAG parents lem-sbc-raw-scalar-coefficient-unshifted,
lem-sbc-raw-module-scalar-source-class-formula and lem-sbc-raw-scalar-source-square
continue to cite the same composition node, now attached upstream. The first two
already attach to upstream proofs importing the canonical composition theorem.
The Sheaf source-square module was previously withdrawn; this delivery does not
remove its DAG node or dependencies. No realized unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open proof chain. The current queue identifies
this particular assignment as a retirement repair, and the present item contains zero
sorries. The old retirement row lists three Sheaf consumers, but the current coefficient
and source-class files already use the adopted upstream implementations, and the source
square file is already an empty withdrawn module. Its reported missing pullback_unit_hom
helper is absent from the present copy and has no current uses. The private scalar_unit
helper has no external use either. These historical entries therefore require no
consumer patch. The current DAG attachment was still local; this packet corrects it
while preserving all mathematical parent references and the unit route.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
