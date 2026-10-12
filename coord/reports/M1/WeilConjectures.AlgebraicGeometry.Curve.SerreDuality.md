## What changed

Removed the sole direct sorry in WeilConjectures.AlgebraicGeometry.Curve.SerreDuality:
AlgebraicGeometry.Scheme.exists_isIso_pushforwardHomObjComparison_unit.
Added proof-only imports of FiniteFlatDualityEvaluation,
NoetherianDerivedDirectImageRightAdjoint, and SmoothCurveUpperShriekDifferentials.
The initially added FullyFaithful imports were removed during second reading.
Existing signatures, docstrings, and public imports are unchanged.
Updated lem-sc-finite-duality-trace to follow the actual Lean proof.

Added Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials, with a complete
proof from the existing smooth proper dualizing, upper-shriek composition,
ringed-space derived composition, and Noetherian adjoint-existence declarations.
Private proved helpers establish quasi-coherence of single complexes and stability
of D_QCoh under isomorphisms and shifts. The proof chooses adjoints for the structure
maps, applies the two smooth-curve dualizing identifications, lifts them through
full-subcategory inclusions, transfers shift compatibility to the supplied right
adjoint, composes the isomorphisms, and cancels the common shift by one.

The original trace theorem applies finite flat evaluation, descends the resulting
degree-zero isomorphism using full faithfulness of single complexes, and transports
the trace. Its comparison is proved equal to the composite isomorphism on every
section and every smaller open. Linearity, restriction naturality, evaluation at 1,
and the scalar-evaluation identity are used explicitly. All delivery modules compile
without warnings; no direct sorry remains in either module.

## Proved and sorry left

Proved from named existing declarations:
AlgebraicGeometry.Scheme.exists_isIso_pushforwardHomObjComparison_unit
(lem-sc-finite-duality-trace), and
AlgebraicGeometry.smoothCurve_upperShriek_differentials
(lem-sc-smooth-curve-upper-shriek-differentials).
The item's module now has no direct sorry. The new module also has no direct sorry.
No sorry was split off or added. The existing final Serre duality proofs and every
other proof of the source module remain intact.

The proofs still rely on the already-stated, still-sorried declarations
AlgebraicGeometry.finiteFlatDualityEvaluation
(lem-sc-finite-flat-duality-evaluation),
AlgebraicGeometry.noetherian_schemeDerivedDirectImage_has_rightAdjoint
(lem-pc-noetherian-derived-direct-image-right-adjoint),
AlgebraicGeometry.smoothProperCurve_dualizing
(lem-sc-smooth-proper-curve-dualizing),
AlgebraicGeometry.exists_properUpperShriekComposition
(lem-sc-proper-upper-shriek-composition), and
AlgebraicGeometry.RingedSpace.exists_derivedModuleDirectImageComposition
(lem-pc-ringed-spaces-derived-direct-image-composition), and their dependencies.
These retain their existing nodes and modules; they were used, not restated.
This delivery is a complete reduction to them, not a claim of transitive axiom closure.

## No longer needed

Removed the redundant proof-only import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
from both delivered modules after compiling scratch copies without it. Its single-complex
homology and full-faithfulness declarations are already available transitively.
Also removed the redundant proof-only import
Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition from the new module: its
composition theorem is already exposed by ProperUpperShriekComposition. A scratch compile
confirmed this removal. All three remaining added source-module proof imports are used.
lem-sc-smooth-proper-curve-dualizing and lem-sc-proper-upper-shriek-composition
are no longer direct proof dependencies of lem-sc-finite-duality-trace; both remain
prerequisites through the new, proved differential-identification node.
def-sc-p1-standard is no longer listed as a direct proof dependency of the trace
node: the standard projective line is already its statement dependency, which is
retained. Its module is not globally pruned. No claim is made that any other module
has become unreachable from the targets.

## Where the brief, the DAG or earlier work was wrong

The plan's shift cancellation was not exposed as a single Lean declaration.
It is now implemented, including D_QCoh stability under shifts and the shift
comparison of the supplied right adjoint. No statement or definition needed repair.

The existing upper-shriek composition theorem requires a composition isomorphism
on the entire derived category and its right-derived-unit compatibility, whereas
ProperDerivedDirectImageComposition supplies a comparison only after restricting
to D_QCoh. The existing RingedSpaceDerivedDirectImageComposition gives exactly the
required full-category comparison and compatibility. It is used as a generic
composition tool, with no change to the finite-duality route or the unit's argument.

Sources read: Stacks Tags 0BRT, 0ATX and 0BVI on the official website; the local
checkout has literature lists but not the cited TeX files. The new statement is
about proper maps between smooth proper curves and assumes neither finite flatness
nor connectedness, integrality, algebraic closedness, or separability. Its use in
the trace theorem is legitimate because a finite map to the proper projective line
makes X proper. Checked identity maps, finite etale covers, characteristic-p
Frobenius (no division by ramification index or field trace), empty curves, and a
constant proper map between curves. Both structure maps have relative dimension one,
so their dualizing shifts cancel even for a constant f.

Searches: LeanFinder found smooth/flat ring lemmas, not geometric duality;
Loogle/source search supplied fully faithful single complexes and adjoint shift
compatibility as categorical tools. LeanSearch returned Internal Server Error and
is recorded as unavailable without an absence verdict. Project-library, DAG, and
blueprint searches found no duplicate of the new differential-identification
statement. Existing declarations were sufficient once the shift machinery was
transported explicitly. The axiom probe allows the existing transitive sorry
assumptions and detected no additional nonstandard axiom.

## New nodes

lem-sc-smooth-curve-upper-shriek-differentials: a proved intermediate theorem carrying
step two of lem-sc-finite-duality-trace, inherited from lem-sc-finite-duality in the
Picard duality unit. Its source, full proof in words, actual dependencies, and
matching Lean signature are recorded. It is strictly the differential-identification
part of the argument, without a trace or Hom comparison. No new unproved node was
created. No statement or definition was changed; no change record is needed.


## Second reading by M1

1. Compared both delivered modules against the read-only repository. The existing
   SerreDuality module differs only in three proof-only imports and the body of
   exists_isIso_pushforwardHomObjComparison_unit. All existing signatures,
   definitions, docstrings, public imports, and other proofs are byte-for-byte
   unchanged. The other delivered module is new. No change record is required.
2. Compiled both modules locally in import order with the required lcompile.py:
   no errors or warnings and no direct sorry in either module. Scanned for forbidden
   declarations and kernel bypasses: none. Explicit #print axioms probes of the trace
   theorem, the new intermediate theorem, and both final Serre-duality isomorphisms
   show only propext, Classical.choice, Quot.sound, and the existing transitive
   sorryAx. This is a reduction to the previously stated open dependencies, not
   transitive axiom closure.
3. No unproved statement is split off. Read the new differential-identification
   statement, its docstring proof, and its matching node. It is strictly the
   differential-identification step, with no Hom comparison or trace conclusion.
   Checked identity maps, empty source, disconnected curves, constant proper maps,
   finite etale covers, and Frobenius: proper composition of the two curve structure
   maps and cancellation of the same shift applies in every case; no separability
   or nonconstant hypothesis is needed. Rechecked the sources at
   https://stacks.math.columbia.edu/tag/0BRT and
   https://stacks.math.columbia.edu/tag/0ATX. Independent LeanFinder search for
   "proper pushforward right adjoint sends canonical bundle to canonical bundle
   smooth curves" returned ordinary pullback/pushforward adjunction tools, not
   this statement. Loogle search for DerivedCategory.singleFunctor and source
   searches for canonical adjoints and differential/upper-shriek identifications
   found no shorter geometric proof or duplicate. The new statement has its
   source, full proof, creation record, blueprint origin, and Lean record.
4. Read the full SerreDuality module and the actual imported duality statements.
   The proof descends the degree-zero isomorphism by full faithfulness, transports
   finite-flat evaluation, and proves the comparison equality on every section
   and every smaller open. The new theorem establishes quasi-coherence and shift
   stability before transferring shift compatibility through comparison and
   adjunction, so cancellation is justified. Removed the redundant FullyFaithful proof import from both modules; their
   single-complex homology/full-faithfulness lemmas remain available transitively.
   Also removed the new module's redundant RingedSpaceDerivedDirectImageComposition
   import, compiling without it; ProperUpperShriekComposition already exposes it.
   Completed No longer needed with every old direct proof dependency removed:
   def-sc-p1-standard (still a statement dependency),
   lem-sc-smooth-proper-curve-dualizing and
   lem-sc-proper-upper-shriek-composition (now used through the intermediate).
   No mathematical route or globally reachable module is pruned. The unit's
   finite-map/projective-line route and its downstream Serre-duality assembly are
   retained. dag/units/sk-thm-picard-duality.json has empty realized fields already
   in the repository; this inherited bookkeeping gap is reported here, and no
   unit record is modified by this proof delivery.
5. Compared the existing node diff: only proof, proof_deps, and proof_origin
   changed. Checked both nodes' proof steps and dependency unions against the
   Lean calls and inferred geometric instances. The new node's statement matches
   its Lean theorem, with arbitrary chosen derived-category morphism universes.
   Ringed-space derived composition supplies exactly the full-category comparison
   and unit compatibility required by the existing upper-shriek composition
   theorem. Verdict: the node records agree with the proved reduction.

Second reading removed redundant proof imports and completed the
report's pruning/dependency accounting; the mathematical proofs were retained.
