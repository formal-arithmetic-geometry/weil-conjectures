## What changed

Repaired the returned duplicate statements in RawAffineComplexSystemMapCoherence.
Removed private idFactors, compFactors, unitLeray_naturality and
complex_pullback_laws, and imported
Sheaf.Paper.DerivedEtaleCohomologyPullbackLaws as a proof-only dependency.
The coherence theorem now uses its public
AlgebraicGeometry.Etale.derivedEtaleCohomology_pullback_laws directly.
It requests bounded-below stage complexes and a bounded-below cocone vertex.
The remaining coefficient theorem now records hbelowL: its constructed vertex
is a degree-zero single complex and therefore vanishes in negative degrees.
Both modified helper modules and their nodes are NEW relative to the library.
No existing library signature or visibility changed.

RestrictedAffineComplexSystem packages these bounds using
CochainComplex.isStrictlyGE_iff, then constructs the cohomology functor T and
cocone B from the proved identity, composition and cone-leg equations.
The final element equality evaluates the coefficient morphism equality.
The original item's signature, docstring and public visibility are unchanged.
Its scoped unusedVariables setting covers unused existential proof witnesses
in that unchanged statement. All three modules compile without warnings.

## Proved and sorry left

Closed one original hole:
AlgebraicGeometry.Etale.exists_restricted_affine_complex_system
(lem-sbc-restricted-affine-complex-system).

Added one strictly smaller named hole:
AlgebraicGeometry.Etale.exists_restricted_affine_coefficient_system
(lem-sbc-restricted-affine-coefficient-system), exactly := by sorry.
It supplies geometry, coefficient single complexes, their colimit and restriction
comparisons, including the negative-degree vanishing of the vertex. It supplies
neither T nor B. This is a decomposition: one hole closed and one added, net zero.
No sorry remains in the original module.

Also proved AlgebraicGeometry.Etale.rawAffineComplex_system_map_coherence
(lem-sbc-raw-affine-complex-system-map-coherence), with no new hole.
Its pullback laws come from the existing public theorem; all local helpers are
proved. No public data is chosen from an arbitrary unproved existence witness.

## No longer needed

Removed original proof-only imports:
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction,
WeilConjectures.SixFunctors.Etale.Derived.LowerShriek,
WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs.
The latter two remain transitively available through the retained public import
Sheaf.AlgebraicGeometry.RawAffineRestrictedCohomology.

The coherence module no longer directly imports
Sheaf.Paper.DerivedUnitLerayId or Sheaf.Paper.DerivedUnitLerayComp.
They remain dependencies of the existing public pullback-law theorem, so are
not claimed pruned from the targets' closure. Its direct proof edges to
lem-weil-pbc-derived-unit-leray-id, lem-weil-pbc-derived-unit-leray-comp and
lem-weil-pbc-exact-functor-derived-factorization are replaced by
lem-weil-pbc-derived-cohomology-pullback-laws.

The original node's direct proof edges to def-weil-pbc-inverse-image,
lem-weil-pbc-inverse-image-composition, def-pc-fibre-product,
def-weil-pbc-etale-cohomology, prop-weil-pbc-derived-inverse-image-adjunction
and def-sbc-raw-affine-restricted-cohomology are replaced by the two precise
new nodes. These foundational objects remain used below; no whole blueprint
unit or globally unreachable module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The returned version duplicated two private factorization lemmas from
DerivedEtaleCohomologyPullbackLaws. Private visibility did not justify that
duplication: the required construction uses degree-zero single complexes, so
the existing bounded-below public theorem suffices. The repair removes those
duplicates rather than renaming them, and removes the other copied calculations.
The earlier claim that arbitrary-complex generality was needed is withdrawn.

The coefficient step's vertex is a single complex too; recording its bound
lets the cone-leg composition apply the existing theorem. This does not
strengthen the original item or introduce any additional hole. The new helper
nodes and proof routes now match the repaired Lean signatures and proof.
The previous second reading was for the rejected version and must be repeated.

The original dependency list did not contain a theorem constructing all the
restricted geometric and coefficient witnesses; the one remaining named hole
records that part with source and complete proof in words. Previously recorded
searches are in searches.jsonl. LeanSearch was unavailable, not a negative match.
The unit sk-lem-failure-field has empty realized lists; its higher-direct-image
limit route remains intact. Edge cases: singleton index, empty schemes, zero
coefficients and p=0 remain permitted. Bounds follow from degree-zero single
complexes in all these cases. The coherence theorem permits empty J and every
integer degree; the vertex bound is explicitly assumed even for empty J.

## New nodes

lem-sbc-restricted-affine-coefficient-system:
lean/Sheaf/AlgebraicGeometry/RestrictedAffineCoefficientSystem.lean.
One remaining geometric/coefficient construction theorem, now explicitly
recording negative-degree vertex vanishing. It omits the cohomology diagram and
cocone constructed by the original module.

lem-sbc-raw-affine-complex-system-map-coherence:
lean/Sheaf/AlgebraicGeometry/RawAffineComplexSystemMapCoherence.lean.
A proved identity/composition/cone-leg theorem for given bounded-below stage
complexes and cocone vertex, using the existing public pullback laws. It asserts
no geometric existence, coefficient colimit or cohomology continuity.

Updated the original node's proof, proof_deps and proof_origin. No existing
statement, definition or public interface changed; no forced adaptations or
change records are required.

## Second reading by Q1

1. PASS. Diffed the delivered original module against the read-only repository:
   its existing theorem signature is byte-for-byte identical, its docstring and
   public visibility are unchanged, and its only other changes are proof-only
   imports and a scoped unused-variable linter option. Both helper modules and
   their nodes are absent from the repository. No definition or target changed.
2. PASS as a decomposition. Compiled all three modules locally in import order
   with lcompile.py: no errors or warnings. Searched every delivered Lean file
   for forbidden declarations and sorry: the sole hole is the reported named
   coefficient theorem. A scratch axiom probe returned propext, Classical.choice
   and Quot.sound for rawAffineComplex_system_map_coherence, and those plus
   sorryAx for both existence theorems. The original proof destructs existence
   inside a theorem of Prop; no definition selects an arbitrary witness.
3. PASS. Read the coefficient statement, its complete construction docstring,
   node, and the definitions of the canonical restricted maps. Checked the
   construction for a singleton index, empty schemes, zero coefficients and
   degree zero: pullbacks and degree-zero single complexes still supply the
   stated objects; mapping the coefficient colimit by inverse image and single
   preserves the colimit and negative-degree vanishing. The remaining theorem
   omits the cohomology functor, cocone and their laws, which the original module
   genuinely constructs, so it is a strictly smaller construction obligation.
   No short proof of that geometric/coefficient construction was found.
   Independent searches used leanfinder for inverse-image base-change diagrams
   with single complexes and colimits, loogle for CochainComplex.singleFunctor,
   and grep for rawAffineRestricted, mapCochainComplexSingleFunctor and colimits.
   The results provide components, not this construction. Read Mathlib's
   HomologicalComplexLimits single-functor colimit instance and the single
   functor's lower-bound instance. Also searched lean/Sheaf and upstream Lean;
   AffineEtaleBaseChangeSystem concerns diagrams of etale sites, and the
   pro-etale pullbackPresentationCone concerns a specific presentation, so
   neither supplies the coefficient theorem. Read the cited sources at
   https://stacks.math.columbia.edu/tag/09Z1 and
   https://stacks.math.columbia.edu/tag/0EZM: the construction is their
   restricted-scheme/coefficient setup, with no continuity conclusion assumed.
4. PASS. Read the proof downward: it uses the coefficient construction,
   packages the supplied bounds, applies the existing derived pullback laws
   through the coherence theorem, and constructs T and B explicitly. The
   coherence calculation uses coefficient cocone naturality and cancellation
   of eG; its empty-category case is vacuous, and it permits every integer
   degree with the vertex bound explicitly supplied. Imports are needed for
   signatures or the actual proofs, with proof-only dependencies private.
   No longer needed lists all six removed original proof edges and three
   original imports, and correctly avoids claiming global module pruning.
   Read dag/units/sk-lem-failure-field.json: its realized statement and step
   lists are empty; no realized unit node is bypassed by this reduction.
5. PASS. Diffed the original node: only proof, proof_deps and proof_origin
   change. Read both new nodes, their sources, searches, creation provenance,
   blueprint ancestry and Lean records. Their lean.statement fields match
   their Lean signatures verbatim; the original node retains its existing
   statement record. Proof dependencies are exactly the unions of the cited
   steps and match the construction/coherence reduction written in Lean.

Second reading changed only this report, adding the independent review and
validation evidence. No Lean repair was needed. One original hole closed and
one strictly smaller hole added remains a net-zero decomposition; the new
coherence theorem is proved without sorryAx. No globally unreachable module
is claimed pruned. Scratch axiom probes were removed from delivery sources.
