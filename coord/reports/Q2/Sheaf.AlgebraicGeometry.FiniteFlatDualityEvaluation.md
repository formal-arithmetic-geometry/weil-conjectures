## What changed

Replaced the sole sorry in AlgebraicGeometry.finiteFlatDualityEvaluation with a compiling
reduction along the original route. Its signature, public imports, and docstring are unchanged.
Added three proof-only helper imports and Mathlib's degree-zero homology identification.
A documented local heartbeat setting permits elaboration of the derived comparison composition;
single-file compilation takes under 20 seconds.

The proof applies finite pushforward local freeness, supplies the derived restriction adjunction,
invokes finite_duality_derived_hom, and composes its isomorphisms. Finite locally free derived Hom
gives a degree-zero pushforward. Taking H0 of its comparison with R(aK) proves the Hom sheaf is
quasi-coherent; affine concentration then constructs quasi-coherent M and e0. The canonical
right-derived-unit comparison is constructed using a proved invertibility helper. After the
remaining counit/action compatibility, the final identity follows by b = 1 and mul_one.

Two new infrastructure modules have complete proofs: derived restriction's right adjoint follows
from the existing affine derived sheaf-Hom adjunction, exact scalar restriction, localization,
and adjunction transport. The canonical affine comparison follows from a bounded-below injective
resolution, the source-library Leray acyclicity theorem, and naturality of the unbounded unit.
Updated the target node's proof, proof dependencies, and proof origin to match this assembly.
No existing statement or definition changed; the unit record is untouched.

## Proved and sorry left

Closed the original sorry in AlgebraicGeometry.finiteFlatDualityEvaluation
(node lem-sc-finite-flat-duality-evaluation) by reduction to named dependencies.
This does not assert that its transitive dependencies are free of sorry.

Also proved AlgebraicGeometry.finiteRestriction_derived_rightAdjoint
(node lem-sc-finite-restriction-derived-right-adjoint) and
AlgebraicGeometry.affine_singlePushforward_unit_isIso
(node lem-sc-affine-single-pushforward-unit-iso). Neither has a direct sorry.

The only sorry in the delivery is AlgebraicGeometry.finiteDuality_degreeZero_counit_action
(node lem-sc-finite-duality-degree-zero-counit-action). It assumes the already constructed
quasi-coherent M, representation e0 and canonical c. It supplies the underived Hom isomorphism,
counit, evaluation at one, and action. It does not construct M/e0/c or assert the final identity.
Its proof is exactly by sorry, with a source and detailed proof in its declaration docstring.
The next worker must retain the canonical exact Hom model, rather than choose an arbitrary
derived-Hom isomorphism, to preserve evaluation and the algebra action.

## No longer needed

Second-reading import cleanup: FiniteRestrictionDerivedRightAdjoint no longer publicly
imports FiniteSheafHomAffineAdjoint (now a proof-only import) or SchemeDerivedDirectImage.
Its signature instead imports DirectImageAlgebraDerivedCategory and
RingedSpaceDerivedDirectImage, which supplies the ringed-space Grothendieck/K-injective
instances required to form rightDerivedFunctor in the public statement.
FiniteDualityDegreeZeroCounitAction no longer imports FiniteLocallyFreeDerivedHom;
its proposed exact-model proof uses dual tensor evaluation and tensor exactness instead.
These changes prune no original proof dependency or blueprint step.

None of the original imports or five planned dependencies is pruned. Each is used: Noetherian
finite presentation via Mathlib's instance, finite pushforward local freeness, finite derived
duality, finite locally free derived Hom, and affine concentration. The rejected core/tail
split is not reused or delivered. No existing module is claimed to become unreachable.

The source-library lem-weil-pbc-leray-acyclicity-quasi-iso is used as a proved generic tool
in the canonical affine comparison; bounded-below injective/K-injective results are Mathlib
tools. Localization's universal property is a generic tool in the proved restriction helper.
These do not replace a blueprint unit's step.

## Where the brief, the DAG or earlier work was wrong

The previous attempt merely repackaged existential clauses into undocumented circular sorries.
This delivery has no dependency on the item in any new node. The target actually invokes the
existing finite-duality, local-freeness, derived-Hom and affine-concentration declarations.
Two missing infrastructure steps are now proved rather than assumed. New nodes have complete
statements, proof steps, exact Lean signatures, sources, provenance and three kinds of search.
The target node records the actual route.

The original signatures leave real compatibility work: the ordinary derived-Hom isomorphism
has no evaluation normalization, and affine concentration only provides an unspecified
representation. The proved canonical-unit helper repairs the latter gap without changing a
statement. The remaining theorem isolates counit/action descent, using the action from the
underived affine sheaf-Hom adjunction. Empty schemes, rank zero, the empty open and zero
sections require no cancellation and are included.

LeanSearch returned Internal Server Error on the new queries; this is recorded as unavailable,
not a mathematical no-match. LeanFinder/Loogle and source grep completed, and candidate
signatures were checked. Stacks Tags 0AX2, 0AX3, 0FKW and 01XC were read online because
the local TeX sources are absent. No source or target statement correction is proposed.

## New nodes

lem-sc-finite-restriction-derived-right-adjoint, in
lean/Sheaf/AlgebraicGeometry/FiniteRestrictionDerivedRightAdjoint.lean, is proved from the
existing affine derived sheaf-Hom adjunction and exact scalar restriction. It supplies only
the auxiliary adjunction needed by finite_duality_derived_hom.

lem-sc-affine-single-pushforward-unit-iso, in
lean/Sheaf/AlgebraicGeometry/AffineSinglePushforwardUnitIso.lean, is proved by acyclic
resolution and unit naturality. It applies to arbitrary affine f and quasi-coherent M,
and specifies the actual unit composite.

lem-sc-finite-duality-degree-zero-counit-action, in
lean/Sheaf/AlgebraicGeometry/FiniteDualityDegreeZeroCounitAction.lean, is the remaining
intermediate theorem. It descends the canonical counit and algebra action after M/e0/c
have been constructed. No change record is required.

## Second reading by Q2

1. Compared all four modules with the repository. Only FiniteFlatDualityEvaluation
   already exists there. Its theorem signature is byte-for-byte identical, its
   existing docstring is unchanged, and all added imports are proof-only. The
   three helper declarations are new. No definition or existing statement changed;
   no change record is needed. Verdict: pass.
2. Compiled the complete set locally in import order. Scanned all delivered Lean
   for forbidden declarations, attributes and kernel-check shortcuts: none. The
   only direct sorry is finiteDuality_degreeZero_counit_action, exactly by sorry.
   A scratch axiom audit of all four declarations reports only propext,
   Classical.choice, Quot.sound and sorryAx. The latter remains in upstream
   dependencies even for the two infrastructure proofs; this is a reduction,
   not a claim of transitive sorry-freedom. Verdict: pass.
3. Read each helper and its node. Derived restriction is transported from the
   existing adjunction through localization and the exact-functor comparison.
   The affine unit proof uses an acyclic injective resolution and cancels only
   isomorphisms. For the open compatibility lemma, checked identity morphisms,
   zero sections, rank-zero algebra and the empty open. On affine charts its
   canonical pairing is (omega,b) -> epsilon(b omega); uniqueness of right
   adjoints makes that pairing perfect, and commutativity gives its action law.
   Arbitrary choices of e0 are transported by this pairing, not assumed normalized.
   Its hypotheses already provide M/e0/c, so it is strictly the counit/action
   part of the item, not a restatement of the existential degree-zero construction.
   Repeated LeanFinder searches for acyclic derived units and scalar coinduction
   evaluation, Loogle for adjunction transport, and rg across Mathlib, upstream
   and Sheaf. Checked the returned module coextension counit: it is an underived
   ring-module result, not this sheaf/derived compatibility. The upstream acyclic
   unit theorem concerns the bounded-below derived category, not the specified
   unbounded unit. No duplicate or quick closure was found. Verdict: pass; the
   remaining compatibility still needs a substantial Lean proof.
4. Read the assembly from its conclusion backwards: the final identity is
   hlin at b=1; counit/action compatibility is used only after local freeness,
   finite derived duality, degree-zero Hom, H0 quasi-coherence, affine concentration
   and invertibility of the actual unit have constructed the witnesses. Every
   original proof dependency is used, so no original node is pruned. The
   sk-thm-picard-duality unit and its realized record are untouched. All new
   helper modules stay below that unit's route. Corrected the publicly exposed
   proof import and removed the unused derived-Hom import described above.
   Other imports of the open lemma record its documented proof plan. Verdict: pass.
5. Checked all four node Lean signatures against whitespace-normalized source
   signatures; all match. Each proof_deps equals the union of its proof steps'
   uses, and every referenced node exists. The target node records the actual
   reduction; new nodes have sources, provenance, search records, blueprint
   origins and complete Lean records. Verdict: pass.

Changed only the helper imports and this report. The original theorem proof,
all signatures, all node records and the unit route are retained.
