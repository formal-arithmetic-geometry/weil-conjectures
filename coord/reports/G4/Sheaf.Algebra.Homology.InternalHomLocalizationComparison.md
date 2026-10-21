## What changed

Filled the proof script of CategoryTheory.internalHom_localization_comparison in
Sheaf.Algebra.Homology.InternalHomLocalizationComparison. The five public
definitions and the complete theorem signature remain verbatim. All added helpers
are private. No imported module, public definition, target, consumer or upstream
source declaration changed. No new module or node was needed. The command-scope
record is coord/changes/internal-hom-localization-proof-scope.md; it documents
proof-only local attributes, notation and variables required by preflight.

The proof constructs the scalar module colimit degreewise, identifies its target
with restricted ordinary extension, and checks the zeroth leg against the unit.
Exact tensor localization and reflection through fully faithful restriction prove
ordinary extension exact. Localizing that ordinary adjunction and comparing left
adjoints identifies the recorded derived extension, with the correct unit.
Exactness also makes restriction preserve K-injectives; the existing right-derived
fully-faithful theorem then supplies the fullness needed for unit uniqueness.

For the Hom towers, augmentation naturality gives equality of the two scalar
transitions after Q. Naturality of the ordinary Hom comparison, invertible at
K-injective targets, transports this equality through Hom. Comparing the two
existing distinguished telescope triangles gives an isomorphism preserving every
colimit leg. The continuity hypothesis and resolution comparison then produce the
unit-normalized isomorphism. Evaluation normalization identifies the actual
comparison by uniqueness; naturality transports it from a bounded-below complex
to L and gives the two-variable square.

Proof-only imports reuse the existing private interfaces in
LocalizationInverseImageCoherence, RingedInternalHomShiftOfUniverses,
ScalarHomTensorCancellation, ScalarHomOrdinaryTensorComparison and
ClosedScalarHomComparison. The other added proof imports supply K-injectives,
right-derived full faithfulness, localization of adjunctions and telescope
triangles. The node's proof, proof_deps and proof_origin now describe this route.
Only the two obsolete tool_uses entries identified below are removed; other live
metadata is retained.

Verification: the complete module compiled successfully through lcompile.py in
23.0 seconds, with exit code 0 and no errors or warnings. All diagnostic cutoffs
and print commands are removed. Earlier requests intermittently returned busy
exit 124; the 10:53 UTC delivery attempt explicitly pushed nothing. The required
delivery command now runs its compile and preflight before pushing.

An axiom query before the final correction reported propext, Classical.choice,
Quot.sound and sorryAx. Existing imported project holes remain, including the
SiteTensorFunctoriality interfaces; the delivery does not claim the transitive
dependency closure is free of sorryAx. The item's own proof and all added private
helpers have no holes.

## Proved and sorry left

Closed in this packet: CategoryTheory.internalHom_localization_comparison
(node lem-sfb-internal-hom-localization-comparison), from existing declarations.
Original holes: one. Item holes left: zero. Holes added elsewhere: zero.
Split-off statements: zero. All private helpers have complete proofs.
The complete module compiled successfully in 23.0 seconds. Existing imported
theorem holes are not changed; this is not a claim that the dependency closure is
free of sorryAx.

## No longer needed

Removed proof imports:

- Sheaf.CategoryTheory.ScalarLocalizationSheafExact: extension exactness follows
  from the proved tensor-localization exactness and reflection through restriction.
- Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore: assemble the already proved
  independent-universe module cocones degreewise instead.

Relative to the current shared node, removed direct proof dependencies:

- lem-sfb-derived-scalar-localization-reflection: prove the needed exactness,
  derived fullness and injectivity from existing declarations. The broader
  reflection and counit API is unnecessary.
- lem-sfb-kinjective-hom-scalar-telescope: naturality identifies the diagrams after
  Q, and a comparison of distinguished telescope triangles preserves every leg.
  A chosen chain homotopy is unnecessary.
- lem-weil-pbc-scalar-localization-complex-colimit: its coefficient-universe
  specialization is replaced by the independent-universe degreewise construction.

Removed obsolete top-level tool_uses entries
lem-weil-pbc-scalar-localization-sheaf-exact and
lem-weil-pbc-scalar-localization-complex-colimit for the reasons above. No approval
was added or reordered. The historical direct K-injective homotopy/cone dependencies
are likewise unnecessary for this route. The derived change-of-rings statement
dependency and public import remain; its theorem is not used to prove exactness.

No existing module or declaration is withdrawn. Other consumers, quarantined
parents and unit routes retain their nodes and dependencies. The new statement-only
reflection and telescope nodes are not statements realized by this item's unit.

## Where the brief, the DAG or earlier work was wrong

The complex-colimit interface identifies the site object, morphism and coefficient
universes, whereas this item keeps them independent. The existing module colimit
in LocalizationInverseImageCoherence has the required universes and suffices.
The scalar exactness interface uses changeOfRingsOfUniverses whereas the recorded
pair uses changeOfRings. Reflection from exact tensor localization avoids changing
either interface.

During this session the shared DAG was re-split to cite
lem-sfb-derived-scalar-localization-reflection and
lem-sfb-kinjective-hom-scalar-telescope. Both currently have lean: null. They were
not redeclared: the proof uses existing declarations instead. The delivered node
copy retains current shared metadata while replacing the proof route. The unit's
own statements and route are preserved.

The prior attempt's missing Mathlib artifact was not reproduced. Busy/no-answer
responses were retried until actual Lean diagnostics were available. No launcher,
budget, shared source or build configuration was edited.

The latest preflight refusal required a command-scope change record and
identified a private-named but globally registered additive instance. Nothing was
pushed. The instance is now a proved private theorem registered explicitly with
`attribute [local instance]`; the record documents all local commands and the
read-only downstream check (zero current Lean importers). Public interfaces are
unchanged.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
