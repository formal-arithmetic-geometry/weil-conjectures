## What changed

Proved `AlgebraicGeometry.Scheme.Modules.coefficientUnit_isIso_of_isOpenImmersion`
in `Sheaf.AlgebraicGeometry.Cohomology.OpenImmersionCoefficientUnit` without changing
its signature. Added a proof-only import of
`WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit`.

The image/preimage adjunction on opens induces the abelian restriction adjunction.
Its unit is definitionally the forgotten module restriction unit. The canonical
left-adjoint uniqueness isomorphism and the forgotten module restriction/pullback
isomorphism compose to the coefficient unit: apply the abelian hom equivalence,
its right naturality, and `pullbackUnit_eq_of_isOpenImmersion` to prove that equality.
Both factors are isomorphisms. The DAG proof is updated to describe this realization.
The argument has no additional geometric hypotheses and applies also to empty
schemes, identity immersions and zero modules.

## Proved and sorry left

Closed the only hole:
`AlgebraicGeometry.Scheme.Modules.coefficientUnit_isIso_of_isOpenImmersion`
(`lem-pc-open-coefficient-unit-iso`). No holes added or split off. No sorry left
in the item's module. This is a proof, not a decomposition.

## No longer needed

No imports removed and no DAG nodes or modules pruned. The explicit
`Topology.IsOpenEmbedding.sheafPullbackIso` construction from the first planned
step is unnecessary: the abelian restriction adjunction gives the required
isomorphism directly by `Adjunction.leftAdjointUniq`. This is a shorter realization
of the same two steps. The unit record `sk-thm-picard-rr` is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The unit of the abelian restriction
adjunction agrees definitionally with the forgotten module restriction unit,
so an explicit computation with the sheafification-based `sheafPullbackIso` is
not needed. The original imported module was initially absent from the local
published compiled snapshot; the proof glue was checked in a sandbox scratch
file using the already compiled coefficient definition while awaiting publication.

Validation (second reading, 2026-10-13): the actual item compiled cleanly
with lcompile.py in 5.9 seconds. A scratch copy with #print axioms reported
exactly propext, Classical.choice and Quot.sound, with no sorryAx. The earlier
missing compiled dependency is now available. The identical sandbox copy of
InverseImageCoefficientComposition was removed from the delivery because it
changes nothing and the published compiled dependency is available.

## Second reading by K1

1. Compared both sandbox modules with their repository versions. The item has
   only a proof replacement and a plain proof-only PullbackUnit import; the
   existing theorem signature and docstring are byte-for-byte unchanged. The
   other module was identical and is excluded. No definitions or target
   statements changed; no change record is needed.
2. The item compiles without errors or warnings. No sorry, forbidden declaration,
   or hollow definition appears in it. A scratch #print axioms check gives only
   propext, Classical.choice and Quot.sound. Read the adjunct calculation: the
   restriction unit equality is checked componentwise by rfl; naturality and
   left-adjoint uniqueness give the exact coefficient morphism, and both
   comparison factors are isomorphisms. Verdict: genuine complete proof.
3. No new statements or split-off holes were added. Read the existing source
   pullbackUnit_eq_of_isOpenImmersion and coefficientUnit definition. They have
   precisely the generality used; identity and empty immersions and zero modules
   require no extra condition. Verdict: no deferred obligation to review.
4. Searched the library for coefficientUnit_isIso, leftAdjointUniq and
   sheafPullbackIso. No shorter complete coefficient-unit theorem was found.
   Both imports are needed: the public import supplies the statement's
   coefficientUnit; the plain import supplies the proven module unit comparison.
   The old proof_deps has only def-pc-flat-cohomology-comparison, still used.
   No nodes or modules are pruned. Read sk-thm-picard-rr's realized record;
   this auxiliary localization proof replaces no realized unit step.
5. Compared the node JSON: only proof and proof_origin changed; proof_deps
   remains the coefficient comparison definition. The two recorded steps
   match the restriction adjunction comparison and the adjunct calculation
   actually written in Lean. The module-unit identity comes from the existing
   source library and introduces no new DAG obligation. Verdict: metadata agrees.

Second-reading changes: removed the redundant unchanged dependency file from
this delivery, replaced obsolete pending-validation text with actual successful
compile and axiom results, and added this independent review. The Lean proof
and DAG update required no repair.
