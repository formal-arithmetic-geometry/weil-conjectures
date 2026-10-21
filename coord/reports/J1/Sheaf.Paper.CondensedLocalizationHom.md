## What changed

Proof-only partial delivery of `lean/Sheaf/Paper/CondensedLocalizationHom.lean`.
The coefficient localization map now preserves the original internal ring structure.
After applying the lax monoidal sheaf-to-presheaf functor, the target unit and
multiplication are identified with the sectionwise operations using
`Sheaf.ε_comp_map_one` and `Sheaf.μ_comp_map_mul`. The unit identity follows from
additivity on the integer tensor unit and preservation of one by the actual
localization ring homomorphism. The multiplication identity follows on pure
tensors from preservation of multiplication. `Sheaf.isMonHom_of_isMonHom_map`
then reflects these identities back to sheaves.

The scalar-map existence and uniqueness theorem is now proved by applying the
existing monoid-valued presheaf equivalence, evaluating at the terminal profinite
space, and applying `InternalAbelianSheafModule.monToRing`. The resulting ring
homomorphism has exactly the required underlying additive map; `RingHom.ext`
proves uniqueness.

The module's signatures, definitions, attributes, documentation and imports are
unchanged. No dependency module was modified. The remaining main theorem retains
its existing statement and proof plan.

## Proved and sorry left

Closed two of the three original holes:

- `AlgebraicGeometry.ProEtale.CondensedLocalization.coefficientLocalizationMap_isMonHom`.
- `AlgebraicGeometry.ProEtale.CondensedLocalization.scalarRingMap_existsUnique`.

Both belong to node `lem-pod-condensed-localization-hom`. Both compile, and
explicit `#print axioms` checks report exactly `propext`, `Classical.choice` and
`Quot.sound`, without any dependency on an unproved theorem.

One original hole remains, unchanged:

- `AlgebraicGeometry.ProEtale.CondensedLocalization.condensed_localization_hom`
  (node `lem-pod-condensed-localization-hom`).

No holes were added or split off. The module with both completed proofs and the
axiom probes compiled cleanly through `lcompile.py` in 32.3 seconds. The delivery
performs its own module compilation and preflight.

## No longer needed

None. The main theorem's telescope, boundedness, Hom-continuity, coefficient
adjunction, tensor, and restriction dependencies remain needed by its unchanged
proof plan. No import, node or module is withdrawn or claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The two foundational holes require no new theory:
the existing monoidal sheaf-to-presheaf reflection and section-ring construction
already supply the needed unit, multiplication and evaluation machinery.

Searches used `msearch.py` with LeanFinder, Loogle and grep, followed by direct
inspection of `RingObjects.RingPresheaf`, `Sites.MonObj`, and
`InternalAbelianSheafModuleEquivalence`. For the remaining main theorem, the
existing scalar-localization derived-Hom theorem is stated for sectionwise
module sheaves; applying it here still requires the internal-module equivalence
and compatibility with the specified central actions and normalized derived
comparisons. No replacement statement or unproved transport lemma is introduced.

Several compile attempts received the server-busy response; a subsequent compile
of the exact delivered source with the two axiom probes succeeded.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
