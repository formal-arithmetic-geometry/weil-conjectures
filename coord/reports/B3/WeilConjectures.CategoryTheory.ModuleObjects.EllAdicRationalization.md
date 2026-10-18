## What changed

The module `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`
proves `AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars`
from the existing continuous-coefficient integral-model, denominator-clearing,
complex-telescope, derived-unit and sheaf-Hom continuity declarations. Every existing
target signature is unchanged. All pre-existing public statements and
non-theorem bodies are restored verbatim. Added proof imports are private.
Local instances `moduleTensorLeft_smallColimits`,
`moduleTensorRight_smallColimits`, `moduleTensorLeft_preservesColimit` and
`moduleTensorRight_preservesColimit` cache standard colimit preservation of tensor
functors. These instances are proof-valued and change no coefficient data.
The integral triangulation instance has a higher local search priority. These
instances prevent repeated expensive graded-tensor typeclass searches in
the existing derived-functor signatures. The proved integral triangulated instance
is supplied locally in the localization proof.

The criterion application is proved with the continuous-coefficient APIs in
`continuousScalar_isLocalization`, and specialized once to the fixed subfield.
A proved `integralScalarExtension_additive` helper supplies additivity before
specialization. An explicit functor equality identifies the concrete and continuous
constructions. This avoids repeated conversion of the finite-subfield coefficient
presentation.
The categorical glue constructs the factor through rationalization, proves it full
by clearing denominators, faithful by eventual scalar equality, and essentially
surjective using integral models. Its proof that torsion-cone morphisms are inverted
uses left and right inverses up to scalars and triangle exactness. For eventual equality,
the proof uses the shifted-Hom continuity part of the existing bounded devissage
argument, then equality of representatives in a filtered colimit of abelian groups.
The telescope transition is computed explicitly as a power of ell.

The localization node's proof, proof dependencies and proof origin follow these
implementations. Its statement and its unit are unchanged. The integral-model
implementation uses the unit's integral-generators/cones/bounded-truncations route.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars`
(node `thm-sfb-extend-scalars-localization`), the module's one original hole.
Added holes: none. Remaining holes in delivered files: none.
The complete file, with the original upstream public API, compiled through
`lcompile.py` in 33.0 seconds with no warnings. This is a proof from
existing declared dependencies, some of which retain their previously registered
holes, rather than a claim that the full dependency closure is axiom-free.

## No longer needed

No original public import is removed. No module is withdrawn. The following nodes
are removed from this node's `proof_deps`; some remain transitive inputs of the
reused library proofs or definitions in `stmt_deps`. This is dependency pruning,
not a claim that their modules are globally unreachable:

- `def-weil-closed-immersion`
- `def-weil-open-immersion`
- `def-weil-pbc-condensed-e-module-category`
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `def-weil-pbc-proetale-site`
- `def-weil-triangulated-category`
- `det-prop-sfb-qlbar-colimit-x-invert-ell`
- `lem-kun-distinguished-cone-zero`
- `lem-pc-module-filtered-colimits-tensor`
- `lem-sf-derived-ses-triangle`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-sf-triangle-morphism-iso`
- `lem-sfb-topological-stratified-lisse-lattices`
- `lem-weil-pbc-condensed-constructible-serre`
- `lem-weil-pbc-condensed-lfp-local-triviality`
- `lem-weil-pbc-hom-colimit-extension`
- `lem-weil-pbc-integral-constructible-serre`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-weil-pbc-proper-fp-permanence`
- `sk-prop-sfb-cartesian-coefficients`

The scalar-fraction criterion replaces a separate triangulated-functor/cone-zero
argument. Existing integral-model and denominator theorems replace rebuilding
stratum lattices, open/closed reconstruction, cone lifting and coefficient tensor
calculations here. Existing bounded Hom devissage replaces reproving its extension
stability. The remaining definitions are already the statement dependencies or the
interfaces of the reused declarations.

Obsolete top-level tool-use approvals removed (same reasons):

- `det-prop-sfb-qlbar-colimit-x-invert-ell`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-weil-pbc-hom-colimit-extension`
- `lem-pc-module-filtered-colimits-tensor`
- `lem-sf-triangle-morphism-iso`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `sk-prop-sfb-cartesian-coefficients`
- `lem-sf-derived-ses-triangle`
- `lem-weil-pbc-integral-constructible-serre`
- `lem-weil-pbc-condensed-constructible-serre`
- `lem-weil-pbc-condensed-lfp-local-triviality`
- `lem-weil-pbc-proper-fp-permanence`

## Where the brief, the DAG or earlier work was wrong

The direct route listed in the node duplicated continuous-coefficient APIs that
are already implemented. Its planned Hom comparison included finite-stage
factorization; injectivity also needs eventual equality of representatives. The
existing Hom-colimit proof supplies this as well, and this delivery writes the
filtered-colimit equality argument explicitly. No disputed statement is used in
place of the assigned statement. The first delivery gate rejected a concrete derived-functor cache and explicit
instance bindings in public statements. Those changes were removed. The final
version retains the original API verbatim and uses proved private additivity and
localization helpers plus proof-valued local tensor-preservation instances.
Downstream/name-use checks find only this module and its import-only root
aggregator; no external module requires adaptation. The interface probe requests
a record of the four named proof-valued local instances and inferred instance
expressions: `coord/changes/B3-ell-adic-tensor-instance-cache.md`.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
