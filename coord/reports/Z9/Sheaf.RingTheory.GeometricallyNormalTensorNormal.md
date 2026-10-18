## What changed

Completed the normal-domain argument in
`lean/Sheaf/RingTheory/GeometricallyNormalTensorNormal.lean`.
The proof reduces to finite-type normal subalgebras, uses separability and the declared
smooth directed cover for normality after extending to `Frac(A)`, and proves the
intersection of the two partial fraction localizations using a linear retraction.
Normality then follows from the existing reduced, finite-minimal-prime criterion.
All added helpers are private and fully proved; no additional Lean module is needed.

Repaired the universe parameters of the intermediate `Algebra.normal_domain_case`:
its field tests now range over `Type (max u v w)`, matching the existing main theorem.
Universe lifts implement the reduction without restricting either algebra's universe.
The main theorem `Algebra.isNormal_tensorProduct_of_geometricallyNormal` keeps its
signature and visibility. No definition or target statement changes. The change record is
`coord/changes/geometrically-normal-tensor-domain-universes.md`.

Added the proof-only import `Mathlib.RingTheory.TensorProduct.Maps`; removed the eight
imports listed below. Updated both existing DAG proofs and attached the existing proved
Noether finiteness theorem as a new library leaf. The unit's realized statement and steps
are unchanged: these algebra lemmas are below its normalization argument.

The server compiled the final file cleanly in 29.6 seconds, with no errors or warnings.
There are no diagnostic commands left. `#print axioms Algebra.FiniteType.finite_integralClosure`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Original hole: `Algebra.normal_domain_case`, node
`lem-weil-pbc-geometrically-normal-tensor-normal-domain-case`.
Closed this hole after the documented universe-interface repair, with a complete Lean
proof of the repaired statement. The original independently quantified extension universe
is not claimed to have been proved. The unchanged main theorem now uses this proved
intermediate theorem.

Holes added: none. Holes remaining in this module: none. New split-offs: zero.
This is a proof and interface repair, not a decomposition. The pre-existing supporting
Sheaf declarations remain dependencies; their existing holes are not claimed closed here.

## No longer needed

Removed these proof-only imports:

- `Mathlib.Algebra.Module.LocalizedModule.Basic`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.RingTheory.RingHom.Flat`
- `Sheaf.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra`
- `Mathlib.RingTheory.Localization.Integral`
- `Mathlib.RingTheory.Ideal.GoingDown`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`

The following former direct proof dependencies of this item are unnecessary:

- `lem-fin-normalization-extension-finite`, `def-fin-normalization-extension`, and
  `def-weil-finite-integral-morphism`: construct finite normal subalgebras using the
  existing algebraic Noether finiteness theorem, without scheme normalization.
  Removed the obsolete top-level `tool_uses` approval for the first of these nodes.
- `lem-sc-flat-going-down` and `def-weil-pbc-flat-ring-map`: the injection into the
  Noetherian fraction-field tensor product and `Ideal.minimalPrimes_comap_subset`
  already bound the minimal primes. Tensor-map injectivity only needs field flatness.
- The direct citation of
  `lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra` is replaced by
  `lem-kun-separable-smooth-colimit`, whose declared cover supplies exactly the stages
  used here. The former lemma remains a transitive dependency of that cover, so this
  delivery does not claim its whole module can be removed from the target closure.

The remaining former dependencies are retained in the domain-case node as appropriate,
including localization base change, field flatness, filtered-colimit normality,
smooth normality, separability, and the reduced-normality criterion. Removed imports
may still be reached through other modules; the list describes this proof's direct needs.

## Where the brief, the DAG or earlier work was wrong

The old intermediate signature used an independent `Type*` for the test fields.
It did not guarantee that the fraction fields in the argument were admissible tests;
for a large base field the smaller-universe test condition can even be vacuous.
The corrected signature follows the main theorem's common-universe convention.
The declaration-use search lists only this module; all eleven downstream modules use
its unchanged main API, so no downstream adaptation is required.

The inherited proof plan invoked geometric finiteness of normalization to construct
normal finite-type subalgebras, although the source library already proves the exact
algebraic finiteness input. Its going-down step is also unnecessary by the general
minimal-prime comap lemma. The inherited domain-case node was absent from the main
node's proof dependencies despite being used by its Lean proof; that edge is now explicit.

Installing fraction-field structures with `IsFractionRing.toField` preserves the existing
localization ring structure and avoids expensive conversions through another field instance.
The finite-type subtype localization instance elaboration still needs a local 400000-heartbeat
budget; the file remains within the unchanged 60-second compile limit.

## New nodes

`lem-weil-pbc-finite-type-field-integral-closure-finite` attaches the existing proved
`Algebra.FiniteType.finite_integralClosure` from
`WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure`.
It is Noether's finiteness theorem (Stacks Tag 0335), used with the degree-one extension
of the fraction field. No new declaration or hole is introduced. Searches found no
matching general Mathlib theorem: `IsIntegralClosure.finite` requires a normal base and
separability. The attachment's axiom check is clean. Its statement and definitions include
the compatible scalar towers and the finite extension, and cover the degree-one case used.

Change record: `coord/changes/geometrically-normal-tensor-domain-universes.md`.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
