## What changed

Prove signed interchange and the two specified finite-free augmentation corollaries in
`Sheaf.Algebra.Homology.FiniteFreeResolutionTensor`. All original signatures, public
imports, and public definitions are unchanged. The private coordinate isomorphism is
proved by product extensionality and finite-sum identities. Finite-free flatness uses
finite biproducts and the existing finite-coproduct flatness helper. The augmentation
proof uses the specified mono-cokernel augmentation, the normalized fixed-K-flat
comparison, and preservation of cones by the additive ordinary tensor functor.
The degree-zero proof uses the supplied isomorphism itself.

The generic signed-braiding helper avoids repeated unfolding of the sheaf tensor.
Private structural instances and local irreducibility control the existing localization
and derived tensor definitions. The five cached instances are private proved lemmas
registered with local instance attributes. The node records the two proved routes; the original
plan for the main theorem remains.

## Proved and sorry left

Three original holes closed:

- `SheafOfModules.FiniteFreeResolution.signedInterchange`.
- `SheafOfModules.FiniteFreeResolution.shortExact_finiteFree_augmentation`.
- `SheafOfModules.FiniteFreeResolution.finiteFree_iso_augmentation`.

One original hole remains:

- `SheafOfModules.FiniteFreeResolution.finiteFreeResolution_tensor`, node
  `lem-sfb-ringed-finite-free-resolution-tensor`.

No holes added, no split statements, no holes in definitions. The coordinate identities,
flatness helpers, signed formula, and both augmentation corollaries were checked in
scratch compiles. The assembled module compiled successfully after local transparency control;
delivery preflight performs the final verification.

## No longer needed

No existing module or node is withdrawn. No original public import is removed.
The proved corollaries need no new cone-cohomology theory: the existing
`CochainComplex.finite_free_mono_cokernel_kflat` supplies the specified augmentation.
The signed formula and naturality use the existing monoidal cochain braiding.

The experimental proof imports `Sheaf.SecSmoothPurity.CochainTensoratorExistence`,
`Sheaf.SecSmoothPurity.CochainTensorCoherenceData`,
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`,
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`, and
`Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` are not needed by the delivered
proofs and were removed. The section-calculus and coherence dependencies tried for the
unfinished main proof are not added to the DAG. Original planned dependencies remain
needed by that unfinished theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The existing library already contains the
signed cochain braiding and the specified finite-free cokernel resolution, shortening
the proofs of the three completed declarations.

A complete main-theorem attempt was written, but the assembled proof did not compile
within 60 seconds. Profiling identified repeated tensor typeclass inference and
unfolding of localization constructions. The verified corollaries are delivered, with
the original main hole retained. This is a partial proof delivery, not a decomposition.
No definition or statement was weakened to make it compile.

The compile service and provider interrupted numerous earlier checks. Those requests
were checked before retrying; the first delivery attempt pushed nothing after its local compile timed out.

Preflight requested the proof-context change record
`coord/changes/Y2-finite-free-resolution-proof-context.md`; it records the local
attributes and all consumers. No consumer adaptation is required.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
