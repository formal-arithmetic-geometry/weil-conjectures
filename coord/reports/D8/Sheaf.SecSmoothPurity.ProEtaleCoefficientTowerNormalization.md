## What changed

Only `lean/Sheaf/SecSmoothPurity/ProEtaleCoefficientTowerNormalization.lean` and its
existing DAG proof route change. All existing public statements, definitions and
public imports are preserved. Private helpers implement tensor transport along a
ring-sheaf isomorphism, ordinary coefficient-square pasting, exact-equivalence
derived transport, and
specialization of the existing successive normalization to the published functors.

The geometric comparison uses the existing normalized ring-isomorphism theorem.
Scalar transport pastes the balanced ordinary comparisons and applies the existing
`CategoryTheory.leftDerivedSquare` to the exact coefficient-relabelling equivalences.
Its universal counit equation holds on every complex. The main theorem
uses the existing equality of the published associator with normalized derived
composition. No arbitrary comparison is substituted for the specified associator.

## Proved and sorry left

The packet closes the three original holes, with no new holes or splits:

- `AlgebraicGeometry.ProEtale.coefficientTowerGeometricTransport`.
- `AlgebraicGeometry.ProEtale.coefficientTowerScalarTransport`.
- `AlgebraicGeometry.ProEtale.proEtaleCoefficientTowerNormalization`.

Actual remaining `sorry` count in the module: zero. No new module contains a hole.
All private helpers are proved. The existing dependency statements retain their
own proofs or holes; none is changed in this packet.

The complete proof passed the required remote compiler cleanly in 50.6 seconds.
Delivery preflight checks the complete packet and its axioms.
All three public signatures, all six original definition bodies, and every original
public import are preserved. Sequential elaboration avoids contention among the
large derived-category specializations; normal linting and kernel checking remain
enabled. The final proof contains no `sorry`.

## No longer needed

The route does not directly invoke the separate K-flat resolution and pullback
proofs, the general derived coefficient-adjunction theorem, the abstract conjugate
API, or conjugate-unit uniqueness. Their needed computation and coherence results
are already packaged in the proved successive-normalization and published
associator interfaces. Accordingly the direct proof dependency list is reduced.
These dependencies may remain transitively needed by those existing modules; no
source declaration or module is withdrawn.

The obsolete direct tool approvals removed from this node are
`prop-weil-pbc-proetale-constant-ring-map`, `lem-pc-kflat-resolution`,
`lem-weil-pbc-ringed-topos-kflat-pullback`, `lem-pur-derived-change-of-rings`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`, and
`lem-weil-pbc-conjugate-iso-unit-equation`. The actual constant coefficient
comparison is already proved for arbitrary rings by the operations interface.

Removed redundant original proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.

The retained proof imports expose the existing private normalization and published
associator interfaces. The new private import of `ExactEquivalenceDerivedSquares`
uses its proved left-derived square and counit equation. `ScalarExtensionRingIso`
uses its public theorem only.
No module deletion is proposed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The plan can be shortened using results proved since
its formulation. In particular exact coefficient relabelling is an additive
equivalence. The
already proved exact-equivalence derived-square theorem gives scalar transport
and its specified counit equation on every complex directly;
there is no need to introduce a new K-flat preservation lemma or restrict the
normalization equation to resolving representatives.

The blueprint unit route and all public mathematical content are retained.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
