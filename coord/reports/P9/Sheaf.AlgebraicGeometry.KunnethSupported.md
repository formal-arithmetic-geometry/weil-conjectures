## What changed

Replaced the hole in `AlgebraicGeometry.Etale.isIso_supportedExteriorProduct` by a
complete Lean proof from the existing ordinary Kunneth theorem, the two specified
localization morphisms, supported site comparison, and two new compatibility lemmas.
The blueprint's double localization, including its boundary maps, is retained.
The original theorem signature and the three coefficient instances are unchanged.
No adopted source-library file, definition, target statement, or existing theorem
statement was changed.

The proof first localizes in Y with full first support, repeats on the complement
of Z, then localizes in X. It cancels the specified support-congruence and open
transport isomorphisms rather than replacing the actual products by unspecified
triangle components. The canonical pro-etale clause follows from the published
comparison equality. The arbitrary-witness clause uses the supplied witness data,
the finite-coefficient realization equivalence, and a proved naturality calculation.

Added three proved supporting results:
`Etale.supportedExternalProduct_boundedBelow` in the item, using the existing general
Tor-amplitude tensor estimate, and `ProEtale.isIso_supportedExteriorProduct_of_iso`
in `ProEtaleSupportedProductNaturality`, and the full-support normalization
`Etale.isIso_supportedExteriorProduct_of_fullSupport` in `SupportedFullSupportProduct`.
The naturality proof treats the actual derived coefficient comparison and evaluation
counits, transposes their square, and cancels isomorphisms. The full-support proof
uses the existing full-support forgetful isomorphisms and the forgetful pairing
equation. All private helpers are proved.

The proofs use abstract coefficient categories and an abstract predicate adapter
for `Over.mk` before specializing to the p-adic quotient. Explicit structural
congruence handles the two derived tensor presentations. This avoids large
unfoldings; the existing definitions and compile limit remain unchanged.

## Proved and sorry left

Closed the item's one hole, by declaration:
`AlgebraicGeometry.Etale.isIso_supportedExteriorProduct`
(`lem-pur-kunneth-supported`). The item now contains zero holes.

Added exactly two holes, each in its own new module:

- `AlgebraicGeometry.Etale.isIso_supportedExteriorProduct_iff_supportComplement_eq`
  in `Sheaf.AlgebraicGeometry.SupportedProductSupportCongruence`, node
  `lem-pur-supported-product-support-congruence`.
- `AlgebraicGeometry.Etale.supportedExteriorProduct_forget`
  in `Sheaf.AlgebraicGeometry.SupportedProductForgetSupports`, node
  `lem-pur-supported-product-forget-supports`.

This is a decomposition of one upper hole into two independent normalization
results, not a net proof-closure gain. Both are true independently of Kunneth:
the first changes the presentation of a closed support, and the second is the
forgetful pairing equation explicitly required by the final paragraph of the
blueprint definition. Neither asserts the
original finite-coefficient, double-localization, or pro-etale-witness theorem.
Their docstrings and nodes contain their source and complete proofs in words.

The other three new public results, `Etale.supportedExternalProduct_boundedBelow`
(`lem-pur-supported-product-bounded-below`),
`ProEtale.isIso_supportedExteriorProduct_of_iso`
(`lem-pur-proetale-supported-product-naturality`), and
`Etale.isIso_supportedExteriorProduct_of_fullSupport`
(`lem-pur-supported-full-support-product`), have complete Lean proofs and no
new holes. Existing named dependencies that still have holes are used as intended
by this stage; they were not copied or replaced by new assumptions.

Validation: lcompile --all passed for all five modules in import order, without
warnings: the item checked in 27.4 seconds and the full-support proof in 19.4 seconds.
Earlier slow conversions were fixed by abstract predicate interfaces and keeping
the witness transport definition irreducible. Individual checks also passed. The
original main signature was compared with the shared source after whitespace
normalization and is identical. All Lean lines are at most 100 characters.

## No longer needed

Removed these direct proof imports from the item:

- `Mathlib.Topology.Constructible`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`
- `Sheaf.AlgebraicGeometry.SupportRestrictionTriangle`
- `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution`

The root proof no longer uses `lem-kun-0f1m`: its lower-bound calculation follows
from the proved abstract Tor-amplitude estimate instead of constructing a separate
K-flat representative. Its direct `lem-pc-derived-tensor-second-factor-functor`
and `lem-pur-support-restriction-triangle` dependencies are absorbed into the
existing localization theorem, which already supplies distinguished triangles.
Those results remain needed by that theorem. The direct definitional dependencies
`def-weil-finite-type-morphism`, `def-weil-proper-morphism`, and
`def-kun-derived-tensor` are replaced by the existing scheme instances and the
new bounded-below lemma. The corresponding root proof dependencies and the two
obsolete root tool approvals were removed.

No module is withdrawn or claimed globally pruned. In particular, all declarations
and imports of `WeilConjectures/` remain present. The unit's localization route is
unchanged.

## Where the brief, the DAG or earlier work was wrong

The localization components use `supportIntersection (identity) i`, rather than
the syntactically identical closed immersion i. Their derived support congruence
alone identifies the target support functors; it does not identify the actual
supported coefficient pairing. The separate support-presentation normalization
supplies precisely this missing compatibility. Likewise, the full-support product
is defined through its own normalized coefficient adjunction and derived tensor
comparison; identifying its sections with global sections does not by itself
identify its arrow with ordinary Kunneth. The forgetful pairing equation records
that calculation explicitly, and the full-support consequence is proved by
cancelling the already-stated full-support forgetful isomorphisms.

The planned lower K-flat representative is unnecessary: the source library already
proves the required derived tensor lower-bound estimate and preservation of Tor
amplitude by exact pullback. The old blanket fixed-origin interface is unnecessary
for transporting the specified witnesses. No mathematical statement is disputed.

Edge cases checked in formulating the new statements: empty or full supports,
empty ambient schemes, zero complexes, shifts, empty Tor intervals, arbitrary
scheme structures on the same closed subset, and full supports presented by
nonidentity isomorphisms. Neither normalization lemma assumes finiteness,
constructibility, flatness of K, or an unwarranted boundedness condition.

## New nodes

`lem-pur-supported-product-support-congruence`: invariance of invertibility under
equal open complements, for arbitrary unbounded etale complexes. It is needed to
cancel the identity-intersection presentation in both localization arguments.

`lem-pur-supported-full-support-product`: the proved invertibility consequence of
the forgetful pairing equation and the existing full-support forgetful
isomorphisms. It supplies the middle and open isomorphisms in the second-variable
localization, and has no hole.

`lem-pur-supported-product-forget-supports`: the equality of the actual pairing
followed by forgetting support with the tensor of the source forgetful maps
followed by the ordinary pairing. This is the final paragraph of the blueprint
definition, stated for arbitrary unbounded coefficient complexes. It is needed
for the now-proved full-support consequence and retains one hole.

`lem-pur-supported-product-bounded-below`: the proved lower-bound estimate for a
bounded-below first factor and finite-Tor-amplitude second factor, in the item.

`lem-pur-proetale-supported-product-naturality`: the proved transport of the actual
pro-etale pairing through isomorphisms, needed for arbitrary specified witnesses.

Each new node has its Lean attachment, source, complete proof plan, and three
Mathlib searches. The proof interface and local elaboration commands are recorded in
`coord/changes/P9-kunneth-supported-proof-interface.md`; no existing statement or
definition was repaired or changed, and there are no forced adaptations.

The initial server preflight requested LeanSearch records in addition to the
LeanFinder/Loogle and source searches, and a change record for the item commands.
All five LeanSearch queries were run and recorded, and the change record was added.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
