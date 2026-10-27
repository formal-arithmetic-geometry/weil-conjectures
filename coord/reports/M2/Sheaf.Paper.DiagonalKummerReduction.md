## What changed

Restored the quarantined item source and replaced the whole-proof hole in
`AlgebraicGeometry.ProEtale.diagonal_kummer_reduction` by a complete combination
of two separate mathematical steps. Its original theorem signature and public
import are unchanged; its three proof imports are private. Nine further new
modules provide generic assembly, sheaf-level assembly, full Cartier adjunct uniqueness,
the diagonal sign calculation, finite scalar normalization, canonical small-Ext caches,
and real definitions sharing the concrete proposition and predicate types
before specialization.

`DiagonalSourceQuotientNormalization` isolates the ordinary supported-source
cokernel and quotient-generator normalization. It uses no derived functor, units,
boundary, or invertibility hypothesis on the base.
`KummerStrictTargetTransport` computes simultaneous derived reduction of shifted
comparison units on an arbitrary scheme and its action on arbitrary degree-one
arrows from normalized sources. It supplies a residue-linear lift and its full
Kummer adjunct without a Cartier divisor, pole extension or Cartier class.

The proved generic assembly unpacks one strict target H, its roots identification
and b; the sheaf-level helper specializes it to the actual coefficient categories.
At each level it chooses the normalized source, applies arbitrary-arrow transport,
and substitutes the evaluation equation into the finite-class predicate. The
finite implication uses both sign cancellations and full Cartier adjunct uniqueness
before restricting scalars. No derived faithfulness or reconstruction of strict
arrows from unrelated level maps is used.

Only proof, proof_deps and proof_origin change in the existing node. Each new
module has a complete node; the unit's strict-system and Kummer route is preserved.
No existing shared interface changes.

## Proved and sorry left

The upper hole in `AlgebraicGeometry.ProEtale.diagonal_kummer_reduction` is closed
by a complete combination proof. These public helpers have complete proofs:

- `AlgebraicGeometry.ProEtale.kummerModuleHasExt`.
- `AlgebraicGeometry.ProEtale.kummerAbHasExt`.
- `AlgebraicGeometry.ProEtale.kummer_transport_assembly`.
- `AlgebraicGeometry.ProEtale.sheaf_kummer_transport_assembly`.
- `AlgebraicGeometry.ProEtale.canonical_cartier_class_of_adjunct`.
- `AlgebraicGeometry.ProEtale.diagonal_cartier_class_of_adjunct`.
- `AlgebraicGeometry.ProEtale.diagonal_finite_cartier_normalization`.

The private `double_negative_ext_associativity` is also proved. Two whole named
public theorem holes are added and remain:

- `AlgebraicGeometry.ProEtale.diagonal_source_quotient_normalization`, node
  `lem-sfb-diagonal-source-quotient-normalization`.
- `AlgebraicGeometry.ProEtale.kummer_strict_target_transport`, node
  `lem-sfb-kummer-strict-target-transport`.

Item-module holes: 1 before, 0 after. Delivery holes: 2. This is a decomposition,
not a complete proof of the mathematical obligation: upper holes closed 1,
lower holes added 2, net -1. No definition, instance or private declaration has a hole.

`KummerArrowTransport` is a real predicate for the scalar-adjunct and evaluation
equations. `KummerTargetData` stores actual strict-system data; `KummerStrictTarget`
merely specializes its type. Its existence theorem asserts Nonempty; no definition
chooses data from that unproved existence theorem.

The definitions `sheafKummerConclusion` and `sheafKummerClassCondition` have
exactly the original normalized target and scalar-adjunct implication as bodies.
They add no theorem, proof hole, hypothesis, existence assertion or chosen data.
`sheafKummerFinitePredicate` and `sheafKummerSourcePredicate` are the literal
function types of the predicates, with no chosen data or proofs.
The definition `kummerRootNormalization` is exactly the original canonical
underlying roots-map equation, shared before derived specialization.
The real definitions `kummerScalarAdjunct`, `negativeExtProduct` and
`kummerComparedUnit` name exactly the full scalar adjunct, negative Yoneda product
and positive units-comparison/Kummer composite. The abstract private identity
cancels the two signs and reassociates the product before geometric specialization.
`canonicalCartierClass` and `diagonalResidueClasses` are the existing uniquely
characterized Cartier classes, with their interfaces shared. Their data come from
the existing unique-characterization theorem, never an arbitrary existence witness.
The finite helper applies congrArg to the full class equality and then takes HEq.

The two small-Ext cache theorems reuse `geoCartierModuleExt` and
`geoCartierIntegralExt`, with the named canonical abelian structures in their
theorem types. Local instance attributes select these caches; no global instance
or priority is introduced. Existing additive and exactness witnesses are retained.
No new category or abelian structure is introduced. Attributes on existing
definitions are local; new irreducible definitions have explicit real bodies.

Validation: all twelve modules compiled in import order within the per-file limit.
The final assembly kernel check took 35.3 seconds and the item theorem 29.3 seconds.
Profiling options were removed before submission. The original theorem signature
and public import were checked against the current shared source verbatim.

## No longer needed

No original import is removed and no library module is withdrawn or claimed pruned.
All proof imports are used. The item needs the ordinary source calculation,
strict target transport, sheaf assembly and full finite Cartier normalization.
It does not directly invoke the entire site-comparison conjunction or the entire
divisible-extension theorem.

The original dependencies def-kun-truncations, def-pur-roots-of-unity-sheaf,
lem-amb-kummer-any-base, lem-sfb-divisible-extension-derived-reduction and
lem-sp-cartier-reduction-site-comparison remain in the lower steps.
lem-pc-source-module-kflat-resolution is replaced by lem-pc-kflat-resolution,
the ringed-site resolution theorem: the module-only statement does not directly
supply a sheaf resolution. No adopted source declaration or module is removed.

Both lower plans borrow lem-pur-constant-two-term-resolution and
lem-weil-pbc-site-module-sheaf-constant-ring-equivalence for the coefficient
quotient and the bridge between external module sheaves and constant-ring module
models. These preserve the unit route and bypass no realized unit step.

## Where the brief, the DAG or earlier work was wrong

The item source was initially absent from lean/ and preserved at its exact
coord/rework.tsv quarantine path. It was restored from that archive, not withdrawn.
Its interface was also initially quarantined and became available during the session.

The relevant latest-blueprint paragraphs are step (3), source and target, and
step (4); the old item calls these steps 5--7. The proof follows the actual text.
The module-only resolution input is replaced by the ringed-site theorem.

The existing divisible-extension interface treats one residue-ring cochain model.
It does not identify arbitrary simultaneous DiagonalDerivedReduction with that
model after evaluation or construct the strict roots-system comparison. The
new target step states that missing comparison for arbitrary degree-one arrows.
The supported integral/residue sequence likewise does not itself identify the
normalized p-adic ordinary quotient. Its lower plan uses integer representatives
for surjectivity and PadicInt.ker_toZModPow for the coefficient kernel.

Edge cases checked: n=0 means exponent 1; source normalization requires no base
invertibility; the empty scheme gives zero objects and unique maps. No finite-type,
connectedness or primitive-root hypothesis is added. Target transport is before
coefficient restriction, and its negative sign is uniform in the level. No target
or existing statement, definition, binder or universe changes.

## New nodes

`lem-sfb-canonical-sheaf-ext`, module `Sheaf.Paper.CanonicalSheafExt`, proves small
Ext for the canonical sheaf structures from the existing GeoCartier witnesses.
Its two theorem types cache the checked structures and add no hole.

`lem-sfb-diagonal-source-quotient-normalization`, module
`Sheaf.Paper.DiagonalSourceQuotientNormalization`, is the ordinary source part of
blueprint det-prop-diagonal-tower-system (3), including quotient-unit normalization.

`lem-sfb-kummer-strict-target-transport`, module
`Sheaf.Paper.KummerStrictTargetTransport`, is the target and arbitrary-arrow part
of (3)--(4), without the diagonal Cartier class identification. Its auxiliary
structures and expressions have real bodies and no holes.

`lem-sfb-kummer-transport-assembly`, module `Sheaf.Paper.KummerTransportAssembly`,
proves the formal combination over arbitrary abelian categories. It retains both
normalization predicates and the single strict target and adds no hole.

`def-sfb-kummer-sheaf-predicates`, module `Sheaf.Paper.KummerSheafPredicates`,
names the literal source-normalization and finite-class predicate types. Both
definitions have complete real bodies and introduce no holes.

`def-sfb-kummer-sheaf-conclusion`, module `Sheaf.Paper.KummerSheafConclusion`,
and `def-sfb-kummer-sheaf-class-condition`, module
`Sheaf.Paper.KummerSheafClassCondition`, name the literal concrete target and
full scalar-adjunct implication. Their complete real bodies introduce no holes;
separate modules share the checked concrete types before the assembly proof.

`lem-sfb-sheaf-kummer-transport-assembly`, module
`Sheaf.Paper.SheafKummerTransportAssembly`, specializes the proved generic assembly
to a scheme, preserving the arbitrary source and finite-class predicates and using
the actual strict Kummer target. It adds no hole.

`lem-sfb-cartier-canonical-adjunct`, module `Sheaf.Paper.CartierCanonicalAdjunct`,
is proved full adjunct uniqueness for finite coefficients and a Cartier immersion.
Its canonical class is the existing uniquely characterized class. It is independent
of the strict-target existence hole and adds no hole.

`lem-sfb-diagonal-cartier-adjunct-uniqueness`, module
`Sheaf.Paper.DiagonalCartierAdjunctUniqueness`, proves the two-sign cancellation and
specializes full Cartier uniqueness. It chooses no derived-reduction or strict-system
data and adds no hole.

`lem-sfb-diagonal-finite-cartier-normalization`, module
`Sheaf.Paper.DiagonalFiniteCartierNormalization`, proves restriction of the full
class equality to the original finite-class normalization. It adds no hole.

The nodes record actual LeanSearch, LeanFinder, Loogle and grep searches. No exact
supported quotient normalization or simultaneous strict Kummer transport was found.
Change record: `coord/changes/m2-diagonal-kummer-local-elaboration.md`. It documents
the proof imports and explicitly local compiler attributes flagged by the static
interface scanner; no existing shared interface or importer needs adaptation.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
