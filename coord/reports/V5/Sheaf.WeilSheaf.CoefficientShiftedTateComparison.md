## What changed

Replaced the body of `coefficient_shifted_tate_comparison` with an explicit family:
`canonicalCoefficientWeilCohomology P X₀ n ⋙ E`. Its exceptional comparison comes
from the normalized heart comparison. Its Tate comparison splits into the surviving
degree and the vanishing degrees, with real isomorphism composition in both cases.
The assigned declaration's signature and public imports are unchanged.

Added `CanonicalCoefficientWeilCohomology`, a construction from the existing proved
`fixedPairCommonTruncationCohomology` package. It retains the rational signed Roos
normalization and the common-stage inclusion comparison, and lifts the explicit
truncation/truncation/shift composite into the coefficient Weil heart.

Added `CoefficientTwistedConstantVanishing` with a complete Lean proof. Faithful
coherent reduction identifies the scalar and reconstructed tensor units; sourceUnit,
tensoring with that identification, the right unitor and the inclusion shift comparison
identify the source carrier with a shifted heart line. Standard truncation bounds prove
vanishing on either side of -2d. Faithful forgetting proves uniqueness of all arrows
to and from that object; the available zero arrows then exhibit a zero object.
This proof does not import either new comparison hole.

The two remaining comparison statements are in separate modules. Their statements
concern, respectively, realization of the unshifted coefficient Weil heart with its
exceptional counit normalization, and the surviving coefficient cohomology with its
Frobenius action. Neither asserts the all-degree shifted native comparison. No existing
module besides the assigned item, and no existing node besides its node, was changed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.NativeCoefficientCohomology.coefficient_shifted_tate_comparison`
by a complete proof from two new lower statements. This is a decomposition, not a
claim of net hole reduction: one hole closed and two holes added.

The construction
`WeilConjectures.NativeCoefficientCohomology.canonicalCoefficientWeilCohomology`
and the theorem
`WeilConjectures.NativeCoefficientCohomology.coefficient_twisted_constant_vanishing`
contain no sorry. The vanishing proof is independent of both new holed statements.

Exactly two sorries remain in this delivery, both entire named public theorem proofs:

- `WeilConjectures.NativeCoefficientCohomology.native_coefficient_heart_comparison`
  (`lem-sf-native-coefficient-heart-comparison`).
- `WeilConjectures.NativeCoefficientCohomology.coefficient_twisted_constant_surviving_cohomology`
  (`lem-sf-coefficient-twisted-constant-surviving-cohomology`).

No definition contains a sorry. No target signature changes. Existing imported holes
remain the responsibility of their own items. The delivery tool performs the compile
and axiom probes on the final packet.

## No longer needed

No existing module is withdrawn or claimed globally pruned. The assigned proof does
not use `coefficient_cohomology_comparison`: its module remains publicly imported
because it defines Pairs, exceptionalConstant and twistedConstant, and its DAG node
remains a statement dependency. Its existential functors cannot be assumed to have
off-degree vanishing.

The original direct realization and exceptional-normalization proof dependencies are
still needed in the new heart-comparison node. Root/tensor/shift dependencies remain
needed in the coefficient calculation. Their removal from the assigned node's direct
proof_deps only reflects the actual new proof structure; it is not global pruning.
No original public import is removed. The three new consumer modules import the
canonical cohomology module publicly and omit the redundant direct import of
CoefficientCohomologyComparison, which that module already reexports.

## Where the brief, the DAG or earlier work was wrong

The existing surviving-degree coefficient_cohomology_comparison theorem does not
supply vanishing for its existentially chosen family. Applying it and claiming that
family comes from standard cohomology would add an unstated hypothesis.

The purity-source scalar unit is not definitionally the reconstructed tensor unit,
and inclusion of a shifted finite-stage line is not definitionally the shift of its
inclusion. The vanishing proof supplies both missing isomorphisms explicitly.

The generic sfModelWeilCohomology interface obtains a cohomology comparison from a
chosen ConstructiblePullbackComparison. Its exposed specification does not retain
the finite-stage signed normalization needed to identify shiftedLineTheta in the
surviving degree. Instead of changing this shared definition, the new local
construction uses the existing normalized fixed-pair truncation package. This is
an interface limitation, not a claim that the existing declaration is false.
The generic fixed-pair package is used as t-structure infrastructure; the blueprint
unit's purity transport route and every target statement are preserved.

Both remaining statements were checked at d=0 and on empty schemes. Neither uses
smoothness, geometric purity, or an equivalence of native derived Weil complexes
with derived fixed pairs. The heart equivalence in the remaining realization
statement is only an equivalence of sheaf hearts.

A read-only overlay DAG audit also found the pre-existing cycle
`lem-pc-ring-hom-extension-differential` →
`lem-pc-ring-hom-extension-differential-adjacent` → the first node. It is already
reachable from the assigned node in the shared baseline. No cycle contains any
node delivered here. The inherited DAG records were left for the maintainer.

## New nodes

`def-sf-canonical-coefficient-weil-cohomology` records the explicit normalized
construction and its Lean definition in CanonicalCoefficientWeilCohomology.

`lem-sf-coefficient-twisted-constant-vanishing` records the proved coefficient-side
off-degree vanishing, in CoefficientTwistedConstantVanishing.

`lem-sf-coefficient-twisted-constant-surviving-cohomology` records only the surviving
coefficient-side cohomology and its Frobenius identification, in
CoefficientTwistedConstantSurvivingCohomology. It is the first remaining hole.

`lem-sf-native-coefficient-heart-comparison` records the normalized heart equivalence,
unshifted root-line normalization and exceptional counit comparison, in
NativeCoefficientHeartComparison. It is the second remaining hole.

All four nodes use the assigned chapter and unit. No change record is required:
no existing definition, statement, instance, attribute or public import was changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.WeilSheaf.CanonicalCoefficientWeilCohomology": "93d59bca2c15307b513b53947d4950d37a96dfeb", "Sheaf.WeilSheaf.CoefficientShiftedTateComparison": "f6d1defad014526817b43177f461e725cbf2e03b", "Sheaf.WeilSheaf.CoefficientTwistedConstantSurvivingCohomology": "ee87f492fc14c5586f4297b5e68b58c78809b997", "Sheaf.WeilSheaf.CoefficientTwistedConstantVanishing": "fd3fff1baabda0c124e305ed1f6efe767f0a5945", "Sheaf.WeilSheaf.NativeCoefficientHeartComparison": "c737b42035f48342a65ecdd93c38e133541b5235"}, "results": {}, "time": "2026-10-28T10:44:36+0800", "transitive": 0, "version": 1}
```

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
