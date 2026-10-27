## What changed

Proved `WeilConjectures.geometricCommonStagePull_isLeftAdjoint` with its exact existing
signature. Reused the already proved private raw-localization and stage-descent helpers
through `import all Sheaf.Paper.SfRationalDirectImageAdjunction` and
`import all Sheaf.Paper.SfCommonStageDirectImage`. The proof constructs each rational
adjunction from `sfIntegralPullbackLinearAdjunction`, forms the normalized invertible
coefficient mates, proves their counit equation using `mateEquiv_counit`, then descends
the resulting coherent right family, unit and counit. The existing uniqueness theorem
identifies the descended left functor with the actual `commonStageDerivedPullback`.
Neither direct-image definition nor its specifying adjunction changed.

Generalized the existing lower coefficient-only theorem
`WeilConjectures.sfRationalDirectImageCoefficientCompatibility` from specified finite-field
geometric fibers to scheme maps with the existing residue invertibility instances.
Its right-mate clause still requires every pointwise adjunction as input, so it asserts
no arbitrary-scheme constructible right-adjoint existence. Finite-free coefficient
extension and the normalized scalar associators are independent of a finite-field
presentation. The sole existing caller in `Sheaf.Paper.SfRationalDirectImageAdjunction`
now explicitly specializes this interface to `zlFiberMap D f`; all its signatures and
proofs otherwise stay unchanged. The item uses the same generalized interface.

Updated the lower theorem's node statement and Lean signature, with a statement-change
record checking its existing DAG citer. Retained the finite/integral construction steps
in `def-weil-derived-direct-image` and added the actual arbitrary-field localization and
common-stage descent steps. No new public declarations or nodes were added.

Change record: `coord/changes/C2-geometric-common-stage-coefficient-generality.md`.
It includes all downstream modules and their current claims. All three delivered Lean
modules compiled together through `lcompile.py --all`; the item is also checked after
removing redundant proof imports. Normal delivery preflight performs the axiom probes.

## Proved and sorry left

Closed: `WeilConjectures.geometricCommonStagePull_isLeftAdjoint`
(node `def-weil-derived-direct-image`), 1 of the item's original 1 holes.
The item now has zero `sorry` occurrences. Added holes: zero. Split-off holes: zero.

Retained, not proved: `WeilConjectures.sfRationalDirectImageCoefficientCompatibility`
(node `lem-sf-rational-direct-image-coefficient-compatibility`), exactly one existing
named theorem hole in the adapted dependency. Its statement is generalized as recorded;
this is not reported as a proof or as a closed hole. Its source and complete proof in
words remain in its docstring, with the scope explanation updated. The adapted
`SfRationalDirectImageAdjunction` module has no holes. Packet total: 2 original holes,
1 closed, 1 retained, 0 added. This proves the item relative to the stated lower
coefficient theorem, as intended by stage 3; it is not a claim of axiom-free target closure.

## No longer needed

Removed the item's direct proof import `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility`:
its ordinary/rational/common-stage Hom results require a finite-field datum and separated
finite-type morphisms, so they cannot apply to the item's arbitrary-field signature.
The normalized coefficient mate interface and the already proved formal descent give
the required argument directly. This does not withdraw that module: other consumers
still use it.

Removed the redundant direct proof import `Sheaf.Paper.SfIntegralPullbackLinearAdjunction`:
the actual integral theorem is still needed through the reused rational-localization
proof in `SfRationalDirectImageAdjunction`; its node is explicitly recorded as a dependency.
Retained all public imports, including the published finite-field-model interface.
No existing module or node is withdrawn or globally pruned. No formerly recorded
finite/integral dependency is removed: those steps remain part of the node's broader
construction. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item's original proof docstring proposed applying
`purOrdinaryAdjunctionScalarCompatibility` and `purOrdinaryAdjunction_commonStage` over an
arbitrary field. Their actual signatures demand a finite-field datum and separated
finite-type maps, so that proposal did not fit. The existing coefficient-only theorem
also unnecessarily restricted its schemes to specified geometric fibers. Its finite-free
coefficient proof works independently of that presentation, so the documented lower
interface generalization repairs the mismatch while preserving all former cases.

The owning node's earlier proof covered finite/integral direct image but did not record
the new arbitrary-field common-stage theorem attached to it. The added proof steps now
record precisely the localization, coefficient mates and formal stage descent used.
The blueprint unit `sk-def-sf-operations` has no realized steps to bypass; its
ordinary direct-image operation and all its existing interfaces are retained.

Edge cases checked in the mathematical review: identity coefficient inclusion uses the
canonical tensor unit; zero objects and empty schemes retain the triangle identities;
no separatedness, finite-field descent model or finite-quotient flatness is introduced.
All witness choices used for data are determined by uniqueness: the left stage family
is fixed in equality by its component normalization, and right adjoints are determined
up to their unique adjunction-compatible isomorphism.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
