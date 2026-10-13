## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.affine_open_pseudoCoherent_localization_point` with a Lean
reduction through a specified nested-open finite-free model and the existing
`AlgebraicGeometry.affine_pseudoCoherent_principal_model`. The existing signature,
universes, public imports and docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.SchemeIsoNestedOpenFiniteFreeModel` for the transport
step. The second reader completed its proof using an explicit open-image scheme
isomorphism, termwise exact equivalences, unit/free-sheaf comparisons and derived
localization factorization comparisons. Its functor comparisons follow the existing
proof in `OpenPerfectModelTransport`; that theorem itself requires bounded perfect
models and cannot be applied to the bounded-above finite-free model here.

No existing interface changes or forced adaptations are involved.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.affine_open_pseudoCoherent_localization_point`
(node `lem-sc-affine-open-pseudo-coherent-localization-point`).

Also proved the new intermediate declaration:
`AlgebraicGeometry.Scheme.exists_scheme_iso_nested_open_finite_free_model`
(node `lem-pc-scheme-iso-nested-open-finite-free-model`). The first worker left this as
a split-off hole; the second reader closed it. No holes are added by the final delivery,
and neither delivered module contains `sorry`. The delivery closes one original hole,
not merely a decomposition. The scratch axiom probe shows only `propext`, `Classical.choice` and `Quot.sound`
for both declarations, with no `sorryAx`.

## No longer needed

Removed the item's direct proof import
`Sheaf.AlgebraicGeometry.SchemeIsoDerivedEquivalence`, replacing it with the new
transport module. The second reader also removed that dependency from the new
module. The exact-functor comparisons are already publicly available through
`DerivedCategory`, so no additional proof import is needed.
The old parent proof dependency `lem-pc-scheme-iso-derived-equivalence` is no longer
used. `Sheaf.AlgebraicGeometry.SchemeIsoDerivedEquivalence` leaves this item's
transitive import closure; whether it leaves the targets' closure depends on other
users and is for the maintainer's ledger to determine. No global pruning is claimed.
All existing public statement imports and the principal-model proof import remain.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The old scheme-isomorphism theorem gave
a derived equivalence, not the full nested-open finite-free model transport interface.
The first worker isolated that strictly smaller step. The second reader found that
Mathlib's explicit restriction comparisons, as assembled in the existing proof of
`local_perfect_of_openRestriction_iso`, suffice to prove it without a new hole.
The final node proof dependencies describe this direct construction.

The cited sources are [Stacks Tag 08EE](https://stacks.math.columbia.edu/tag/08EE)
(the affine-spectrum and local-model reduction) and
[Tag 08E7](https://stacks.math.columbia.edu/tag/08E7) (the affine comparison).
The transport lemma is an explicit implementation of the invariant identification
used in those reductions, rather than a verbatim statement of either source lemma.

## New nodes

`lem-pc-scheme-iso-nested-open-finite-free-model`, in
`dag/nodes/sec-picard-framework/lem-pc-scheme-iso-nested-open-finite-free-model.json`,
records the complete proof of the specified bounded-above finite-free model transport
in `lean/Sheaf/AlgebraicGeometry/SchemeIsoNestedOpenFiniteFreeModel.lean`.
The docstring explains the image open, exact equivalences, upper bound, free terms
and derived restriction comparison. No arbitrary data definition is introduced.
There are no change records because no existing interface changed.

## Second reading by W2

1. Compared the delivered item with the repository using `diff` and verified its
   theorem signature byte for byte. Only a proof import and the proof body changed.
   The existing node changes only `proof`, `proof_deps` and `proof_origin`. Pass.
2. Compiled the modules in import order and inspected all declarations and proof
   bodies for forbidden constructs and hollow definitions. Added a scratch-copy
   `#print axioms` probe for both declarations. The final files have no `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by` or `extern`. The probe reports only
   `propext`, `Classical.choice` and `Quot.sound` for both declarations. Pass.
3. Checked the new transport statement on empty V, U = bottom or top, the identity
   scheme isomorphism, rank zero and arbitrary integer bounds. Its explicit image
   open and termwise equivalence handle each case. Independent derived-category
   universes are handled by factorization isomorphisms. Searched independently
   with LeanFinder (exact equivalences and restriction composition), Loogle
   (`"mapFreeIso"`), Mathlib grep and library `rg`. Found useful free-object and
   restriction comparisons, and the perfect-model analogue, but no duplicate of
   this bounded-above finite-free transport statement. The new statement lacks
   the affine, localization and pseudo-coherence conclusions of the item. Pass;
   its formerly split-off proof is now complete.
4. Read the proof from the upper declaration downward. The basis refinement and
   existing principal-model theorem give the intended shortest reduction; the
   remaining transport is now constructed directly from Mathlib comparisons.
   Proof-only imports are plain imports. The removed original dependency is listed
   above. The unit `sk-thm-picard-duality` has empty `realized.statement` and one
   empty `realized.steps` entry; neither is changed or bypassed. Pass.
5. Compared both nodes with their Lean declarations, verified the new node's
   required fields and verbatim signature, and updated its proof steps/dependencies
   to the completed termwise construction. The parent still follows the local
   definition, transport, principal-open basis and principal-model conclusion. Pass.

Second reading changed: proved the transport lemma, removed its redundant proof dependency
import and used the available Mathlib exact-functor comparisons, made its docstring match restriction
along the inverse isomorphism, and updated its DAG proof and this report. The
original upper proof was retained.
