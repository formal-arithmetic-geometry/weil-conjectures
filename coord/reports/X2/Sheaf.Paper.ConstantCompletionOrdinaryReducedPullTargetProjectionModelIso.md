## What changed

Proved the corrected `CategoryTheory.ConstantCompletion.ordinaryReducedPull_targetProjectionIso`
in the assigned module. The defining limit-lift projection equation identifies the two
composite ring maps. Two existing scalar-composition isomorphisms and the existing
inverse-image/scalar-extension isomorphism for the source projection, whiskered and
composed, give the result. This follows the original geometric/scalar-associativity
plan without another split.

Added the missing explicit V, adj : L ⊣ V, and PreservesFiniteLimits L to this statement
and to `ordinaryReducedPull_targetIso`, then changed the latter's caller in Transport
to pass its existing V and adj, with a direct private proof import of TargetIso.
The source-transport call is type-annotated and lets Lean infer its arguments from
the same existing lemma and V/adj, so it elaborates under both the published and the
current reviewed source-side signature. Both are compiled; no source declaration is
modified or duplicated. The corrected conclusion, universes, coefficients and
all target statements are unchanged. The item's public statement import is reduced
from SourceIso to ConstantCompletionInverseImage; a private `import all` reuses the
fully proved generic comparison helpers in ConstantCompletionOrdinaryFinitePullExistence.
No source-library file is changed.

The two statement nodes now describe the actual geometric hypotheses and list all
citers in statement_change. The item's proof plan records the projection equation,
normalized module adjunction argument of the reused helper, and scalar-composition
isomorphisms. The normalized module adjunction node is used as a generic tool from
another unit; this does not replace any statement or step of the proper-base-change
unit. Maintainer tool-use approval, if required, is left to the maintainer.

Change record: `coord/changes/X2-target-projection-geometric-context.md`.

## Proved and sorry left

Initial item hole count: 1, in
`CategoryTheory.ConstantCompletion.ordinaryReducedPull_targetProjectionIso`
(node `lem-weil-pbc-constant-completion-ordinary-reduced-pull-target-projection-model-iso`).
Its corrected geometric statement is fully proved; final item hole count: 0.
No hole is added, no step is split off, and there is no sorry in a delivered definition.
This is a statement repair with a complete proof, not a proof of the false original
non-geometric generality. `ordinaryReducedPull_targetIso` remains proved by composition,
and `ordinaryReducedPull_transport` retains its complete assembly proof.

The pre-existing disputed hole in `ordinaryReducedPull_transport_eq`, node
`lem-weil-pbc-constant-completion-ordinary-reduced-pull-transport-equation`, is not changed
or delivered. This item does not use that false arbitrary-transport assertion to prove
anything. The two generic comparison helpers used here have complete Lean proofs. An independent
`#print axioms CategoryTheory.ConstantCompletion.ordinaryReducedPull_targetProjectionIso`
audit compiled in 6.6 s and reports exactly propext, Classical.choice, and Quot.sound,
with no sorryAx or additional axiom.

Initial item compilation passed in 6.0 s; after narrowing its public import it passed
in 5.0 s. The unadapted TargetIso was compiled against the changed item and failed with
the missing right-adjoint argument and finite-limit instance, establishing the required
caller correction. The final argument-inference version compiled cleanly against published
artifacts (Transport: 4.9 s) and, separately, the complete current-source chain:
SourceIso (3.0 s), the item (4.6 s), TargetIso (2.2 s), unchanged TransportEquation
(3.5 s), Transport (3.4 s), and unchanged OrdinaryReducedPull (3.1 s). Each file was
compiled individually in import order. The unchanged verification copies have been
removed from the packet. Final delivery checks and dependency checks are recorded
by deliver3.py.

## No longer needed

Removed the item's public import of
`Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso`; its own statement needs only
`Sheaf.Paper.ConstantCompletionInverseImage`. TargetIso already imports SourceIso
independently, so the source comparison remains available where needed.

The item no longer has proof-dependency edges to
`lem-weil-pbc-common-quotient-ordinary-insertion`
(`Sheaf.Paper.CommonQuotientOrdinaryInsertion`) or
`lem-weil-pbc-sectionwise-adic-algebra-limit`
(`Sheaf.Paper.SectionwiseAdicAlgebraLimit`). Their stronger quotient/tower or flatness
conclusions are unnecessary here: the actual projection equation and the proved generic
scalar comparison already suffice. These declarations are not withdrawn and are still
used elsewhere. No module is claimed to leave the complete targets' import closure.
The proof does not import any additional quotient or adic-algebra theorem.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (original interface, repaired here): InverseImageData L alone does
not make L a geometric inverse image. Taking C2-invariants, A = ℤ, I = (2), n = 0,
and M = ℤ₂ with sign action gives zero on the old left side and ℤ/2 on the old right
side, despite preservation of finite limits, constant rings, and algebraic operations.
Stacks 03EL assumes a morphism of ringed topoi and uses its adjunction. The added
geometric context is already in the parent Transport theorem and matches the previously
reviewed source-side repair. Each changed node records this correction; all its DAG
citers continue to hold in their geometric context. Edge cases I = 0, I = ⊤, A = 0,
n = 0 and empty sites require no separate argument: the proof uses only functorial
adjunction comparisons and the limit projection equation, with no nonzero or nonempty
hypothesis.

Searches were run through msearch.py: LeanFinder for inverse-image modules commuting
with scalar extension returned generic tensor/base-change results; Loogle for
Adjunction.leftAdjointUniq returned an unknown-identifier response; grep for
AlgebraicInverseImage/changeOfRingsComp/tensorAdjunction returned no Mathlib match.
Repository searches located the already proved generic helpers in the finite-pull
existence module, and their complete proofs and signatures were read before reuse.
The original two DAG dependencies do not state the desired comparison in this API.
The shorter proof needs neither of them directly, and no new statement is introduced.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso": "1a2d8773645f8a5ce98068f66ee75794064bd9d9", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetProjectionModelIso": "13466cba03189fe7999116303273ccfe95dd981b", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport": "2223bd18f3236362a7a7b24a0e2584a214e7610b"}, "results": {"Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation": {"hash": "21720de89e0fdac6157776a9a48266594d01cf84", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T10:32:40+0800", "transitive": 0, "version": 1}
```

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
