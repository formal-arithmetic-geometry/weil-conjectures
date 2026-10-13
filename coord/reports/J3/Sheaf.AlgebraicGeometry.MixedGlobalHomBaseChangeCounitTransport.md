## What changed

Ported the proved single-universe naturality and cancellation argument to the mixed
comparisons in MixedGlobalHomBaseChangeCounitTransport. The existing theorem signature
is unchanged. Added proof-only imports of MixedGlobalHomBaseChangeExchange and all of
GlobalHomAdjunctionIso (for its pinned tensor-Hom API), and a private generic pullback-mate naturality proof and two specialized naturality proofs.
The exchange step is isolated in a new module; it has neither the counit-square
hypothesis nor the invertibility hypothesis and is strictly the first step of the
original argument. Updated the transport node to match this reduction.

## Proved and sorry left

Closed AlgebraicGeometry.mixedGlobalHom_baseChange_counit_transport, with its
signature unchanged and no sorry remaining in the item module. Its private
homMap_comp, pullbackMate_naturality, directImage_naturality and
pullback_naturality helpers are fully proved.

Added one hole: AlgebraicGeometry.mixedGlobalHom_baseChange_exchange, node
lem-sc-mixed-global-hom-base-change-exchange. This is a decomposition (one hole
closed, one added), not a net proof. The exchange identity is strictly the first
step; the transport theorem proves naturality, counit-square substitution and
inverse cancellation from it.

Validation: lcompile.py --all compiles the complete sandbox (transport: 32.3 s).
The deliver3.py --no-push dry run printed OK and passed preflight except for the
second reading, which belongs to the second reader. Nothing was pushed.

## No longer needed

No existing import removed: both public imports remain needed for the statement.
No planned mathematical dependency is pruned: the new exchange node carries the
first step of the original DAG, including the tensorator, Leray, direct-image Hom,
and canonical base-change dependencies.

## Where the brief, the DAG or earlier work was wrong

The existing exchange theorem uses a common localization universe and the original
comparison choices, so it does not directly fit this statement. The mixed exchange
node isolates the missing mixed-universe version. Its zero-object and empty-scheme
cases reduce to identities of zero maps; there is no cancellation in its statement,
so no invertibility assumption is needed. The unit route is preserved.

## New nodes

lem-sc-mixed-global-hom-base-change-exchange states precisely the first exchange step
of the original transport proof, before the counit-square substitution and inverse
cancellation. Its source and complete proof in words are the final comparison
diagrams of Stacks Tag 0AA8 with the canonical mate comparisons of Tags 08I3 and 0B6I.

The previous shared-artifact blocker was resolved locally by compiling unchanged
sandbox copies of MixedHomDirectImageComparison and MixedGlobalHomAdjunctionIso
in import order. These copies are byte-identical to the library sources and are
build inputs only: deliver3.py omits them from the delivery diff. No dependency
statement, definition, proof, visibility or import was changed; there are no
forced adaptations.


## Second reading by J3

1. Compared every delivered module with the repository. The existing transport
   theorem signature is byte-for-byte unchanged. The two local dependency copies
   are byte-identical build inputs, not adaptations. No change record is needed.
2. Compiled all four sandbox modules successfully through lcompile.py. A scratch
   probe with #print axioms reported only propext, Classical.choice, Quot.sound,
   and sorryAx. The transport and its four private helpers are fully proved. The
   only new sorry is the named exchange theorem; no forbidden declaration or
   hollow definition was added.
3. Read the new exchange statement, docstring, and node against the canonical
   tensorator, evaluation-mate direct-image comparison, normalized Leray, and
   pullback definitions. It is the first step of the old argument, without its
   arbitrary t/e/e' maps, square hypothesis, or inverse cancellation. It is a
   true compatibility identity, not a renamed transport theorem. For zero input
   objects or an empty scheme the relevant Hom maps are zero; for identity
   pullbacks the equation is ordinary evaluation naturality. The mate argument
   uses no flatness, properness, or invertibility of beta. Local and Mathlib
   searches found only generic naturality lemmas and common-universe exchanges;
   none directly states this mixed-universe identity.
4. Read the proof top-down: exchange, postcomposition, functorial cancellation,
   counit-square substitution, then comparison naturality. All added imports are
   proof-only; no unused import was found. The old tensorator and base-change
   dependencies move to the exchange node, and no closure module is pruned. The
   unit route is preserved.
5. Compared both nodes with the Lean declarations and proof. The new node has
   its source, proof, dependency union, origin, searches, creation, blueprint,
   chapter, unit and verbatim Lean statement. One hole is closed and one
   strictly smaller first-step hole is added: this is a decomposition with net
   zero holes closed.

Second reading changed only this report: added the review and clarified that the
old direct dependencies remain through the exchange node. No Lean proof,
statement, definition, import, or node needed repair.
