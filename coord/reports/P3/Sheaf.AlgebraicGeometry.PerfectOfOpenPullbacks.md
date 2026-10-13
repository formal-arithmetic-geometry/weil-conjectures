## What changed

Proved `AlgebraicGeometry.perfect_of_open_pullbacks` in
`Sheaf.AlgebraicGeometry.PerfectOfOpenPullbacks`. Its existing signature and
module and declaration docstrings are byte-for-byte unchanged.

The proved private helper `open_pullback_iso` compares derived tensor pullback
along an open immersion with exact localized restriction followed by
`Scheme.Modules.overEquiv`. It identifies tensor pullback with ordinary
restriction by uniqueness of left adjoints, then uses uniqueness of left derived
functors. The main proof chooses the open from the hypothesis and applies the
already proved `Scheme.local_perfect_of_openRestriction_iso` to this comparison.
That theorem transports the local strictly perfect model to an ambient open.

Added two proof-only imports: Mathlib's
`CategoryTheory.Functor.Derived.PointwiseLeftDerived` for
`Functor.isLeftDerivedFunctor_of_inverts`, and
`Sheaf.AlgebraicGeometry.OpenPerfectModelTransport` for the existing model
transport theorem. Updated the item's node proof and proof dependencies to name
`lem-sc-open-perfect-model-transport`; no interface, definition or unit changed.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.perfect_of_open_pullbacks`
(node `lem-pc-perfect-of-open-pullbacks`). The private helper is fully proved.
No sorry remains in the delivered module; no holes were added or split off.
This is one hole closed, not a decomposition. Imported dependencies are used as
provided; this does not claim that their transitive holes are closed.

## No longer needed

None. Both original public imports remain necessary for the statement, and both
original proof dependencies remain used. No old dependency node or module is
pruned. The second reading replaced the duplicated model transport construction
with its existing proved library theorem, imported only for the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The first proof repeated the existing proved
`Scheme.local_perfect_of_openRestriction_iso`; its report mentioned existing transport proofs but missed reusing this public theorem. The second reading
uses this shorter route and records the additional existing node dependency.
The unit `sk-thm-picard-semicon` and its realized fields are unchanged. The reused
transport lemma is an auxiliary tool from `sk-thm-picard-duality`, not a bypass of
any realized unit statement or step.

## Second reading by P3

1. Compared the sole delivered Lean module with the repository version using
   diff, and checked the existing theorem signature byte-for-byte. Verdict:
   unchanged statement, visibility, definitions and existing docstrings; no
   change record required. All new imports are proof-only.
2. Compiled the original and the shortened module locally without warnings.
   Scanned for sorry and prohibited declarations. A scratch copy with
   `#print axioms` checks the private comparison, the target theorem and the
   reused transport theorem. Verdict: no local sorry or forbidden declaration;
   the comparison and target depend only on the three standard axioms and
   upstream `sorryAx`; the reused transport theorem also depends on upstream `sorryAx`.
   The only choices used by the comparison come from adjunctions or the left
   derived universal property, which determine their objects up to the natural
   isomorphisms used downstream. The transport theorem constructs its model by
   applying an explicit exact equivalence to the given local model.
3. No split-off statement or new public statement. Read the existing transport
   theorem and its node: it preserves the degree bounds, finite free comparison
   and retract equations and uses the restriction-composition isomorphism to
   transport the representing isomorphism. Empty schemes are vacuous, empty
   opens contain no point, and zero models, rank zero and top opens need no extra
   assumption. Verdict: the private comparison and existing transport theorem
   are true and sufficient. Independent LeanFinder search for exact restriction
   computing derived tensor pullback found only underived restriction and
   adjunction tools; rg over Sheaf found the reusable transport theorem, while
   upstream WeilConjectures had no equivalent perfect-locality theorem.
4. Reviewed from the target downward. Verdict: replaced roughly one hundred
   lines of repeated transport proof with the existing proved theorem, retaining
   the necessary open derived-pullback comparison. No old dependency was made
   unused; the No longer needed list is complete. The unit route is kept.
5. Compared the node's proof, proof_deps and proof_origin with the Lean and read
   both original dependency nodes and the existing transport node. Verdict:
   the first step still chooses a local model; the second now explicitly uses
   `lem-sc-open-perfect-model-transport` after exact derived restriction.
   Updated only the existing node's proof and proof_deps. No new node is needed.

Second reading changed the main proof to reuse the existing proved transport
lemma, added its proof-only import and DAG dependency, and corrected this report.
