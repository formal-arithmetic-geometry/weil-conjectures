## What changed

Proved `AlgebraicGeometry.Etale.presentation_pullback_coherence` directly from the
inverse-image unit and associativity laws in
`WeilConjectures.SixFunctors.BaseChange.Pasting`. All three complex-map equalities
are checked degreewise. Four proved private helpers express equality transport
and cancellation for arbitrary functors and categories, avoiding costly concrete
inverse-image substitutions. Explicit component goals replace rewrite-generated
transport terms. The statement and its docstring are unchanged.

## Proved and sorry left

Closed the one hole: `AlgebraicGeometry.Etale.presentation_pullback_coherence`.
No sorry remains in the item and no holes or public statements were added.

## No longer needed

Removed the direct proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; its declarations are
available through the existing public import and the coherence proof import.
No DAG proof dependency or target-reachable module is pruned: the proof follows
the original unit, associativity, and cone argument.

## Where the brief, the DAG or earlier work was wrong

The earlier timeout came from concrete equality-substitution proof terms: the
original unit helper alone spent about 45 seconds in kernel checking. Abstracting
that elementary transport before specialization reduced its compilation to
2.6 seconds. The direct proof compiles without splitting any statement or module.

## Second reading by P1

1. PASS: compared the delivered module with the repository version using diff and
   the delivery declaration parser. The existing public theorem signature and its
   docstring are byte for byte unchanged. No definitions, public statements or
   change records were added; the four additional declarations are proved private
   helpers used only by the proof.
2. PASS after repair: the full scratch copy of the repaired module compiled cleanly
   in 46.8 seconds. The actual module also compiled cleanly in 55.0 seconds
   against the published build after clearing a stale sandbox overlay. Its target axiom check shows exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Separate checks of all four private helpers
   show only subsets of those axioms. The delivered source has no sorry or forbidden
   declarations, and introduces no data chosen from an unproved theorem.
3. PASS (no splits): no new public statement, node or hole was introduced. The unit
   transport helper uses equality induction and the established left unit law;
   the two cancellation helpers follow from the inverse equations of isomorphisms,
   including identity isomorphisms. No nonemptiness or cone limit condition is used.
4. PASS: searched the local Sheaf and upstream library for unit, associativity and
   component coherence under alternative names, and ran msearch grep for inverse
   image identity comparison and cone associativity. The upstream component law
   in BaseChange.Pasting is already used directly. CompatiblePullbackSheafSystem
   assumes a preorder and does not cover this arbitrary small-category theorem.
   Both remaining imports are needed: Transport supplies presentationIdentityMap
   to the statement; Pasting supplies the proof's component associativity law.
   The removed Defs import was proof-only and is transitively available. The sole
   old proof dependency, lem-weil-pbc-inverse-image-composition, remains used; none
   is pruned. The unit sk-prop-h2 realized record is unchanged, and no unit step is
   bypassed by this component calculation.
5. PASS: the existing node's proof and proof_deps describe exactly the degreewise
   unit, associativity and cone cancellation proof. Its documented source remains
   the origin of the argument. No node metadata correction is needed.

Changed only the proof: removed the redundant initial `dsimp only`. The submitted
version timed out twice at 60 seconds. Isolating the three branches showed that
concrete identity transport dominates kernel checking; the helpers and other two
branches compile quickly. Keeping the original let bindings and letting the
conjunction constructor reduce them avoids the redundant simplification proof
term. The complete repaired proof and its target axiom check then passed. No new
helper or statement from the scratch experiments is delivered.

The sandbox contained a stale `.lbuild` from earlier experiments, including a
locally compiled Transport dependency and obsolete split modules. Moved it under
scratchpad so the delivered module is checked against the published library.
This cache cleanup is local only. Timing varies substantially under concurrent
machine load: some retries hit the unchanged 60-second limit. Experiments with
alternative generic lifting and component simplification were slower and were
not delivered; no compilation limit or tool was changed.
