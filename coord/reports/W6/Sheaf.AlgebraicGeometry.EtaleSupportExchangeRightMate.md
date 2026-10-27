## What changed

Filled the six theorem proofs in Sheaf.AlgebraicGeometry.EtaleSupportExchangeRightMate.
The inverse comparison uses the existing graph-coherence base-change equation directly.
The common transpose uses the sum-exchange counit equation, and adjunction injectivity
proves the right-mate equation and its counit characterization. Private, proved helpers
identify normalized comparisons with the graph comparison, establish its refinement law,
transport inverse exchange to arbitrary target compactifications, and transpose the
resulting refinement square. All existing signatures and definitions are preserved.
Moved common_transpose before rightMate_eq so the latter can use it.
Local transparency settings let the elaborator compare the existing functor wrappers
without unfolding their geometric constructions.
Added private proof imports for EtaleCompactSupportGraphCoherence, EtaleSumExchangeCounit,
and OpenExtensionProperSupportRange. Updated the existing node proof to this route.

## Proved and sorry left

Closed six holes, all in node lem-pur-etale-support-exchange-right-mate:
AlgebraicGeometry.Etale.EtaleSupportExchange.inverse_comparison,
AlgebraicGeometry.Etale.EtaleSupportExchange.common_transpose,
AlgebraicGeometry.Etale.EtaleSupportExchange.rightMate_eq,
AlgebraicGeometry.Etale.EtaleSupportExchange.counit_characterization,
AlgebraicGeometry.Etale.EtaleSupportExchange.rightAdjointIso_refinement,
and AlgebraicGeometry.Etale.EtaleSupportExchange.rightMate_refinement.
No holes added, none retained in the item, and no split statements.
The proofs use existing stated dependencies; no claim that those dependencies are closed.

## No longer needed

No existing public imports removed. The quasifiniteCompactSupportExact theorem is not
used by these proofs: the support comparison is already fixed by the graph construction,
and its refinement law follows from the normalized support-map compatibility clause.
Removed lem-sfb-quasifinite-compact-support-exact from proof_deps and its obsolete
tool_uses entry. Its public import and statement dependency remain because this packet
does not change the existing public import interface. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition found. The original plan can use graph coherence
instead of extracting an existential support-map comparison for the single-base-change
clause. For refinements, the existential comparison must first be identified with the
specified canonical graph comparison; the proof supplies this using its sheaf and homotopy
normalizations. The original Noetherian hypotheses are retained; IsNoetherian structures
are assembled locally from IsLocallyNoetherian and CompactSpace.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
