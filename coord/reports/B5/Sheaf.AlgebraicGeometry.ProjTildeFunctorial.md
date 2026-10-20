## What changed

Retired the zero-hole duplicate `Sheaf.AlgebraicGeometry.ProjTildeFunctorial` using
`deleted.txt`. Redirected the sole consumer, the unclaimed
`Sheaf.AlgebraicGeometry.ProjSheafificationExact`, to the existing proved
`WeilConjectures.AlgebraicGeometry.ProjTildeFunctorial`. Only its public import changes;
its declarations and proofs are verbatim. Updated the attachment of
`lem-sc-p1-proj-tilde-functorial` to the source declaration, including its actual signature.
The proof route and unit realization stay unchanged. No source-library module changes.
Change record: `coord/changes/retire-proj-tilde-functorial-B5.md`.

## Proved and sorry left

Zero original holes; zero holes closed; zero added; zero remaining; zero split off.
The existing source `AlgebraicGeometry.Proj.tilde_functorial` has the same conclusion
without the unused `h𝓜`, `hsmul`, and `hmu` assumptions. A separate compile check derives
the complete old signature by applying that source theorem (compiled successfully, 3.1 s).
`#print axioms` for the source theorem reported exactly `propext`, `Classical.choice`,
and `Quot.sound`. The redirected consumer compiled successfully in 5.6 s.
The consumer contains no
application of `tilde_functorial`, so no application needs adaptation.

## No longer needed

The entire duplicate module `Sheaf.AlgebraicGeometry.ProjTildeFunctorial` is withdrawn.
Its only incoming import, in `Sheaf.AlgebraicGeometry.ProjSheafificationExact`, is replaced
with the source-library import. The duplicate's private helpers `away_exists_fraction`,
`localized_map_smul`, and `tilde_chart_map_exists` are also removed with it; the source
keeps its complete proofs and every declaration verbatim.
No mathematical DAG node is pruned: `lem-sc-p1-proj-tilde-functorial` remains attached to
the source theorem. The standard-open and basis-extension dependencies still support
that proof, so none is claimed unnecessary. No new module or node is introduced.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed item, but the queue actually labels this
module `retire`, and it already has zero holes. The source declaration is not textually
identical: it omits three hypotheses unused by the existing proof. Reading both signatures
and checking specialization shows this is a reusable stronger theorem, so retaining a
second declaration is unnecessary. The DAG previously pointed at that redundant copy.
Stacks Constructions, Lemma 01M7, final paragraph (local `constructions.tex:1221`), states
functoriality of the graded-module identifications; the source proof implements precisely
that route. No mathematical statement, target, definition, or unit route changes.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
