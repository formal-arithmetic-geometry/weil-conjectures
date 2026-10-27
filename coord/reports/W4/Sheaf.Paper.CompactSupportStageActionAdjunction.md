## What changed

Proved `WeilConjectures.LocallyFiniteAdicCompactSupport.compactSupport_stageAction_isLeftAdjoint`
in `Sheaf.Paper.CompactSupportStageActionAdjunction` without changing its statement.
The finite right functors and invertible scalar comparisons are taken from the supplied
coefficient construction. Private proved helpers transport adjunctions and comparisons
along the recorded functor equalities and derive right stage coherence and unit
compatibility from counit compatibility and the existing left stage coherence.
A private helper carries out the finite-stage assembly over an abstract coefficient field,
so specializing to the concrete algebraic closure does not repeatedly unfold its instances.
Added the proof-only import `Sheaf.CategoryTheory.StageSystemAdjunction` and applied
its adjunction descent. Updated the item's node to record this argument.
The complete proof passed the required remote single-file compile in 43.5 seconds;
the delivery tool reruns compilation and the packet checks.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.LocallyFiniteAdicCompactSupport.compactSupport_stageAction_isLeftAdjoint`
(node `lem-sf-compact-support-stage-action-adjunction`). No holes were added or split off;
no `sorry` remains in the delivered Lean module. All private helpers are proved.
This proof uses the supplied coefficient construction and the existing stage-system API;
it does not claim to close holes in those dependencies.

## No longer needed

The declared proof dependency `lem-sf-constructible-exceptional-coefficient-coherence`
(module `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence`) is not needed by
this proof: right stage coherence follows by transposing `S.system.coh` and the
coefficient comparison counit equations. No explicit import of that module was added.
It remains available wherever other proofs use it. No existing imports, declarations,
or modules were removed. All other declared proof dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The previous plan required the separate coefficient-coherence theorem to construct
the right stage morphism. Its right cocycle is unnecessary here because the supplied
left stage morphism already contains precisely the required associator coherence.
This argument also avoids comparing balanced tensor associators a second time.
No mathematical statement, definition, or unit route was changed.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
