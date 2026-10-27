## What changed

Proved `SheafOfModules.locallyFreeEvaluationBiduality`, preserving its full statement:
evaluation, slice compatibility, arbitrary-map naturality, a global two-sided inverse,
local dual coordinates, and the explicit finite-sum inverse formula.

Added the explicit sectionwise restriction isomorphism `evaluationOverHomIso` and used
it in `bidualOverIso` to avoid costly equality transport through whole internal-Hom
presheaves. The maps are the existing iterated-slice forward and backward maps. This
is a definition implementation repair, recorded in
`coord/changes/locally-free-bidual-restriction.md`; there are no downstream Lean consumers.
Private proved helpers establish the finite-free dual projection and basis expansion.

## Proved and sorry left

Closed the single original hole: `SheafOfModules.locallyFreeEvaluationBiduality`
(node `lem-sf-locally-free-sheaf-evaluation-biduality`). Added zero holes and split off
zero statements. No `sorry` remains in the delivered Lean file. The complete file compiled through
`lcompile.py` without errors or warnings (54.1 seconds in the reported run). The proof uses the
already proved source `isIso_bidual`, the chart criterion for finite local freeness,
internal-Hom-free isomorphism and naturality.

## No longer needed

Removed the unused proof import `Mathlib.CategoryTheory.Sites.LocalProperties`.
The node `lem-sfb-sheaf-cover-local-isomorphism` is not needed by this proof: the
existing source `isIso_bidual` directly yields the global isomorphism after the
chart criterion constructs finite local freeness. Its dependency edge is removed from this node; no module
or declaration is withdrawn. All original public imports remain available because
the statement and definitions use their constructions and small-site instances.
No other declared dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

The existing source API already proves bidual bijectivity on every arrow into a
finite-free slice. Repeating the planned explicit proof of bijectivity is unnecessary;
only the coordinate formula and restriction compatibility need additional calculations.
The supplied `bidualOverIso` computes through a whole-presheaf equality transport;
componentwise restriction avoids that elaboration cost without changing its meaning.
The first delivery attempt timed out before pushing; removing redundant definitional
reductions and temporary elaboration settings yielded the clean 54.1-second compile.
Rank zero uses the same empty-sum basis identity, and there is no uniform rank,
nonempty cover, points or nonzero-ring assumption.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
