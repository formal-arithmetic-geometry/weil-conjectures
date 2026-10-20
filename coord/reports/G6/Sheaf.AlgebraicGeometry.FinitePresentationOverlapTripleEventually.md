## What changed

Retire Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually, the
listed retirement item, in favor of the existing upstream theorem of the same
name. Its only signature difference is omission of the unused Noetherian
instance; the original statement follows directly by specialization.

Migrate the single private proof import in
Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations to the upstream
module. Exactly one import is swapped relative to the current live consumer;
the landed upstream diagonal import is preserved. Reattach
lem-pc-fp-overlap-triple-eventually to upstream and reconcile its
proof steps with the existing canonical-equation plus transport proof.
Change record: coord/changes/retire-fp-overlap-triple-eventually-G6.md.

## Proved and sorry left

The assigned module already had zero local sorries: 0 closed, 0 added, 0 split
off, 0 left. AlgebraicGeometry.finitePresentation_overlap_triple_eventually has
an existing complete upstream proof. The exact original signature is checked
by a proved scratch specialization theorem; both its axioms and the upstream
axioms are checked by the server compiler. No theorem is weakened or replaced
by a hole. The consumer also has no sorries.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/FinitePresentationOverlapTripleEventually.lean.
Remove its consumer's private import of
Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually and replace it
with the upstream import. The duplicate's imports disappear with its body;
its proof dependencies remain needed by the upstream proof. No mathematical
node is withdrawn. All parent DAG citations retain their meaning through the
new Lean attachment; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an obligation repeatedly split off, but the
current assigned item is a zero-hole retirement item in coord/retire-items.tsv.
The upstream library already proves a more general statement with the same
conclusion. The old node proof text described the full defect argument even
though its actual Lean proof already used canonical eventuality and transport;
the delivered proof steps now match that proof.

The returned delivery used a stale consumer and reverted B8's landed diagonal
import, causing `Unknown identifier finitePresentation_overlap_diagonal_eventually`.
This repair starts from the live consumer and changes only its triple-overlap
import on line 14; the upstream diagonal import on line 13 is preserved.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
