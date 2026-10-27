## What changed

Moved the unchanged canonical constructions and all already proved helpers from
Sheaf.Paper.PurityDiagonalSectionPasting into
Sheaf.Paper.PurityDiagonalSectionPastingData, publicly re-exported by the original
module. The first conjuncts of openPairProperties and openMiddleProperties now use
Scheme.pullback_map_isOpenImmersion directly instead of broad instance search;
profiling identified those searches as the slow steps. Their statements and
every definition body are unchanged. The final theorem is assembled from independent
global, open-restriction and
affine-coordinate claims. DoubleDiagonalSectionIdentifications and
AffineDifferenceTowerFactorization change only their direct statement import to the
shared data, removing the obstruction to using them as proof dependencies.

The data module retains the full collection of heavy definitions and geometry proofs;
it was separated to remove the proof-import cycle, not to divide a slow compile.
The compile-time repair is the pair of direct open-immersion theorem applications.

The interface relocation is recorded in
coord/changes/E9-diagonal-section-pasting-shared-data.md. No source-library or target
signature is changed. The unit route and every canonical map are preserved.
The definition node def-pur-diagonal-section-pasting-data owns the relocated
declarations; the original node retains the assembly theorem's attachment.

## Proved and sorry left

Closed the original body hole of
WeilConjectures.PurityFiniteSetting.DiagonalPasting.diagonalSectionPasting by Lean
conjunction and universal introduction, with the Noetherian instances derived from
the given structure morphism. This is a decomposition, not a net proof gain:
one original hole is replaced by three proper, independent parts, net -2.

New remaining holes (each exactly `:= by sorry`):

- WeilConjectures.PurityFiniteSetting.DiagonalPasting.diagonalSectionPastingEquation
  (lem-pur-diagonal-global-equation).
- WeilConjectures.PurityFiniteSetting.DiagonalPasting.diagonalSectionPastingOpen
  (lem-pur-diagonal-open-restriction).
- WeilConjectures.PurityFiniteSetting.DiagonalPasting.diagonalSectionPastingChart
  (lem-pur-diagonal-affine-chart-equation).

The original item and shared data have zero holes. All previously proved helpers stay
proved. There is no sorry in a definition. The new parts each omit the other two
conclusions; none restates the original ModelStatement or Statement under another name.
Validation: remote `lcompile.py --all` compiled all seven modules successfully.
The delivery command's compilation and axiom-probe stages also passed.

## No longer needed

No mathematical node or module is pruned. The eight declared assembly dependencies remain
needed in the proof plans of the three new nodes. Their prior appearances in the parent
proof move to the appropriate proper part; they are not declared unnecessary.

The original item's public statement imports and private helper-proof imports move to
the data module and remain re-exported or used there. The two adapted modules no longer
import the final assembly theorem: they use only the canonical definitions, now imported
from PurityDiagonalSectionPastingData. No declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The declared double-diagonal and affine-factorization dependencies imported the item
itself for its canonical map definitions. Thus a direct proof import as proposed in the
brief would close a Lean module cycle. The data relocation fixes that interface issue.
The remaining mathematical work is the explicitly recorded final map assembly; the
component pasting/locality and coordinate declarations are available but require
transport between their normalizations and the item's fully specified formulas.

The three conclusions are separated along the DAG's existing three assembly steps.
Each new theorem has a source, full proof in words, exact Lean attachment, and its
own node. Empty schemes, empty opens and zero coordinate blocks add no assumptions.

## New nodes

def-pur-diagonal-section-pasting-data: the already constructed canonical objects,
comparison maps and equality propositions, relocated to
Sheaf.Paper.PurityDiagonalSectionPastingData. This definition node carries zero holes
and asserts none of the three remaining equality claims. Its Lean declarations are
removed from the original node's declaration list and attached here.

lem-pur-diagonal-global-equation: only the global equality alpha_(gf) kappa =
sigma (alpha_f tensor f^*alpha_g), using double-diagonal restrictions and smooth tensor
pasting. Its new module is Sheaf.Paper.PurityDiagonalGlobalEquation.

lem-pur-diagonal-open-restriction: only the seven naturality squares of OpenEquation,
using normalized target/source restriction and finite-expression locality. Its new
module is Sheaf.Paper.PurityDiagonalOpenRestriction.

lem-pur-diagonal-affine-chart-equation: only the equality on one given affine chart
triple, using the translated Cartesian tower, normalized etale tensor comparison and
input/output section identifications. Its new module is
Sheaf.Paper.PurityDiagonalAffineChartEquation.

Each is in sec-smooth-purity/sk-thm-smooth-purity, follows the same Step 1 of the current
blueprint, and retains the original argument's dependencies. Searches found component
categorical and scheme lemmas, but no existing final assembly theorem.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
