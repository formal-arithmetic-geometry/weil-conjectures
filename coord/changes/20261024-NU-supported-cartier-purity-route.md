# Finite-torsion supported Cartier purity: route/data repair, 2026-10-24

The repeated NU runs complete preflight and then stop because Q159 requires a
maintainer route decision. The current item was created on 2026-10-22, after the
2026-10-19 Artin-Gabber pivot. Its arbitrary Noetherian regular-pair statement
needs ordinary etale absolute purity, while the two exact existing inputs were
still excluded as nodes that the older route no longer reached. The mixed
characteristic example Spec(Z[1/ell]), V(p), p != ell rules out substituting the
fixed-field smooth-purity statement. No statement error warrants weakening it.

This is the maintenance route decision requested by Q159: re-admit exactly
lem-per-gabber-regular-pair-purity and lem-per-regular-immersion-class-calculus as
finite-coefficient theorem statements needed by this item. Remove exactly these
two ids from route-pivot-dropped.txt, and the obsolete class-calculus module id
from route-pivot-dropped-modules.txt. Preserve every other exclusion. The old
Artin-Gabber route correction and the no-SGA rule still apply.

Both inputs are reset to unsplit with empty proof/proof_deps and no current
review, split report or tool-use approval. The class-calculus Lean record points
at a module deleted as dead on 2026-10-20; remove that stale attachment and its
reviewed_lean record. No source module is changed or recreated. Their statements,
sources, statement dependencies, Mathlib search history and blueprint provenance
are unchanged. The old splits are deliberately not restored: traversing them
would bring the dropped proof machinery back. The released stage-1 repair notes
make the remaining mathematical work explicit, through the normal worker/review
path. Re-admission is neither a proof nor a claim that their old routes are valid.

For the item, the saved NU seven-step candidate already uses the live
lem-pur-cartier-pair-tensor-addition in place of the third dropped input named by
Q159. Its Step 3 can now cite the two re-admitted existing statements. The item,
its consumers and every target signature remain unchanged. The historical Q159
return remains intact; its request for a route decision on these two citations
is answered here. All other content/review checks still apply.

The item repair note and coord/preferred-upstream/lem-sfb-ramified-cartier-supported-purity.md
tell resumed workers that stale BLOCKED notes and sandbox reports predate this
decision. Reuse the candidate, citations and logged searches; dry-run once to
completion and deliver for independent review. Do not rename/duplicate the inputs,
pretend they are Mathlib leaves, or push an unchanged old input proof.

Before repair: 4f7906866bd7cd5802ed139641d79290f256fc16. Full old JSON records and reviews are available with
git show at that checkpoint. Every changed/new file has a sibling
.maint-NU-supported-cartier-20261024.bak backup (empty means it did not previously exist).
No launcher code, review service, landing tool, queue, claim, concurrency setting
or Lean file is changed by this transaction.

## Q84 dependency correction, 2026-10-24

The "exactly two" scope above is extended by coord/changes/20261024-Q84-gabber-purity-inputs.md. Six direct finite-coefficient ILO XVI inputs and two definition dependencies are now explicitly re-admitted as unsplit statements. Their obsolete proofs, reviews and stale Lean attachments are withdrawn. This supersedes "Preserve every other exclusion" only for those eight listed ids and six exclusively owned module ids. Every other exclusion and source restriction remains. No old alteration or adic proof is restored.

## Q26 class-calculus construction inputs, 2026-10-24

The boundary above is further extended by coord/changes/20261024-Q26-class-calculus-inputs.md: precisely four finite-coefficient construction interfaces are re-admitted as unsplit statements, with their historical proofs/reviews withdrawn. Their statement closure has no additional excluded inputs. The single exclusively owned RegularFlagBlowupGeometry module exclusion is removed; its deleted source is not restored. All unlisted exclusions remain.
