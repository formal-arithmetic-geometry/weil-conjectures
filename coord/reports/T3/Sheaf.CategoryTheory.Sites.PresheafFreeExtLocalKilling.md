## What changed

Repaired upstream review #1428 in
`Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling`:
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` now concludes the
vanishing equation directly, removing `∃ h : ... = 0, True`. Its proof packages the
same E, f, local surjectivity and vanishing equation. The sole caller,
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`, applies it directly;
that caller's signature and visibility are unchanged. No imports changed.

Updated both existing DAG nodes to remove descriptions of the True marker,
and recorded the witness statement correction and its sole DAG citer.
The `statement_change.by` field uses the required `T3 stage 2` schema spelling
for a statement correction performed during this stage-3 repair.
Change record: `coord/changes/presheaf-ext-local-killing-witness-padding.md`.
No external modules require adaptation: downstream.py and a library-wide
name search find the witness's sole caller in the assigned module itself.

## Proved and sorry left

Holes closed: none (zero baseline holes). Holes added: none. Sorries left: none.
The repaired theorem `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness`
and unchanged-signature theorem `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`
have complete proofs. The two private helpers remain completely proved.
This is the assigned statement-padding repair, not a new proof or decomposition.

The old and new conclusions are logically equivalent for all sites and presheaves:
extract h from the old existential proof marker; conversely pair the vanishing
proof with True.intro. This includes x = 0, P empty and the zero sheaf, without
changing q > 0, the sheafification assumption or any universe. No definitions
or target statements change.

## No longer needed

None. No imports, modules or mathematical dependencies were pruned. Only the
vacuous proof marker and its destructuring are removed; the existing effacement
and explicit generator-lifting route remain intact.

## Where the brief, the DAG or earlier work was wrong

The earlier worker treated this as a stale zero-sorry assignment and delivered
an unchanged file. The current brief explicitly identifies the upstream #1428
padding repair, so a real interface correction is required despite zero sorries.
The witness node and the caller's proof description unnecessarily recorded True
as mathematical content. Both now record the actual vanishing conclusion.
The unit route is unchanged; the witness node's sole citer still holds.

## Second reading by T3

1. Compared the delivered module with the repository version. Existing declaration
signatures are unchanged except for the declared correction to
`exists_presheaf_ext_local_killing_witness`; the public local-killing theorem and
all helper declarations retain their interfaces. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds without warnings or errors.
Axiom checks for both public theorems report only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`. No definitions contain `sorry`, and no forbidden
commands occur. Verdict: pass.

3. The only interface correction removes a vacuous `True` marker while retaining
exactly the vanishing equation and all hypotheses. The two conclusions are
logically equivalent, including degenerate sites and presheaves. The correction
has a change record, node metadata, source, and citer. No duplicate declaration
was introduced. Verdict: pass.

4. The proof follows the existing effacement, locally-surjective image, cover-lift,
and Ext composition route. The unit route is preserved; no proof dependency or
import is unused, so no pruning is required. Verdict: pass.

5. DAG proof steps and dependencies match the Lean proof: the witness node records
the direct vanishing conclusion, and the caller applies it directly. The unit's
realized route remains unchanged. Verdict: pass.

Changed in this second reading: appended this review only; no Lean proof or DAG
changes were needed.
