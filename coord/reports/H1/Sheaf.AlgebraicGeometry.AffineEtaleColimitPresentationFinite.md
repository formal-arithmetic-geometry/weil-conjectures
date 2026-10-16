## What changed

The source uses finite covering families (Stacks Sites 0A34/09YL and Etale
Cohomology 0EYL). Replaced the sole theorem call to the disputed presentation
wrapper with the completed `exists_affineEtale_finite_colimit_construction` in
`Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement`, explicitly reassembling
its strict-stage and colimit witnesses. The final raw-presieve criterion keeps
`Finite R.uncurry`, as finite-family coverings require. All other clauses remain.

Withdrew the now unnecessary assigned module via `deleted.txt` (brief step 8d),
removed its node's Lean attachment, and updated the parent's proof dependencies.
The withdrawn node's proof record now records the withdrawal rather than claiming
that its original Lean statement and sorry remain.
The parent node makes the finite-family scope of its last clause explicit and
carries a statement-change record checking all five mathematical citers. The unit
route is unchanged. This corrects the attachment's accidental arbitrary-presieve
strengthening; all source-required finite-family comparisons remain.
Change record: `coord/changes/affine-etale-finite-colimit-direct-H1.md`.

## Proved and sorry left

Original holes: one, `AlgebraicGeometry.Scheme.exists_affineEtale_colimit_presentation_finite`
(node `lem-weil-pbc-affine-etale-colimit-presentation`). **Not proved**: its module
is pruned after replacing its only caller by the source-correct finite construction.
Holes closed by proof: 0. Holes removed by pruning: 1. Holes added: 0. Split-offs: 0.
There are no remaining sorries in the delivered Lean file. The parent
`AlgebraicGeometry.Scheme.exists_affineEtaleSite_colimit` is assembled from the
already proved finite construction and its original geometric descent argument.

## No longer needed

- Module `Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentationFinite`, its sole
  theorem `AlgebraicGeometry.Scheme.exists_affineEtale_colimit_presentation_finite`,
  and node `lem-weil-pbc-affine-etale-colimit-presentation` are no longer used.
- The parent removes the proof import of that module and directly imports
  `Sheaf.AlgebraicGeometry.AffineEtaleFiniteColimitConstruction`. No dependency of
  the proved finite construction is pruned.
- The assigned module's private obstruction and finiteness lemmas are removed with
  the module. Their conclusions were diagnostic and were never library interfaces.
  The obstruction remains explained in this report and the change record.

## Where the brief, the DAG or earlier work was wrong

The old Lean final iff required reflection for arbitrary presieves despite finite
stage covers. Equivalence of categories does not preserve finiteness under inverse
images of presieves: infinitely many labelled copies of a source can map to one
source. The W4 construction correctly proves `R covers ↔ Finite R.uncurry ∧ image covers`.
The source begins its colimit-of-sites construction with finite indexed coverings;
for those families this is precisely the needed criterion. No proof is claimed for
the stronger original existential, nor is its universal falsity claimed.

The parent has no actual theorem callers outside its own module. Its only direct
importer is held by XR65519786246dce9c and is unchanged: it imports the parent but
does not use the declaration. All consumers of the withdrawn theorem were adapted
(the sole caller), and no held module was edited. Neither affected node is in the
unit's `realized` lists; the parent remains on the same geometric/site-colimit route.

Validation: a scratch copy type-checked the complete geometric descent prefix to
the single final construction obligation. A second scratch copy type-checked the
new witness assembly from exactly the finite-construction output, leaving only
that existing theorem's statement as the goal. The original labelled-presieve
obstruction and finite-object-fiber criterion compiled independently with only
`propext`, `Classical.choice`, and `Quot.sound` (the scratch file has the expected
private-only-module style warning). These diagnostics add no delivered declarations.

The current retry independently confirmed the consumer list with
`tools/downstream.py --uses` and the absence of an import cycle with
`tools/import_direction.py may`. The local Stacks sources were reread:
`sites.tex` lines 3761–3808 explicitly restrict the colimit construction to finite
index sets, and `etale-cohomology.tex` lines 7335–7399 invoke that construction.
The finite-family correction and all five mathematical citers remain as recorded.

The previous missing-dependency blocker cleared during the ordinary cache refresh.
The complete delivered `exists_affineEtaleSite_colimit` module compiles cleanly in
6.4 seconds. The repository source of the finite construction also compiles cleanly
in 6.5 seconds. The cached pair-category construction now has generalized universes;
the stale-cache diagnosis of the prior attempt no longer applies.
No duplicate declarations, new sorries, timeout increases, or tool changes were
introduced. Validation complete: `deliver3.py H1
Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentationFinite --no-push` printed
`OK (dry run)` and passed compilation, declaration probes and preflight except for
the independent second reading, which is intentionally left to the next worker.
Nothing was pushed. The changed parent and an unchanged copy of its sole direct
importer, `Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishingAux`, were
compiled together in a scratch overlay; both passed cleanly (6.9 and 2.1 seconds).
This checks the consumer against the actual changed parent interface. The parent
node's Lean signature is recorded verbatim from the delivered file.

## Second reading by H1

1. **Signatures and accidental changes — pass.** I diffed the adapted
   `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement` against the repository
   version. Its theorem parameters and all existing declarations are unchanged
   except for the declared finite-family correction in the final conjunct. The
   withdrawn item has no replacement declaration, and no target statement is
   changed. The change record lists the five mathematical citers and their effects.

2. **Proof and axioms — pass.** I compiled the delivered adapted module with
   `python3 /home/ubuntu/weil-launcher/lcompile.py`; it succeeds in 7.9 seconds.
   The deleted item contributes no declarations or sorries. The proof invokes the
   already compiled finite construction and contains no `sorry`, `axiom`, `unsafe`,
   `opaque`, `extern`, or hollow definition. I independently compiled a scratch
   copy with `#print axioms` for both `exists_affineEtaleSite_colimit` and
   `exists_affineEtale_finite_colimit_construction`; each reports exactly
   `propext`, `Classical.choice`, and `Quot.sound` (7.2 seconds).

3. **Statements and split-offs — pass.** No new split-off theorem is delivered.
   The withdrawn wrapper was an incorrect stronger interface: arbitrary raw
   presieves need not be finite after transport. The retained `Finite R.uncurry`
   clause matches the finite indexed covering construction, including the empty
   family. The labelled-presieve counterexample in the report and change record
   checks the edge case; no Mathlib or upstream duplicate is introduced.

4. **Pruning and route — pass.** The sole caller now uses
   `exists_affineEtale_finite_colimit_construction` directly, which is the shortest
   proved route while preserving the unit's strictification and colimit steps. The
   obsolete item import, theorem, private diagnostics, and node attachment are
   removed and listed under `## No longer needed`; the remaining imports compile.

5. **DAG agreement — pass.** The parent node's `proof`, `proof_deps`, and
   `proof_origin` describe the direct finite-construction assembly, and its
   statement-change record records the finite-family correction and all citers. I
   checked programmatically that the recorded Lean statement and the change
   record's Old/New signatures match the source verbatim, and that `proof_deps`
   is exactly the union of the proof steps' `uses`. The
   withdrawn node records its pruned status and has no Lean attachment. The unit's
   `realized` route is unchanged. I reread Stacks Sites 0A34/09YL and Étale
   Cohomology 0EYL locally and searched every Lean source for callers and importers;
   the source scope and consumer list agree with the report. No Lean repair was
   needed. I added this second-reading section and its independent verification
   results; the required dry run then printed `OK (dry run)`.
