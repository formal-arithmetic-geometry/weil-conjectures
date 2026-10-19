# NH: lem-fd-inversion

## Files written

- `dag/nodes/sec-fourier-transform/lem-fd-inversion.json`: existing item split into three proof steps; statement and hypotheses retained; blueprint ancestry updated to `main-20261015`; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotes for every cited node in every step.
- `sk-thm-inversion.json`: realized statement and proof-step bindings recorded for the key unit.
- No Lean files were written and no compiler, Lake, or build command was run.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and the read-only master source for the item id, Fourier inversion names, and the blueprint names. The source declaration `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_inv` is specialized to finite coefficient affine spaces and has hypotheses (`Finite`, invertible exponent, normalized Tate twist, compactification) that are not the item's constructible Weil-complex statement; `...comp_self` is likewise specialized. Neither is an exact attachment.

## WANTED

None.

## Issues found and repaired

The imported proof was one long paragraph and cited the generic functor package without isolating the diagonal-kernel identity. I split it into: (1) composition and convolution, (2) the diagonal kernel acting as the identity using the package's projection formula and compact-support composition clauses, and (3) shift cancellation and the anti-diagonal/same-character calculation. The conclusion and all hypotheses remain unchanged. The generic package is an off-unit tool and is declared in `split_report.tool_uses`.

I searched the whole DAG and both blueprint snapshots for a diagonal-kernel identity node; none states this calculation, so no duplicate node was created. The item is not a Mathlib leaf: the required searches found only analytic Fourier-transform APIs or generic category isomorphisms, not sheaf-theoretic Fourier--Deligne inversion.

## Not duplicates

No new nodes were created. Searches for diagonal-kernel identity, kernel-transform identity, and anti-diagonal transform found only this item and its unit proof; there is no existing node with the auxiliary statement.

## Mathlib searches

I ran LeanFinder, Loogle, Mathlib grep, and LeanSearch twice with the exact queries recorded in the item's `mathlib_searches` and in `searches.jsonl`. LeanFinder/LeanSearch returned analytic Fourier or generic category declarations; Loogle's compound identifiers were reported unknown; grep found no Fourier--Deligne inversion declarations. These are recorded as no-match results (with the Loogle diagnostics preserved).

## Review by NH

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `coord/dag-sync.md`, the B--E delivery-error checklist, the chapter and unit records, the imported item, and the current `main-20261015` blueprint proof. I also read the full statements of `lem-fd-kernel-composition`, `lem-fd-convolution-kernel`, and `prop-functor-package` before writing the steps and quotes.

Step 1 uses exactly the composition statement's clause that the inverse-character composite has kernel `\\mathcal K_{\\psi^{-1}}\\ast\\mathcal K_\\psi` and shift `[2r]`, and the convolution statement's diagonal and anti-diagonal kernel formulas. Step 2 uses the package's explicit compact-support projection formula and its compact-support composition law with identity equations. Those clauses provide the two non-elementary functorial facts used in the diagonal calculation; the equation `s_2\\circ\\Delta=\\operatorname{id}_V` is the defining diagonal identity. Step 3 uses the convolution node again for the twist, shift, and anti-diagonal kernel, and the same package clauses for the repeated identity-kernel calculation. Every `uses` entry is therefore supported by a verbatim quote in `citations.json`.

I checked the edge cases relevant to the statement: rank `r=0` gives zero shift and zero Tate twist; the anti-diagonal is the diagonal followed by inverse addition; and the shift cancellation is formal in the triangulated category. The specialized source declarations were checked for their extra coefficient and compactification hypotheses and were correctly rejected as attachments. No statement was weakened, no unsupported hypothesis was introduced, no cycle is present, and no proof step exceeds 2000 characters.
