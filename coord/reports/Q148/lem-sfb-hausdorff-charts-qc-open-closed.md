## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-hausdorff-charts-qc-open-closed.json`: statement, split; four proof steps, statement unchanged, no new hypotheses.
- `dag/nodes/sec-six-functors-basics/lem-sfb-compact-subset-hausdorff-closed.json`: statement, Mathlib leaf; `IsCompact.isClosed`, `Mathlib/Topology/Separation/Hausdorff.lean:592`.
- `citations.json`: five verbatim statement quotations, one for every cited node in every step.

Attachments: none for the item. The existing `pqf-lem-qs-intersection-qc` is already attached to `AlgebraicGeometry.Scheme.isCompact_inf_of_quasiSeparatedSpace`, `lean/WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean:73`; it is reused without modification.

WANTED: none.

The item was statement-only. I retained its statement, original citations, searches, source and blueprint chain. No repair order exists for this item. Whole-project Lean searches for the blueprint id and Hausdorff/chart/closed-open-immersion notions did not find an exact project declaration; the existing compact-intersection declaration covers only step 1. The item's existing Mathlib search record was retained, and today's actual searches added. LeanSearch now answers, while its inherited 2026-10-22 unavailable result remains historical. The whole-item hits give pieces of the proof rather than its complete conclusion.

I read `literature/stacks-project/properties.tex`, Tag 0CKV, `lemma-dimension-zero`, especially the proof of (1) implies (2), and `literature/stacks-project/topology.tex`, Tag 08YB, `lemma-quasi-compact-in-Hausdorff` (1). The statement generalizes the local Hausdorff argument in 0CKV and was already imported in that generalized form: no dimension-zero assumption is used or added. The proof does not infer global Hausdorffness before proving closedness. It proves the complement open chart by chart. The closed subscheme is the original open subscheme, not a reduced or newly chosen structure.

No source error or disputed statement was found. Nothing mathematical remains unfinished at this level: the one new subsidiary node is an exact Mathlib leaf. No Lean file was written and no compiler/build tool was run.

## Searches and blueprint route

Before creating the leaf I searched all DAG titles and statements for compact subsets closed in Hausdorff spaces and searched `08YB`, `lemma-quasi-compact-in-Hausdorff`, `IsCompact.isClosed`, and closed-image open-immersion phrases throughout the DAG. Blueprint searches were `Hausdorff`, `08YB`, `closed image`, `Hausdorff affine`, `quasi-compact subset`, `compact subset`, and `Intersections of quasi-compact opens`. The latter identifies the existing intersection node, which is reused; none states the new general topological leaf. Whole-project Lean searches found related constructible-topology lemmas, not an attachment for this general result.

All Mathlib searches were run through msearch.py and their unmodified result summaries are in searches.jsonl and the node records. For the new leaf, LeanSearch and LeanFinder returned `IsCompact.isClosed`, grep located line 592, and I read its actual declaration and hypotheses. Loogle `IsCompact, IsClosed` returns related intersection/closed-subset compactness lemmas on its first page, not the desired implication; the other services give the exact match. The new node contains only a self-contained statement, no proof or postponed subclaims, and defines Hausdorffness and quasi-compactness inline. Its status is mathlib, not unsplit.

The item has no imported blueprint ancestor: `blueprint_refs.py ancestor` prints None. I preserved this null ancestor and its original via chain; the new leaf prepends this item to that chain. Both from.place fields identify the precise Tag 0CKV sentence served and its role below paragraph (3) of `lem-sfb-field-profinite-galois-site`. The unit and chapter records were read and unchanged. The generic intersection node is in the Nagata unit, which this chapter uses; its Lean audit is closed and it is the exact tool for the local overlap argument, so no replacement of the unit's route is involved.

## Not duplicates

lem-sfb-compact-subset-hausdorff-closed vs lem-sfb-qcqs-zero-dimensional-affine: the existing node concludes affineness of a quasi-compact quasi-separated scheme with closed points; its source mentions 08YB in its proof, but its statement does not give compact-subset closedness for arbitrary Hausdorff spaces.
lem-sfb-compact-subset-hausdorff-closed vs lem-sfb-hausdorff-charts-qc-open-closed: the item is a local-to-global scheme result, including the original closed immersion and requiring quasi-separatedness; the leaf is a pure topology lemma on a single Hausdorff ambient space and does not assert any clause about schemes or their sheaves.
lem-sfb-compact-subset-hausdorff-closed vs lem-weil-pbc-compact-hausdorff-bijection: the existing node makes a continuous bijection from a compact space to a Hausdorff space a homeomorphism; it does not state closedness of a subset of an arbitrary Hausdorff ambient space.
lem-sfb-compact-subset-hausdorff-closed vs lem-sfb-compact-hausdorff-surjection-quotient: the existing node concludes a quotient-map property; it does not state compact subsets are closed.

## Review by Q148

I reviewed the actual statements of all five cited nodes against each use. In step 1, `lem-weil-pbc-affine-scheme-qcqs` explicitly states affine schemes are quasi-compact, so it applies separately to every chart V_j without requiring a finite cover. `pqf-lem-qs-intersection-qc` explicitly takes two quasi-compact opens of a quasi-separated scheme. Its hypotheses are X quasi-separated from the item, U quasi-compact from the item, and V_j quasi-compact from the first citation. It does not say the intersection is affine, and the proof does not claim that. The topology of the intersection is the same subspace topology inside V_j, by the definition of an open subscheme. These two non-elementary facts are cited as statements, not extracted from their proofs.

In step 2, the new leaf states exactly that a quasi-compact subset of a Hausdorff space is closed; the ambient space here is V_j, for which Hausdorffness is an explicit assumption. The leaf agrees with Tag 08YB (1), not the stronger neighbourhood-separation assertion (2). I read Mathlib's `IsCompact.isClosed` at line 592: its only relevant assumptions are T2Space and IsCompact, with no CompactSpace assumption on the ambient space and no Nonempty assumption. Thus it is an exact leaf. It is a genuinely reusable theorem, not a restatement of a scheme clause or an elementary consequence of the existing cited statements.

Step 3 is elementary: the complement of U is the union of V_j minus U because the V_j cover X; every member is open in X since it is open in the open chart. This is valid for an infinite family and for the empty cover of the empty scheme. It needs no additional separation theorem or local-to-global geometric criterion.

In step 4, I read `def-weil-open-immersion` and `def-weil-closed-immersion`. The former identifies the original structure sheaf with the restriction; the latter requires a closed embedding and surjectivity of O_X to i_*O_U. The map is the original subspace inclusion, so closedness from step 3 gives the closed embedding. Surjectivity is proved explicitly: for each open W the two disjoint opens W intersect U and W minus U cover W; gluing any section on the first with zero on the second lifts it. Sheaf gluing is part of the definition of the structure sheaf. This two-piece gluing is elementary and needs no new node for the closed-image open-immersion criterion. The explicit lift also prevents a hidden change of scheme structure.

I tested the leaf on E empty, T empty, and a noncompact Hausdorff T (for example the real line), and the item on the empty scheme, empty U, an affine Hausdorff spectrum, and an infinite disjoint union of spectra of fields. In the last case X need not be quasi-compact but each compact open meets only finitely many components, consistent with the argument. I did not remove quasi-separatedness or infer compactness for an arbitrary open intersection. No finite-type, Noetherian, reducedness or finite-cover assumption appears. No proof step exceeds 2000 characters. All citation quotes are copied verbatim from the cited statements; there are no undefined new notions or double-escaped TeX. The principal corrections to the initially empty proof were to expose the existing compact-intersection citation, add exactly the general Hausdorff compactness leaf, and write both the complement and section-lifting arguments instead of leaving them as implicit criteria.

The first dry run required an explicit definition-node citation in the new leaf despite the inline definition. I added `def-weil-pbc-quasi-compact-scheme`, whose statement defines quasi-compactness for arbitrary topological spaces, not just schemes, and refreshed the verbatim quotation. I also made the Loogle verdict distinguish its related first-page hits from the exact match found by the other searches.
