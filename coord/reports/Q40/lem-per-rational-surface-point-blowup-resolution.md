# Q40: lem-per-rational-surface-point-blowup-resolution

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-rational-surface-point-blowup-resolution.json`: split the item into eight steps, preserving its statement and statement dependencies. Appended this worker's actual Mathlib searches to its inherited records.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-ordinary-point-blowups-globalize.json`: one new statement-only lemma, unsplit; no Mathlib match. It is the ordinary point-blowup localization/gluing tool, not a resolution theorem.
- `citations.json`: one verbatim statement quotation for each step/node citation (20 entries).
- `searches.jsonl`: unedited log made by msearch.py. Both phrasings and all four search modes were read; the successful searches returned only unrelated local-ring, scheme, smoothness, normalization, DVR and elliptic-curve declarations. No returned declaration supplies either theorem.

## Attachments

None. I searched WeilConjectures in the read-only slopmaster2 source for the item tag, rational singularity, rational double point, Gorenstein and ordinary point-blowup globalization. No matching project theorem exists. The compactification localization hits concern affine blowup charts and do not assert this item or the new lemma. I also checked the exact upstream master reference for the surface keywords, without treating any master sorry as a proof.

## WANTED

None. All sources needed for this split are present in literature/stacks-project.

## Corrections and retained route

No statement dispute and no mathematical change to the item. Its explicit H^1 condition is rationality in Tag 0B4N once Nagata is proved. In particular, the base C need not be a domain and B need not be complete. The existing Gorenstein-blowup node already incorporates dualizing-complex existence from Tag 0BFR, so no new dualizing assertion is needed here. I did not use full surface desingularization or normalized-refinement, either of which would create a circular route through this item.

The current chapter and unit records and the inherited blueprint ancestry were read. This is a technical input below the dimension-normalized duality step of lem-per-artin-gabber-affine-curve, not the unit's key theorem. It retains the Gorenstein-then-double-point route of resolve.tex 0BGM. Generic off-unit algebra, dimension and blowup tools are declared in split_report.tool_uses; no chapter or unit route changes.

## Not duplicates

lem-per-local-ordinary-point-blowups-globalize vs lem-per-local-normalized-blowups-globalize: the existing node produces normalized blowups and states only endpoint local-ring comparisons. The new node produces ordinary blowups without normalization, matches all intermediate stages and therefore preserves singularity of the prescribed centers. Ordinary normal local inputs alone do not let us read these conclusions from the existing node's statement. Its source is 0BFY rather than 0BFZ; both use the fibre comparison 0BFX. The new node is generic in the dimension and in the given towers, asserts no existence of a resolution and assumes neither rationality nor Gorensteinness.

Whole-DAG statement and source searches (0BFY, ordinary/globalize, point blowups with local schemes) and blueprint_refs.py searches for 0BFY, blowups local, sequence blowups, rational singular and rational surface found no duplicate. Ancestor search gives lem-per-artin-gabber-affine-curve, retained with the full inherited via chain, prefixed by this item for the new node.

## Review by Q40

I read the item against resolve.tex 0BGM, especially the complete-local permanence paragraph and its last two paragraphs. I read the statements and proofs of 0BBV (lemma-rational-to-gorenstein), 0BG0 (lemma-rational-propagates), 0BGE (lemma-resolve-rational-double-points) and 0BFY (lemma-equivalence-sequence-blowups), including the modification-category hypotheses and the fibre comparison preceding 0BFY. I read dualizing.tex 0BFR, and more-algebra.tex 07QW, 07QU, 07QV and 0C23 to check the exact permanence and completion assumptions. The new node follows the converse construction of 0BFY and its stagewise fibre argument. No SGA source is used.

Step 1 uses complete-local excellence, finite-type/localization excellence and quasi-excellent-implies-Nagata exactly as their statements say; C is Noetherian complete local, and B has the required localization presentation. I opened def-per-rational-surface-singularity and checked that its normal modifications and vanishing agree exactly with this item's explicit universal vanishing condition. The topological-cohomology definition explicitly identifies its cohomology with Zariski cohomology on a scheme. This supplies rationality without assuming a resolution.

Step 2 uses the existing rational-surface-gorenstein-blowups statement. Its hypotheses include a normal Nagata dimension-two rational local domain essentially of finite type over a Noetherian complete local base; Step 1 verifies precisely what was not already given. Its conclusion supplies normal integral intermediates, Gorenstein local rings of the endpoint, support of all centers, and proper birational composite. I separately cite blowup properness and finite-type-over-Noetherian to justify properness of each arrow and induction on Noetherianity; the ideal of a reduced closed point is quasi-coherent and finite type on a Noetherian scheme. No additional theorem about dualizing modules is silently used.

Step 3 uses excellence stability on affine charts, closed-dominant dimension for the proper birational map (transcendence degree zero), and excellent-normal-surface-local-data. I opened the latter's statement: it gives finite closed singular set, dimension two for each singular local ring, and normal completion, not just openness of the regular locus. Nagata then follows for these excellent stalks. I corrected an initial draft that obtained this geometry by viewing the tower as normalized: the delivered proof obtains it directly from its finite-type proper birational structure, avoiding any normalization identification.

Step 4 uses the definition of properness (closedness of images), the general-integral-scheme paragraph of the function-field definition, and the affine-stalk localization statement to check every hypothesis of rationality propagation. Each singular point is closed, so its image under the proper structure map is the closed point of the local base. This proves locality of B to R_i. Both embed in the identified common fraction field, proving injectivity and equality of fraction fields. The affine chart E is finite type over B, and R_i=E_q is exactly an essentially finite type extension. Normality, dimension two and Nagata of B were already checked. I do not infer rationality merely from Gorensteinness.

Step 5 uses the rational-double-point-blowup-resolution statement, which I opened in full. Its normal-completion hypothesis is indispensable and comes from Step 3. Its Gorenstein hypothesis comes from Step 2, rationality from Step 4, and its other local-ring assumptions from Step 3. It supplies ordinary blowups, integral normal intermediates and regular endpoints, not just a general birational model.

Step 6 uses the new ordinary globalization statement. Its base is integral normal Noetherian, its support points are distinct and closed, and each local tower has integral normal intermediates and reduced singular closed centers over the specified closed point. All are supplied in Steps 3 and 5. The new statement explicitly gives all intermediate comparisons and singular global centers. Step 7 is then a direct two-case local-ring argument using only these comparisons and the cited definition of regular scheme. Step 8 concatenates two finite towers and verifies support through the already established image of each x_i. Both steps are elementary and do not hide a resolution lemma.

For the new node I checked the source's quasi-compact-open hypothesis: S Noetherian implies every open, including U, is quasi-compact. The point ideal is finite type and every blowup is finite presentation over this Noetherian base, so the modification-category equivalence applies. At each stage, a point over s_i corresponds via equality of fibres; on an affine chart base localization inverts only elements already units in the local ring at that point, so the local rings agree. This proves preservation of normality and of singularity at corresponding centers; outside the finite support the schemes are unchanged. Ordinary blowups of an integral scheme remain integral by their domain chart rings A[I/a] inside Frac(A), with common generic point, and are proper. The inductive gluing construction uses one global blowup for each prescribed blowup, hence N=sum n_i. These are the reasons for the strengthened stagewise clauses, not an appeal to the proof of the existing normalized node. The child itself contains only its self-contained statement, source and searches, with no proof or proof dependencies.

I checked B through E explicitly: definitions are cited or given inline, TeX escaping is single at the mathematical-string level, tag/label pairs were checked against tags/tags, no unrun query is recorded, no Mathlib leaf is claimed, and no finished declaration or existing generic fact was recreated. Every non-elementary use is a cited statement; citations.json uses literal substrings of those statements. The new node does not restate a clause of the item: it glues arbitrary already supplied ordinary towers in any dimension and proves no local existence. Every proof step has fewer than 2000 characters. No edge goes through full resolution or normalized refinement, so there is no intended cycle. The remote DAG check will also test this mechanically.

Small cases checked: C may be nonreduced or have several components (only its excellence is used); B may be regular (zero-length towers are allowed); X may have no singularities (t=0 gives the identity); local towers can have length zero; the globalization support may be empty and r=0; disjoint supports may be processed in any order with inserted identities at the others. Normality is assumed at every local intermediate stage, so no blowup of an arbitrary normal surface is incorrectly claimed normal. Arbitrary residue fields and positive/mixed characteristic are allowed throughout the cited rational-singularity theorems. All centers retain their reduced point structures.

## Unfinished work

Only the new generic globalization lemma is left unsplit, as required for a one-level split; existing cited nodes keep their own states. No Lean was written, no compiler or Lake was run, and the repository and launcher files were read-only. Final validation and push results are recorded by deliver.py.
