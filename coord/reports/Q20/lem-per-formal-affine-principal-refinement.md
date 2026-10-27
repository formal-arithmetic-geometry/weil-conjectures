# Stage-1 delivery: lem-per-formal-affine-principal-refinement

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-formal-affine-principal-refinement.json: statement, split into eight proof steps; not a Mathlib leaf. All non-elementary inputs are existing DAG nodes.
- citations.json: twenty entries, one for each step/node citation, quoting the cited statement verbatim.
- report.md: this report.

No new nodes and no new Mathlib leaves. The inherited statement, source record, blueprint provenance and searches have been retained. The current logged searches have been appended. Auxiliary sandbox files are write_split.py and searches.jsonl; these are not project files.

## Attachments

None. Searching lean/WeilConjectures by the exact blueprint tag and by formal-affine/principal-refinement terminology found no declaration giving this statement. The existing FormalAffineSectionLimit and FormalCompletionAffineQuotients files concern modules and completions of ordinary schemes, not formal-scheme principal neighbourhoods.

## WANTED

None. All sources used are present in literature/stacks-project/.

## What needed repair

The item was a statement-only node, not an existing split. Its mathematical statement is retained. The proof has to distinguish completed localization from ordinary localization: a section of R_{\{f\}} cannot generally be written as a/f^e. Only its reduction modulo the ideal of definition is such a fraction. Step 6 uses precisely that reduction, after Step 3 proves the quotient formula. This is the additional argument required to adapt the ordinary scheme proof of Tag 01IW.

Continuity also does not require a map (R,K) -> (S,L) to carry K into L. Step 4 therefore uses a nondecreasing choice of m(n) with phi(K^{m(n)}) contained in L^n, and spells out independence of this choice and the restriction/composition squares.

The existence of an open maximal ideal above m is proved before using local flatness: it is the kernel of C_s -> (R/K)_s -> R/m. Flatness alone is not used to assert the existence of that ideal. No regularity, quasi-excellence or excellence is added.

## Unfinished work

None for this one-level split. The existing unsplit dependencies retain their own queue status. No Lean was written, compiled, or built.

## Not duplicates

No new nodes. The potential new ingredients were already represented by lem-weil-pbc-module-completion-complete (05GG), lem-weil-pbc-localization-quotient-commute (00CT), lem-weil-pbc-localization-noetherian (00FN), lem-weil-pbc-adic-completion-noetherian (0316), lem-weil-pbc-noetherian-completion-flat (00MB), lem-weil-pbc-adic-complete-jacobson-radical (05GI), lem-weil-pbc-flat-local-ring-maps (00HT), and lem-weil-pbc-flat-local-hom-faithfully-flat (00HR/00HQ). These are cited, not duplicated. The existing common-principal theorem for ordinary schemes is not applied to a formal scheme. Whole-blueprint searches for 'principal refinement', 'formal spectrum', '0AHY', and 'adic formal' found no matching blueprint node; a broader completion search gave no node stating this formal-chart result.

## Review by Q20

I read the current chapter and unit records, the latest blueprint's lem-per-artin-gabber-affine-curve proof, and the item's provenance through regular-morphism-formal-completion. This is the existing formal-local ingredient of the ancestor's Step 3 duality route; no chapter or unit route was changed. I read formal-spaces.tex Tag 0AHY, including the definition of the structure sheaf, its formula on D(f), and equation 0AHZ. I read schemes.tex Tag 01IW's proof, and algebra.tex Tags 05GG, 00MB, 05GH/0316, together with the relevant existing node statements. There are no new nodes requiring additional sources. The proof is marked agent-written because the common-principal and continuity arguments are expanded explicitly, rather than claiming that 01IW already states a formal-scheme theorem.

Step 1 uses def-weil-pbc-adic-completion for the compatible-sequence completion and def-weil-affine-spectrum for the Zariski spectrum. The formal-scheme/chart description is the definition already included in the item's statement. The equality of open primes with primes containing K follows from primeness and K^n contained in an open prime. The basic-open basis follows directly from the definition of a Zariski closed set. I use only positive thickening indices.

Step 2 uses lem-weil-pbc-site-sheaf-sets-limits-sectionwise, whose statement allows every small diagram, not merely finite diagrams. The positive-integer inverse sequence is small. Its ring operations are componentwise, so using the underlying-set sheaf theorem does not claim a stronger coefficient theorem than that node states. lem-weil-pbc-affine-open-section-vanishing-prime supplies the full basic-open localization formula, applied only to the ordinary schemes Spec(R/K^n). This gives the canonical restriction maps, not only abstract section-ring isomorphisms.

Step 3 uses lem-weil-pbc-localization-quotient-commute for the exact fraction formula after quotienting. lem-weil-pbc-module-completion-complete applies to the finitely generated ideal KR_s and module R_s; its statement explicitly gives surjective projections, their kernels, and completeness, so it supplies the entire reduction formula needed later. lem-weil-pbc-localization-noetherian applies because R is Noetherian, then lem-weil-pbc-adic-completion-noetherian applies to R_s. The finite-level affine section formula is again used only for ordinary spectra. I checked the sheaf identification on a common basis: reductions of arbitrary completed elements are fractions a/s^e, so the images of elements a of R give a basis on both sides. The finite-level identification on this basis is localization at sa. Sectionwise inverse limits give the actual formal chart isomorphism and its canonical normalization.

Step 4 cites only the definitions of completion/localization and the affine-spectrum functor. Its argument writes all maps on fractions and compatible tuples; it does not appeal to an unrecorded formal-scheme full-faithfulness theorem. For each output quotient, continuity supplies an input quotient, with compatible larger indices resolving both choice independence and composition. This checks the hypotheses for arbitrary continuous maps, including non-adic ones.

Step 5 is an elementary consequence of Step 2: inverse sections exist on D(s), and the first-quotient residue map detects failure of a germ to be invertible outside D(s). Restriction of an open ringed subspace does not change its germs. This proves the intrinsic unit-locus comparison, rather than applying a theorem whose statement is restricted to schemes.

Step 6 uses the precise surjectivity/quotient clause of lem-weil-pbc-module-completion-complete, read again before writing the citation. The point is retained in each successive principal neighbourhood. It is not assumed that U intersect V is affine or that t itself is an ordinary fraction. Reduction modulo KC_f and invertibility of f yield D_U(fa); the intrinsic germ comparison of Step 5 identifies it with D_V(g). This is a short argument from the already established chart and reduction formulas, not a hidden common-principal lemma.

Step 7 uses lem-weil-pbc-adic-complete-jacobson-radical for the assertion that every maximal m contains K. The module-completion theorem's surjective first projection supplies the first arrow to (R/K)_s. Since s is outside m, the second arrow is well defined. Its composite is surjective because the restriction from R is the usual residue surjection. Its kernel is therefore a maximal ideal, contracts to m, and contains KC_s, exactly the openness condition.

Step 8 uses all five required flatness statements, not the definition of flatness in place of a theorem. Localization is flat; completion is flat with its Noetherian source R_s; their composite is flat by lem-weil-pbc-flat-ring-map-comp. The explicit contraction in Step 7 is the hypothesis of lem-weil-pbc-flat-local-ring-maps. Its statement gives the flat local map, and lem-weil-pbc-flat-local-hom-faithfully-flat gives both faithful flatness and spectral surjectivity. These are generic algebra tools; the split_report declares their off-unit use where appropriate.

I checked the small cases: K=0 gives the ordinary affine formula and common-principal argument; nilpotent K gives a constant quotient tower eventually; s=1 gives the whole chart; s=0 gives the empty chart and zero completed ring, with no maximal-ideal assertion triggered; a unit s does not change the completion. For R the zero ring there are no points or maximal ideals. For a complete local ring and s in its maximal ideal the final conditional assertion is not invoked. None of these requires a nonzero-ring hypothesis or an invertible ideal of definition.

Against delivery-errors B-E: no statement-only child contains a hidden proof because there are no children; no duplicate or clause-renaming node was created; all cited statements were read, and citations.json records the exact wording used. Every non-elementary input has a node. No proof step exceeds 2000 characters, no dependency on the item is introduced through the cited input statements, and no forbidden SGA route is used. The only elementary steps are definition unfolding, explicit tuple/fraction formulas, the intrinsic unit-locus check, and the few-line refinement argument from the completed reduction theorem.
