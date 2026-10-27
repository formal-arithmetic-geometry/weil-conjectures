# Stage-1 report: lem-per-finite-coefficient-henselian-cylinder

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-coefficient-henselian-cylinder.json`: statement, split into ten proof steps; not a Mathlib leaf. The statement and its eleven statement dependencies are unchanged. Twenty-four existing nodes provide the proof dependencies.
- `citations.json`: one verbatim statement quotation for every use in every numbered proof step.
- `searches.jsonl`: actual searches produced by the prescribed msearch command.
- `report.md`: this report. `write_split.py` is sandbox-only scratch work.

No new nodes, no new Mathlib leaves, no unit or chapter edits, and no Lean files.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id, henselian cylinders, henselian polynomial rings and finite coefficient henselization. There is no project declaration giving all clauses. The recorded upstream state is `none`; neither a partial result nor a sorried declaration was counted as an attachment.

## WANTED

None for this item. The ILO PDF and the Stacks sources needed to check this argument are present. No new supporting statement needs an unavailable source.

## Problems found and corrected

The imported source pointer called Tag 05WR `lemma-quasi-finite-henselization`. The tags table and algebra.tex show that 05WR is `lemma-quasi-finite-strict-henselization`; the ordinary-henselization statement is 05WP. I corrected only this bibliographic tag, without changing the mathematical statement.

The imported node had no proof. The finite map on henselizations does not follow merely from henselization's definition, and the tensor comparison must be the canonical multiplication map. Steps 5 and 6 now cite the existing quasi-finite henselization and finite-extension completion statements and verify their hypotheses explicitly. The proof also does not infer henselianity for a smaller ideal from maximal-ideal henselianity without argument; Step 7 supplies the idempotent proof.

The current blueprint's chapter and unit text have evolved relative to their imported DAG records. I read `literature/blueprint/latest/` (the chapter, perverse unit, and ancestor Artin--Gabber proof). This item is the algebraic input already assigned to the ancestor's ILO reduction, through the existing marked-cylinder chain; no Fourier or perverse argument is replaced, and no blueprint or unit record is edited. Existing provenance is retained.

## Unfinished work

None in the stage-1 split. The cited unsplit/sorried algebra nodes remain independent work items; none is represented here as a completed Lean proof.

## Not duplicates

No new nodes are introduced. Searches of the whole DAG by tags and notions, and blueprint_refs searches for henselian cylinders, finite coefficient henselization, complete local excellence, power-series finiteness and tensor products found the existing algebra nodes reused here. In particular the distinguished quotient, power-series ring properties, complete-local excellence, ordinary quasi-finite henselization, and completion-finite-extension results were not recreated.

## Review by NL

I read ILO Expose V 1.1.1(i), 1.1.3 and its proof, 1.2.3 and its proof, 2.2.3, and 3.2.3 (printed pp. 63--67; PDF pages 69--73). Lemma 1.1.3 proves the distinguished-polynomial completion comparison, not a finite coefficient theorem by itself. Section 3.2.3 supplies the finite-coefficient situation. I therefore marked the assembled proof as agent-written, with its additional finite-coefficient argument explicit. I also opened Stacks algebra.tex 05WP (`lemma-quasi-finite-henselization`), 05WQ (`lemma-quotient-henselization`), 07N9 (`lemma-completion-finite-extension`) and its proof, and more-algebra.tex 07QU (`lemma-finite-type-over-excellent`), 07QW (`proposition-ubiquity-excellent`) and the ordinary henselization Noetherian/completion theorem. The tag/label table was used to check the identifiers. There are no new nodes whose source requires a separate review.

For Step 1 I opened all four cited power-series statements. They assert, respectively, Noetherianity, the unit/local criterion, completeness for the combined coefficient-and-variable ideal, and domainhood. The coefficient rings are fields or complete DVRs, hence satisfy every hypothesis. Iterated and simultaneous power series are identified by explicit coefficient regrouping, not an unquoted comparison theorem. A field is complete for its zero ideal; no positive residue characteristic or Cohen-ring assumption is used for a general DVR.

For Step 2 the only cited definition is finite module generation. A choice of coefficients expressing each coefficient of a series in the fixed finite list gives the displayed finite sum of series, so neither tensor commutation with an infinite product nor a finite-free assertion is hidden. Constant coefficients check the contraction of maximal ideals. The exact same argument gives finiteness of the full completed coefficient extension and the polynomial map. This is an elementary step, not a new lemma node.

For Step 3 I read the entire statement of `lem-per-weierstrass-henselian-cylinder`. Taking its coefficient ring to be D or E, r=1 and f=T is legitimate, including e=0; it states the precise henselizations, maximal-ideal completions, and faithful flatness used here. Its existential distinguished polynomial is not presumed to be the particular g in this item. The completion map in its conclusion is canonical, so this use does not change coordinates.

For Step 4 the complete-local excellence statement applies to D and E. The finite-type/localization excellence statement applies to each polynomial local ring. The excellence definition supplies quasi-excellence and Noetherianity. The domain and fraction arguments make these local rings reduced. The first clause of `lem-per-henselian-normal-completion-preparation` states exactly excellence for their ordinary henselizations, under these verified hypotheses; no normalization object or conclusion of its proof is used. Finally the faithfully-flat universal-injectivity statement, with N equal to its base ring, supplies injectivity into the known domain completion. I checked the tensor multiplication identification used to extract this ring injection.

For Step 5 I opened both the finite-map/quasi-finite node and the ordinary henselization quasi-finite node. The former supplies finite type and quasi-finiteness, the latter finiteness and locality on the ordinary henselizations. The primes and their contraction are those already computed in Step 2. Completeness implies henselianity by the cited complete-pair statement; uniqueness from the ordinary henselization definition then identifies the two structural maps to R_V. All maps used for that uniqueness are local by the constant-coefficient criterion and the henselization structural maps.

For Step 6 I checked the finite-is-integral statement, the prime-over-maximal statement, and every compatibility clause of the completion-finite-extension statement. The two first results show there is just one prime over the base maximal ideal in the local finite algebra S_V. In the last statement I substitute the base S and algebra S_V, and localization at the maximal ideals is identity. Its compatibility with both scalar structures, together with Step 5, pins down the image of a pure tensor as the product ab. This checks the actual map, not merely existence of some isomorphism. Ramification causes no problem: no equality of extended and target maximal ideals is assumed.

For Step 7 the finite-over-henselian-local-product statement includes locality of each structural map, which is needed to put g in each factor's maximal ideal. I wrote out the local-idempotent argument and applied the exact idempotent-lifting definition. It covers the zero finite algebra via the empty product. The pair assertion is not borrowed from a definition node as if it were a theorem.

For Step 8 I checked the distinguished-polynomial-quotient statement, which gives the canonical algebra isomorphism for every distinguished polynomial. The polynomial g^N remains monic of degree nN and reduces to T^(nN); all its lower coefficients lie in the respective coefficient maximal ideal, including after D to E. The complete-pair and quotient-henselian statements give the quotient's henselianity. Locality and inversion outside the specified prime justify the localization comparison. These are comparisons of the same coefficient maps, so there is no unmentioned abstract identification.

For Step 9 the ordinary quotient-henselization statement says exactly that H/g^N H is the henselization of A/g^N A. I used only the ordinary universal-property definition to prove that the henselization of this already henselian ring is its identity. Both composites are checked by uniqueness; compatibility for N+1 to N is spelled out on residue classes from H. Step 10 uses the complete-local-subideal statement with C Noetherian complete local and g in its maximal ideal. Thus its inverse limit is C, and its map from H is the one already proved faithfully flat. No flatness-for-a-new-topology claim is left implicit.

I checked the small cases e=0, identical coefficient rings, finite inseparable field extensions, and a ramified extension of complete DVRs. None needs separability or an unramified hypothesis. For g=T^n over a field all quotient and completion calculations reduce to ordinary truncated series. For g=T^n plus lower coefficients in the coefficient maximal ideal the same distinguished-quotient argument applies. The condition n>0 is used to keep g a nonunit and all local quotients nonzero; it is not dropped. No statement dispute or weakened conclusion was needed.

Against delivery-errors B: no new node is manufactured, statements remain self-contained with their existing definition dependencies, TeX is singly escaped, the ordinary Stacks tag is repaired, and actual Mathlib searches are recorded. Against C: I read every cited statement, wrote a verbatim quote for every use, and supplied the non-elementary results as nodes rather than bare source tags. Generic off-unit algebra tools are declared in split_report.tool_uses with their purpose; they do not replace a unit step. Against D: the proof is an argument in ten steps using existing smaller facts; no clause is moved to a freshly named node and no proof of a cited node is used as an interface. Against E: every finite-type, local, Noetherian, complete, domain and distinguished hypothesis is verified where it is needed, and the specified maps and inverse-limit reductions are fixed explicitly. Every non-elementary step is under 2000 characters (the longest is under 1000), so no long-step exemption or hidden inline lemma is required. The server review_split check has passed with zero new nodes; the final deliver.py dry run remains the full preflight check.
