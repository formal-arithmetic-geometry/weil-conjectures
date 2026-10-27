# Worker report: lem-trf-finite-smooth-integral-base-refinement

Group Q94, stage 1, 2026-10-23. Direct delivery; this is the author's self-review.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-smooth-integral-base-refinement.json: existing statement, now split into five proof steps; no Mathlib match.
- citations.json: verbatim statement quotations for every step citation.
- report.md and searches.jsonl: report and actual search log.

New nodes: 0. New Mathlib leaves: 0. Statement and statement dependencies unchanged. No Lean files written and no compiler or build used.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint tag, for finite/smooth/integral refinements, geometric integrality and purely transcendental residue fields. The hits concern unrelated curve, Picard, descent and field constructions; none gives this neighbourhood construction with every marked-point clause. Existing sorry declarations were not treated as proofs.

## WANTED

None. The needed Stacks sources are present locally.

## Problems found and repaired

The imported item was statement-only. Its source ends with “Some minor details omitted.” The split supplies both residue-field tensor calculations and the singleton-fibre argument explicitly, rather than treating etaleness as a reason for residue fields to be unchanged. Etaleness alone would not imply that conclusion. No statement error or route change was found. I preserved all inherited provenance, searches and blueprint fields; the existing blueprint.from.place was already specific. Searches of the whole imported blueprint for geometrically integral, connected component, finite smooth, elementary étale and 057K found no equivalent blueprint node. I also read the current latest blueprint proof of lem-trf-local-term-locality and retained the inherited local-structure input without changing any chapter or unit route.

## Mathlib searches

Ran the prescribed msearch command with LeanFinder twice (component spreading and elementary-etale integral-fibre refinement), Loogle, LeanSearch and source grep. The log and item contain the exact queries and actual responses. All services answered. The geometric grep and Loogle pair had zero hits. The semantic results give local standard-smooth presentations, etale permanence and algebra etale-locus/factorization statements. I read Morphisms/Smooth.lean, including Smooth.exists_isStandardSmooth and SmoothOfRelativeDimension: these produce affine standard-smooth charts, not a residue-preserving etale base change selecting a geometrically integral family. None states the item or a one-line specialization. The inherited 2026-10-22 searches remain recorded unchanged.

## Not duplicates

No new nodes were created. The whole DAG already contains lem-trf-smooth-component-pure-transcendental and lem-trf-geometrically-integral-fibre-neighbourhood, which are precisely the two substantive geometric inputs. I opened their statements and used them instead of duplicating them. The generic permanence and point/residue-field lemmas likewise already exist.

## Review by Q94

I read more-morphisms.tex Tag 057K (lemma-local-local-structure-finite-type), from the connected component T through the outer pullback diagram, and Tag 057J (lemma-normal-morphism-irreducible). I compared the integral-fibre neighbourhood node with both clauses of 057J: it really supplies a quasi-compact open and equality of the distinguished fibre, not merely a point in its closure. For the component input I read its full statement and its underlying sources: varieties.tex 04KV (lemma-geometrically-connected-if-connected-and-point) and 056T (lemma-smooth-geometrically-normal), together with the component argument printed in 057K. The component node supplies openness, quasi-compactness and geometric integrality, so those facts are not unproved claims in this split. There are no new-node sources to review.

Step 1 checks finite type of the special fibre using the finite-presentation and finite-type definitions and the finite-type base-change statement of lem-sfb-finite-type-composition-base-change. The affine presentations give finitely many generators after forgetting the relations; quasi-compactness is already in the hypotheses. The smooth relative-dimension permanence node applies to an arbitrary base change, with no Noetherian assumption. Both fibre-product nodes explicitly give the unique point and its residue field for the tensor product kappa(y_0) tensor_k k, so the component lemma receives exactly the assumed purely transcendental extension. Its conclusion is geometrically integral, and the cited definitions give geometric irreducibility.

Step 2 uses the statement of lem-trf-geometrically-integral-fibre-neighbourhood, not its proof. All three hypotheses (smoothness, finite presentation, geometrically irreducible open T) have been verified. That statement supplies the affine S_1, the residue-field isomorphism, quasi-compact V, geometrically integral fibres and the equality V_(s_1)=T_(kappa(s_1)). The dimension claim is separately justified by lem-sbc-smooth-relative-dimension-permanence, the open-immersion clause of lem-weil-pbc-etale-composition-cancellation, and the definition of etale as smooth of relative dimension zero. Thus dimension n has not been inferred merely from the spreading node, which does not mention it.

Step 3 checks directions of the Cartesian squares: the map to Y_0 is the base change of e, rho is the base change of v along pi_0, and pi_1 is the base change of pi_0 along v. The actual statements of lem-weil-pbc-etale-scheme-base-change and lem-weil-pbc-finite-morphism-permanence apply with arbitrary base-change maps. Composition with the open inclusion uses the etale composition statement. I read the source lemmas in morphisms.tex: 02GO (lemma-base-change-etale), 02GN (lemma-composition-etale), and 01WL (lemma-base-change-finite), and checked that no flatness or finite-presentation assumption on pi_0 was inserted.

Step 4 uses both separate parts of Stacks 01JT (schemes.tex, lemma-points-fibre-product), which I read with its proof: the point classification alone does not identify residue fields. The cited point-residue-field node supplies the latter identification compatibly with both factors. I wrote the tensor isomorphism and its inverse, and the equality of the distinguished fibre from step 2 ensures that the unique point lies in V. The open-immersion clause of lem-weil-pbc-residue-field-point-naturality explicitly ensures that passing to V leaves its residue field unchanged.

Step 5 again uses the point and point-residue-field statements of 01JT, now over Y_0, not over S_0. The singleton hypothesis forces every possible first projection to be w_0. Since kappa(y_0) to kappa(y_1) is the induced isomorphism from step 4, the displayed tensor field has one prime. This proves both existence and uniqueness even if the finite fibre is nonreduced. The compatible-factor conclusion of the residue-field node, with the two explicit multiplication formulas, verifies all structural compatibilities. Transporting the original rational-function-field identification then gives the last assertion without any additional field-theory existence claim.

I tested n=0 and zero transcendence degree (the formulas become identity field extensions), a disconnected smooth special fibre (select only the component through c), nonclosed marked points (01JT works for arbitrary points), a nonreduced singleton finite fibre (only its point and residue field enter), and a non-Noetherian affine base (all Noetherian reasoning is confined inside the reused finite-type field-fibre component lemma). Empty total source/base cases cannot satisfy the marked-point hypotheses. The spreading node's nonempty geometrically integral fibres are retained, not replaced by a possibly empty open restriction. None of the five proof steps exceeds 2000 characters. I checked B–E: no new standalone statements or hollow definitions, no duplicate nodes, every non-elementary input has a node citation whose full statement was read, no SGA source, and no statement weakening or circular reference. citations.json quotes the full statements verbatim so each dependency's actual scope is reviewable.

The off-unit tools are declared in split_report.tool_uses: finite-type base change, smooth relative-dimension permanence, etale composition, finite base change, fibre-product point and residue-field descriptions, and residue-field naturality. They are generic tools needed in the existing 057K route; no unit step is replaced by another route.

## Unfinished work

None at this one-level stage-1 split. The existing dependency nodes remain responsible for their own proofs.
