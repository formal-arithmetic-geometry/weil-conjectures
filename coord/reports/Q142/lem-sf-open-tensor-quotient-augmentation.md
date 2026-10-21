# Q142: lem-sf-open-tensor-quotient-augmentation

## Files written

- `dag/nodes/sec-six-functors/lem-sf-open-tensor-quotient-augmentation.json`: statement, split into seven proof steps; statement unchanged; no Mathlib match.
- `citations.json`: 31 step/dependency entries quoting the statements actually read.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `write_split.py` is sandbox-only scratch work.

There are **0 new nodes and 0 new Mathlib leaves**. The item is not the unit's key statement, so no unit realization file is changed.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, open tensor names, quotient/augmentation names, and the open/scalar notions. I read the pro-etale adic OpenImmersion file, the finite-coefficient derived OpenLowerShriekProj file, and the scalar-extension comparison declarations. They supply open projection or constant-coefficient scalar results, not this whole completed-integral, strict augmented-system assertion. In particular the adic OpenImmersion file's coefficient category is the constant Qbar_l module category, not the B_W-module category of the item; finite derived projection formulas alone do not supply the required simultaneous augmentation equation. No attachment is claimed.

## WANTED

None: both Stacks source files and the Bhatt--Scholze paper used here are available locally.

## Corrections and source audit

The imported item had no proof. Its statement, statement dependencies, original searches, source metadata, and blueprint ancestry were retained. I supplied the proof, proof dependencies, proof origin, split report and current logged searches. There is no statement dispute and no change to the coefficient categories or the definition of a completion map.

I read the chapter and unit records and the current `main-20261015` proof of `prop-sf-pf-coherence`. The proof follows its open-factor normalization route. I read Stacks Tag 0E8I (`sites-modules.tex`, `lemma-j-shriek-and-tensor`) and Tag 0GL1 (`sites-cohomology.tex`, same label), checking their tag mapping in `tags/tags`. The former gives the ordinary slice tensor identity via adjunction; the latter passes to complexes and leaves details omitted. Bhatt--Scholze Lemma 6.5.8(2),(3), p.50, supplies the source's constructible open/restriction context. The strict balanced tensor/augmentation calculation is written by the agent, so `proof_origin.by` is `agent`. No SGA route is cited or used by the delivery.

I searched the full DAG and blueprint for `quotient augmentation`, `open tensor`, the tags 0E8I/0GL1, and scalar/tensor reduction concepts, and ran `blueprint_refs.py ancestor`. The nearest blueprint ancestor remains `prop-sf-pf-coherence`, through `lem-sf-pf-open-factor-coherence`. No other blueprint node states this simultaneous tensor square; `same_as` remains empty. Existing `lem-sf-open-semilinear-tensor-model` and `lem-sf-integral-open-reduction-comparison` provide the reduction-model input; creating another node for it would duplicate them. The finite constructibility and restriction clauses likewise use existing nodes rather than introducing clauses as new nodes.

## Mathlib searches

The command-generated log records these fresh searches, all inspected:

- leanfinder: `Extension by zero of module complexes commutes with coefficient reduction and derived tensor with compatibility of the strict quotient tower augmentation`.
- loogle: `SheafOfModules`.
- grep: `extensionByZero|ExtensionByZero|jShriek|lowerShriek` (0 hits).
- leansearch: `Derived tensor projection formula for extension by zero preserves scalar reduction tower augmentations`.
- second leanfinder phrasing: `Canonical open immersion projection formula on sheaves of modules is natural for change of coefficient rings and scalar unit maps`.

The first semantic search found ordinary tensor/quotient/completion maps; LeanSearch returned ordinary projectivity, Tor, zero-tensor and left-derived-zero facts. Loogle lists the sheaf-of-modules definition/interface. The second phrasing returned Zariski structure-module restriction and open-immersion ringed-space formulas. I read Mathlib `Algebra/Category/ModuleCat/Sheaf.lean` (definition and morphisms), `RingTheory/AdicCompletion/AsTensorProduct.lean` (ordinary module-completion naturality), and `AlgebraicGeometry/Modules/Sheaf.lean:395,484` (the restriction formulas). None is the pro-etale completed-coefficient strict augmented tensor statement. No service was unavailable in these fresh searches. The imported search history, including its unavailable Loogle attempt, was preserved without relabelling it as a fresh search.

## Tool uses

The item's `split_report.tool_uses` records the off-unit statements used as generic tools: K-flat resolution, ringed-topos derived tensor pullback, the normalized open tensor comparison, the strict open semilinear tensor model, the actual integral open reduction comparison, exact ringed-slice extension, finite-stage constructibility/interval preservation, and the immersion completed-pullback comparison. The Noetherian-open assertion is also cited. Definitions and the existing Mathlib Noetherian finite-type leaf are used in their usual role. These tools verify the representatives, coefficient comparison and domains of the unit's open-factor maps; they do not replace the unit's route with another projection-formula proof.

## Review by Q142

I checked delivery-errors B--E against the written proof and the local sources. There are no new nodes requiring a self-contained-statement or duplicate audit. I kept elementary tensor formulas in the item's proof instead of creating new elementary nodes or moving the item's final square into a new lemma. All seven steps have explicit sources and `elementary` booleans; every cited statement was opened, and its exact statement appears in the corresponding citation entry. The non-elementary inputs are statements of nodes, not claims borrowed from their internal proofs.

For step 1 I checked that `lem-pc-kflat-resolution` supplies flat terms as well as K-flatness. The open semilinear tensor-model statement explicitly says that j_!Q is flat-term K-flat and that the total tensor has the signed differential and direct sums used here. The ringed-topos tensor-pullback statement supplies K-flat preservation under both restriction and identity-topos scalar extension, with no flatness hypothesis on the ring map. The open tensor normalization fixes the inverse-unit transpose. This verifies the chosen chain isomorphism represents the specified gamma^B, for unbounded complexes.

For step 2 I checked the strict semilinear model's actual statement: its representative is [x] tensor a mapped to [x tensor a restricted], before localization; it explicitly retains all quotient transitions and scalar-unit augmentations. The integral open reduction comparison identifies its localization with r_j(K) and proves completeness. Its quasi-compact hypothesis is satisfied: X is Noetherian by finite type over the Noetherian field and the cited 01T6 leaf, and every open in a Noetherian scheme is quasi-compact by the cited Noetherian-open node (spelled out in step 4). The coefficient-mate definition fixes which transpose the scalar map means; it is not cited as a theorem of invertibility. The actual invertibility comes from the normalization/model and reduction-comparison statements.

For step 3 the scalar-restriction comparison is a short direct argument on the extension-presheaf summands, whose formula is precisely in `def-weil-extension-by-zero-presheaf`. Exact ringed-slice extension is defined as sheafification by its cited statement. Forgetting scalars leaves the additive sheaf and induced action unchanged, hence leaves all the displayed transition maps unchanged. The strict model confirms the A_n-linear comparison before forgetting. No scalar-linear information is inferred merely from a B-linear derived isomorphism.

For step 4 I checked the hypotheses of the finite constructibility-interval node: X is Noetherian, ell is invertible because the schemes are over k of different characteristic, n is positive, and K_n is bounded constructible with the fixed common interval supplied by the integral definition. Its statement explicitly includes the reduced closed complement, zero restriction there, cohomology identity and preservation of the same interval. The integral comparison from step 2 supplies the separate completeness condition. The immersion comparison explicitly says ordinary restriction preserves completeness, the integral category and the uniform interval; so it supplies all requirements for j^*P. The partition restriction is the literal intersection with the open, not an identification of a general subscheme from its underlying set.

For step 5 I checked the balancing maps in both directions, including the product ab and the unit 1, and wrote the K-flatness argument for each total tensor using the definition (tensoring an acyclic complex twice). The canonical identification with derived coefficient change is the tensor-pullback node's stated comparison, computed on the preserved K-flat representatives. The remaining argument is elementary from the sheaf tensor and signed total-complex definitions. The maps preserve the order of homogeneous factors, so no extra Koszul sign appears. Their explicit formulas commute with every quotient homomorphism, not only the adjacent one.

For step 6 I checked that the semilinear tensor-model statement includes the ordinary chain tensor isomorphism for any second complex, so it applies at each finite coefficient stage. The open normalization identifies its inverse by the adjunction unit. On a summand indexed by a map into the open this unit is the same section; consequently the formula for [x] tensor y is the stated unit transpose. I wrote out both coefficient-change routes on ([x] tensor y) tensor a, including the restriction of a, and checked that they coincide before sheafification and after its universal extension. The exact same calculation applies to transitions. This proves the claimed comparison at the level of systems rather than using faithfulness of evaluations.

For step 7 I checked that the reduction-tower definition supplies the strict units x mapped to x tensor 1, and that the tensor-completion definition specifies the matching first Roos coordinate and zero shifted coordinate. Both augmented composites have the identical displayed value on every homogeneous tensor, with the same degree and sign checks as step 5. Since quotient maps preserve 1 this is a simultaneous augmented-system equality. Localization preserves an equality already established there. I did not apply the exact-product/limit comparison to j_!: its preservation-of-products hypothesis has not been assumed. No commutation of extension by zero with arbitrary inverse limits is used anywhere.

I checked the edge cases j the identity, the empty open, zero K or P, n=1, repeated quotient indices, and a homogeneous tensor with odd first degree. The identity and empty cases give the identity/zero maps; zero inputs stay zero; repeated quotients give units; odd degree retains the common minus sign because no factor is exchanged. For U different from X the reduced closed complement receives the zero sheaf as stated. There is no finite-Tor hypothesis on K or P; K-flatness is only a choice of representatives.

I checked dependency reachability in the read DAG: none of the cited generic tools reaches this item, so the proposed edges do not make a cycle. Every proof step is under 2000 characters; no long step hides a lemma. The substantive homological, completeness and finiteness facts are all cited as existing nodes, while the balanced formulas and strict augmentation calculation remain explicit proof steps.

## Unfinished work

None in the requested one-level split. Existing dependencies retain their own stage-1 states and were not edited. The server review_split check passed before this report was written; the required full delivery dry run and push follow.
