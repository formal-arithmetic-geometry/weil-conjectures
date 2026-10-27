# Q142 stage-1 delivery: lem-per-henselian-krasner-neighbourhood

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-krasner-neighbourhood.json: statement, split; no Mathlib match for arbitrary-rank henselian Krasner. Five proof steps, reusing three existing statement nodes.
- citations.json: four citations, checked as literal substrings of the current cited statements.
- report.md: this report.
- searches.jsonl: actual searches recorded by the required msearch command.

No new nodes and no new Mathlib leaves. The existing leaves lem-weil-pbc-finite-galois-fixed-field and lem-exc-etale-galois-fixed-field-subgroup are reused.

## Attachments

None. Searched lean/WeilConjectures for the item id, Krasner, and the henselian/valuation concepts. PadicAlgCl.exists_isAlgebraic_mem_adjoin_simple in NumberTheory/Padics/Extension.lean uses complete p-adic normed-field Krasner; it does not state this item. The deleted Sheaf.FieldTheory.HenselianKrasnerNeighbourhood module is historical evidence only, not an attachment.

## WANTED

WANTED: Bourbaki, Algebre commutative, VI section 8, exercises 12 and 14(a), for lem-per-henselian-krasner-neighbourhood (the forms of Krasner cited in ILO XX 4.4). That text is not locally available. I read the available ILO paragraph and wrote the proof myself from existing interfaces; proof_origin.by is agent. The unsplit admitted input lem-per-henselian-finite-extension-topology retains its own source obligation for valuation-extension uniqueness. I do not claim to have read Bourbaki or to prove that input in this delivery.

## Corrections and scope

The released stage-1 repair note and coord/changes/20261024-Q112-strict-completion-inputs.md explicitly re-admit this exact interface while withdrawing its historical proof, review and attachment. I reconstructed the split from current statements; the item statement, statement dependencies, source, prior searches and blueprint provenance are preserved. No statement dispute was found. No excellence hypothesis or completeness assumption is inserted.

The chapter and unit records were read. The latest blueprint's lem-per-artin-gabber-affine-curve and sk-p-dl-a1-perverse files now carry statements rather than the old expanded proof. The retained ancestor provenance is therefore historical, as the Q112 release expressly requires. This delivery works on the specifically re-admitted lower interface and restores none of the excluded parent comparisons. It does not change chapter or unit records. The item is not its unit's key node.

The important distinction is uniqueness of valuation subrings versus equality of valuation values. The finite-extension node gives the first. Step 2 supplies the second by a finite-cycle contradiction, so no unquoted numeric uniqueness theorem is smuggled into step 1. Stacks Tag 09EI is not used, since it would add complete one-dimensional hypotheses. The Galois fixed-field theorem is applied to the subgroup fixing the whole intermediate field, not to an arbitrary set of embeddings.

## Searches and Not duplicates

Existing item search records were retained. Additional actual msearch queries cover LeanSearch, LeanFinder, Loogle and grep, with two semantic phrasings and the direct IsKrasner query. I inspected Krasner.lean lines 48–75 and 117–129: the available results require a normed extension and complete nontrivially normed base, which do not supply this arbitrary-rank assertion. Other returned signatures are valuation-extension definitions, HenselianLocalRing and p-adic Hensel, not matches. No service was unavailable in these new searches.

DAG statement/title searches found the already admitted finite-extension uniqueness interface and existing Galois leaves. Whole-blueprint searches for Krasner and henselian valuation returned no duplicate; fixed field returned three unrelated blueprint nodes about coefficient and lattice contexts. No node was created; in particular no duplicate of the uniqueness clause or an item clause is introduced.

## Review by Q142

I read ILO, Travaux de Gabber, XX 4.4, printed pp.373–374 (PDF pp.379–380), including its reduction to dense henselian valued fields and the reference to forms of Krasner. It motivates this interface but supplies no proof of the valuation lemma, so this reconstruction is honestly agent-authored. I also read the statements of every cited DAG node, and the matching Mathlib fixed-field sources (Galois/Infinite.lean, lemma fixedField_fixingSubgroup; Galois/Basic.lean, card_aut_eq_finrank, fixedField_top and mem_range_algebraMap_iff_fixed). There are no new nodes with additional sources to audit.

Step 1 uses exactly the prolongation-uniqueness clause of lem-per-henselian-finite-extension-topology. Its F, valuation and E=N satisfy nontriviality, henselianity and finite algebraicity. Precomposing w with an F-automorphism is again a prolongation. Equality of the two valuation subrings gives invariance of W, and a ring automorphism preserves units. This invocation is of an admitted current statement; its proof is not imported from its withdrawn historical graph.

Step 2 cites the finiteness clause of lem-weil-pbc-finite-galois-fixed-field with M=N and k=F. The finite separable normal hypotheses are precisely those in the item. Finite order follows by repetition of powers and cancellation. For nonzero a,b the valuation axioms give w(a)>w(b) exactly when a/b belongs to W but is not a unit; ring invariance from step 1 preserves this test. A strictly increasing or decreasing finite cycle is impossible in a total order. This proves equality of values even when the ambient value group is larger than the image. The zero case is separate. This is an elementary consequence of the cited finiteness and step 1, not a hidden arbitrary-rank uniqueness theorem.

Step 3 is elementary: for an automorphism fixing beta, expand alpha minus its conjugate as the difference of alpha-beta and its image; apply the ultrametric inequality and step 2. If it moves alpha, the assumed strict inequality contradicts the resulting weak reverse inequality. This proves the heart of Krasner inside the item rather than moving it into a new clause node. It also treats alpha=beta using infinity.

Step 4 cites precisely the fixed-field equivalence in lem-exc-etale-galois-fixed-field-subgroup with K=N, k=F, L=F(beta). An automorphism fixes beta iff it fixes F(beta) pointwise, by preservation of field operations; H is defined as the latter subgroup. Thus the cited statement applies to the subgroup actually used and gives the required field membership. This leaf already assumes and supplies the full Galois intermediate-field result; no separate unproved Galois-over-an-intermediate-field claim is needed.

Step 5 reuses both finiteness and the base-fixed-field clause of lem-weil-pbc-finite-galois-fixed-field. If alpha is not in F, some automorphism moves it; the finite nonempty set of finite separation values has a maximum in a totally ordered group. The ball above that maximum is a basis open containing alpha, and step 4 applies to every beta in it. If alpha is in F, U=N works for every beta. I checked N=F, alpha=0, alpha=beta, beta in F, an empty moved-conjugate set, and higher-rank ordered groups. None requires a rank-one embedding, density of the value group, completeness, or excellence. A nonzero conjugate difference always has finite value, so infinity never enters the maximum.

I checked delivery-errors B–E against the actual files: all objects are introduced; no statement was changed or new unsplit proof hidden; the non-elementary inputs are cited statement nodes; every literal citation is copied from the exact clause used; all uses agree with proof_deps; and no new clause-restatement, duplicate, source restriction, or dependency back-edge is introduced. Each proof step is below 2000 characters (418, 550, 511, 239, 611), and together they expose the complete automorphism argument and the open ball. The only remaining proof obligations are those already belonging to the separately admitted unsplit input, not unfinished steps of this item.

## Unfinished work

None in this one-level split. The existing input lem-per-henselian-finite-extension-topology is separately unsplit and is cited as normal stage-1 work, not represented as proved. No compiler, Lake command, repository git command, or repository write was run.
