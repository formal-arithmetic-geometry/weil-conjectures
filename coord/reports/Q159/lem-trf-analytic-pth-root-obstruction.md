# Stage-1 delivery: lem-trf-analytic-pth-root-obstruction

## Files written

- dag/nodes/sec-trace-formula/lem-trf-analytic-pth-root-obstruction.json: item, statement unchanged, split into three steps.
- dag/nodes/sec-trace-formula/lem-trf-analytic-disc-translation-embedding.json: new statement-only analytic input, unsplit; no Mathlib match.
- citations.json: verbatim statement excerpts for both citations of the new node.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, pth-root obstruction, TateAlgebra, Gauss norms, analytic pth roots and type-four fields. The pth-root results found there concern algebraic characteristic-p extensions, not this completed valued-field assertion. No Lean was written or compiled.

## Literature wanted

WANTED: Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, Section 6.2, printed pp. 42, 44-45, for lem-trf-analytic-pth-root-obstruction and lem-trf-analytic-disc-translation-embedding. The cited literature/temkin-stable-modification-arXiv-0707.3953v3.pdf is absent from this read clone. I read the author's online PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, including the disc discussion immediately preceding Lemma 6.2.8 and that lemma's proof. Nothing was downloaded into the repository. proof_origin.by is agent under the missing-local-document rule.

## What was wrong or incomplete

The item had a correct statement and source, but no proof. No statement dispute arose and no hypotheses were changed. Its inherited Q46 Mathlib searches have been retained, and four actual Q159 searches appended. The new node has six actual searches with the exact query texts and returned output, including a second semantic phrasing and a focused grep.

The source's final argument separates rational and irrational disc radii after enlarging scalars to an algebraically closed analytic field. The split uses the same preceding disc construction with l=K; it compares the linear coefficient instead. This supplies the contradiction directly and needs neither an algebraic-closure-completion theorem nor reduction of a disc algebra. This is an elementary calculation within the source's disc route, not replacement of the unit's geometric route.

## Search results and small cases

The item searches returned function-field completions, algebraic pth-root results, metric infDist facts, and unrelated number-field results. None gives the complete analytic assertion. For the new node, Loogle reports unknown identifier TateAlgebra (an actual successful request returning no hits); LeanSearch returns completion algebra instances and adic tensor-completion equivalences, not this nonarchimedean disc embedding. LeanFinder returns Laurent-series completions and PowerSeries.gaussNorm. I opened Mathlib/RingTheory/PowerSeries/GaussNorm.lean (definition around lines 56-65) and Mathlib/RingTheory/MvPowerSeries/GaussNorm.lean: these give coefficient supremum norms and algebraic inequalities, not a map from the particular field K with j(z)=z+W. The new node therefore remains unsplit. All msearch results are saved in search-0.txt through search-9.txt and logged in searches.jsonl; no unrun search is claimed.

The new statement has no characteristic-p assumption: it is the analytic construction independent of root extraction. To see why it is true and substantial, factor a polynomial P over the algebraically closed field k. For each root c, |z-c|>r, so replacing z by z+W preserves the norm of the linear factor and its inverse expands in a convergent geometric series in D_r(K). This defines an isometry on k(z), which extends to K using completeness of the weighted restricted-series algebra. That construction is future work of the statement-only node; it is not placed in that node's statement or proof fields. This is a real analytic extension lemma, not an elementary arithmetic step. It also does not assert the pth-root obstruction or any clause of it.

For equal characteristic p, the coefficient identity p*a_0^(p-1)*a_1=1 becomes 0=1. For mixed characteristic, the norm estimate gives the strict contradiction using exactly the assumed |pz|<r. For p=2 the coefficient is 2*a_0*a_1, with no odd-prime assumption. Nonpositive radius is excluded by the item's strict hypothesis and explicitly by the new node; an attained radius is excluded by the immediate residue/value-group argument, not assumed without proof. An algebraic coordinate over algebraically closed k would lie in k and is excluded. No local compactness, discreteness, spherical completeness, or radius in the value group is assumed. The weighted series condition is used for an arbitrary positive real radius.

## Not duplicates

lem-trf-analytic-disc-translation-embedding vs lem-trf-analytic-pth-root-obstruction: the new lemma constructs an isometric translation map without a residue-characteristic or |pz| assumption; the item rules out pth roots under a quantitative inequality, using that map and a coefficient computation.
lem-trf-analytic-disc-translation-embedding vs lem-trf-analytic-immediate-rationality: the latter constructs a topological generator for a finite extension; the new lemma starts with a specified generator and constructs a map into a weighted disc algebra.
lem-trf-analytic-disc-translation-embedding vs lem-trf-affinoid-supremum-seminorm-calculus: that node concerns spectral seminorms of affinoid quotients, not a field translation map j with j(z)=z+W.
lem-trf-analytic-disc-translation-embedding vs lem-trf-affinoid-spectral-banach-norm: that node concerns norms on reduced affinoid quotients of unit-radius Tate algebras, not a type-four field embedded into an arbitrary-radius disc.
lem-trf-analytic-disc-translation-embedding vs lem-per-tate-banach-substitution: that node substitutes elements of norm at most one into a unit-radius Tate algebra; it does not extend substitution on a dense rational subfield to this completed field.

Whole-DAG statement searches for Schauder, Gauss, disc algebra, isometric embedding, bounded derivation and completed tensor product found no existing statement constructing this map. Source-place searches for 6.2.7 and 6.2.8 found the item and parent, with unrelated tag-number matches elsewhere. Whole-blueprint searches were run with tools/blueprint_refs.py for pth root, completed tensor, Schauder, Gauss, disc, disc algebra and translation embedding. The broad disc hits concerned discrete or disconnected objects; the precise disc-algebra and translation searches returned no match. The ancestor command gives lem-trf-local-term-locality; the new node prepends this item to its existing via chain. No new Stacks tag is used: the source is Temkin's analytic argument, not a result attributed to an unrelated Stacks tag.

## Review by Q159

I read AGENTS.md, the worker role, the stage-1 brief and stage document, GOAL.md, SETUP.md's three-level and tool-use rules, the trace-formula chapter and sk-i-curve-zero unit, and delivery-errors.md sections B-E in both their original and merged copies. I read the latest blueprint's lem-trf-local-term-locality proof and COMMITS.txt (latest ef6f9619fdbffa59e88528fb56483d76c70258c8). The inherited supporting branch is kept and no unit or chapter record is changed. There are no off-unit proof dependencies or SGA sources.

For the item and the new node I read the author PDF's Section 6.2, especially the unattained-distance discussion and the completed tensor product disc description on printed p. 45, followed by Lemma 6.2.8. The source allows any complete analytic extension l with an isometric K embedding for the disc description, so l=K and the identity embedding are valid; the algebraic closedness requirement on l occurs only later in its chosen proof of Lemma 6.2.8. The new node states exactly the first-factor map and its norm after this specialization. Its fields, radius, weighted series, multiplication, norm, constants and algebra map are all introduced explicitly. I checked the field and valuation-ring definition nodes already used in the item's statement; the new node only needs the field definition and defines its analytic objects inline.

Step 1 cites no lemma: |pz|<r gives r>0; if the infimum were attained, value-group equality gives a scalar of that norm and residue-field equality gives a strictly closer constant by a single subtraction. Thus every hypothesis on the radius used in step 2 has been established. Step 2 cites the new node, whose statement explicitly provides the unital k-algebra homomorphism, the formula j(z)=z+W and norm preservation for every a in K. The item's completeness, algebraic closedness and topological-generation hypotheses match it exactly. The copied quote in citations.json contains all three conclusions, so the proof uses its statement and not a future proof construction. Applying the homomorphism to u^p=z and raising the equality of real norms are elementary.

Step 3 also cites the new node, this time for its explicit series algebra and supremum norm definition. The quotation contains exactly those definitions. The degree-one coefficient in a product of p copies has exactly p contributions a_0^(p-1)*a_1; this finite Cauchy-product argument is written out. The two coefficient bounds come directly from the stated supremum. Their product gives r<=|p|*norm(F)^p=|pz|, contradicting the item's strict hypothesis. The argument never assumes multiplicativity of a general Banach algebra norm, a separable polynomial, or an algebraic-closure completion. Both elementary flags are justified by the displayed few-line calculations, while the analytic map is explicitly non-elementary and cited.

For B1-B10 I checked that the one new node is statement-only with empty proof and proof_deps, self-contained, correctly escaped TeX, genuinely sourced, searched, without a fabricated Mathlib match, with creation stamp and blueprint provenance. There is no claim of a finished attachment. For C1-C8 I checked every fact used, the two verbatim citation excerpts, dependency equality, no use of a proof in place of a statement, and the absence of off-route citations. For D1-D5 the item itself carries both the radius argument and root contradiction; it does not move its conclusion into the new node. For E1-E7 I checked all radius and coefficient hypotheses, the two characteristics and p=2, and the exact objects involved; no source statement needed correction. No proof step exceeds 2000 characters (lengths 402, 375 and 547), and no hidden comparison lemma remains in a long step.

## Unfinished work

The new analytic translation-embedding node is deliberately unsplit, as required for a one-level stage-1 split. There is no unfinished step in the item's assembly proof. No compiler, Lake, local DAG checker or local preflight was run.
