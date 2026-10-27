# Worker report — Q89

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-adic-projective-compatible-sections.json`: existing statement item, now split in seven steps; no full Mathlib match. Its statement, statement dependencies, source, creation record and blueprint ancestry are retained.
- `citations.json`: verbatim statement excerpts for the two proof citations.
- `searches.jsonl`: five real Q89 searches logged by msearch.py, reused after the session pause; all returned successfully. The item retains the earlier Q43 search records and adds these exact queries with their results and verdicts.
- `report.md`: this report. `write_split.py` is a sandbox-only generation aid, not a delivery file.

New nodes: 0. New Mathlib leaves: 0. The sole proof dependency is the existing Mathlib leaf `def-weil-pbc-projective-module`.

## Attachments

None. Searching WeilConjectures for the item tag, for compatible sections and splittings, and for the adic/projective notions found no project declaration proving the whole item. A completion-surjectivity theorem or a single projective splitting does not include compatibility with a prescribed previous section.

## WANTED

None. The mathematical sources used here are available in `literature/stacks-project/algebra.tex`.

## What was wrong or incomplete

The item had a statement and search history but no proof. I have not changed its statement. Stacks Tag 05D3 (`lemma-split-completed-sequence`, lines 23177–23221 in this copy) omits the surjectivity check for the inverse-image submodule. Step 3 writes that check explicitly. The statement assumes projectivity of all positive quotients, so neither the parent theorem's flatness hypothesis nor its nilpotent-projectivity lifting lemma is needed for this item.

The source's canonical map from the quotient of the inverse-image submodule to the quotient of E need not be injective. Step 4 uses it only as a map and Step 6 proves compatibility by representatives. No quotient-submodule identification is assumed.

The inherited blueprint.from records a supporting algebra input in the existing ancestry of `lem-trf-local-term-locality`. I read the current `literature/blueprint/latest/` (main-20261023-1620), including the unit and ancestor statement/proof, rather than an older snapshot. Its local-term result is not an alternative statement of this algebra lemma. Whole-blueprint searches for 05D3, projective modules, compatible sections and quotient splittings found no equivalent blueprint statement; same_as remains empty. The item is not the unit's key statement, so no unit record is written. The current chapter/unit route is retained, with no SGA source used.

## Unfinished work

None for this split. This is stage 1 only: no Lean was written and no compiler, Lake or build command was run. Independent maintainer review remains part of the delivery process.

## Not duplicates

No new nodes were created. Existing same-tag nodes were opened: `lem-trf-flat-projective-reduction-completion-splitting` is the parent using compatible sections to split the completed sequence; `lem-trf-adic-quotient-projective-short-exact` supplies quotient exactness and projectivity from flatness and level-one projectivity; `lem-trf-completion-flat-mittag-leffler` is a further ancestor about Mittag-Leffler completions. Citing any of them to prove this item would either give the wrong statement or introduce an ancestor cycle. The existing projective-module node already states the exact generic lifting property needed here. Finite-sum correction and quotient representative calculations stay proof steps, not new nodes.

## Review by Q89

I read Stacks Tag 05D3, from its statement through the induction's final composite, and Tag 05CE (`definition-projective`) with its following paragraph expressing projectivity as lifting maps along a surjection. I also read Tag 05CF (`lemma-characterize-projective`). For the sole cited DAG node I read its complete statement and Mathlib match, and the actual Mathlib `Module.projective_lifting_property` and `LinearMap.exists_rightInverse_of_surjective` in `Algebra/Module/Projective.lean` (lines 91 and 110 in this checkout). The node explicitly states the lifting property as an equivalence; I do not infer a theorem from a definition that lacks it. No new node needs a separate source review.

Step 1 uses the statement's inline definition of I^kL. I checked that finite sums of its generators are exactly the generated submodule; linearity of v sends such sums into I^kM. Surjectivity descends by lifting m under the given v. The reduction identity is verified on representatives. These are elementary calculations, without any exactness or flatness theorem.

Step 2 defines the precise inverse-image submodule in 05D3. The image of the R-linear section is a submodule, and its inverse image contains I^nE. If the reduction of z equals s_n(b), applying v_n gives b=[v(z)] because the prescribed map is a section. Thus the displayed identity uses no hidden choice of b and no injectivity of a quotient map.

Step 3 discharges the omitted surjectivity assertion with actual lifts. A representative z of s_n([m]) differs in image from m by a finite sum of a_j m_j, with a_j in I^n. Surjectivity of v gives e_j lifting each m_j; adding the sum of a_j e_j leaves the level-n reduction unchanged while making the image exactly m. No infinite sum, finite generating set of I, flatness, kernel exactness, or projectivity of E is used. This is a short calculation from the inline definition and is correctly marked elementary.

Step 4 checks both quotient maps separately. The denominator is I^(n+1)P, not P intersect I^(n+1)E; inclusion only needs the containment of the former in I^(n+1)E. Their formulas prove B-linearity, with B=R/I^(n+1); the source quotient is killed by I^(n+1), as required. Surjectivity of pi follows from the stronger P-to-M surjectivity already proved in Step 3.

Step 5 cites `def-weil-pbc-projective-module`, specifically its last sentence: every linear map from P lifts along every surjection. The projective module here is M_(n+1) over exactly B; the surjection is pi, whose source is also a B-module. Lifting its identity gives t, and composing with j gives a section. This step is marked non-elementary, since it invokes the existing lifting theorem/formulation; citations.json quotes the exact sentence used. No assertion of that cited node is strengthened.

Step 6 checks compatibility on every representative z in P using Step 2's equality. This proves q^E j=s_n q^M pi before composition with t. The equation pi t=id then proves the required compatibility with the originally prescribed s_n. All maps in that equality are R-linear; maps between adjacent levels are not mistakenly treated as linear over the smaller quotient ring without scalar restriction.

Step 7 cites the same node and the same lifting sentence over A_1 to obtain a starting section of the surjective v_1. Choosing a successor for each existing section, then ordinary natural-number recursion, yields the whole family. The induction has an explicit base and the extension property for every section, so it does not assume an already compatible family. This is marked non-elementary because of the projectivity use; the remaining choice/recursion is elementary logic.

I checked the B–E return cases against the actual files. There is no statement-only child hiding a proof, no new duplicate or restated clause, no unstated non-elementary theorem, and no use of another node's proof instead of its statement. Each proof citation has a verbatim quote. The proof-dependency union is exactly the two occurrences of the existing Mathlib leaf. No proof step has 2000 characters (the maximum is 696), and the finite-sum and representative calculations do not conceal an auxiliary lemma with new hypotheses. The report identifies the source's omitted calculation and supplies it, rather than merely repeating 'details omitted'.

Edge cases: I=0 makes all levels the original modules and Step 3 has zero correction; compatibility forces the same section. I=R makes all target quotients zero; the unique zero section and the construction still work. If M=0, E=0 when permitted by surjectivity, or R is the zero ring, the same formulas hold, including empty sums. Nontriviality is unnecessary. Infinite E/M and infinitely generated I are covered because membership in I^nM uses an individual finite sum, not finite generation of the module or ideal. A non-flat test M=Z/4 over R=Z, I=(2), E=Z also fits all quotient-projectivity hypotheses: the first two levels have their evident sections and later levels are excluded because Z/4 is not projective over Z/8. Thus there is no implicit claim that level-one projectivity alone suffices. For a non-flat system satisfying every level, take R=Z, I=0, M=Z/n only when M is projective (so it is not a counterexample); the proof consistently uses the stated projectivity at each level.

The five completed Q89 searches and their actual results were read, including the result whose process handle was lost in the pause: its durable log lists only completion extensions, individual-element corrections and ideal-power reduction definitions. I inspected the adic correction lemmas in `RingTheory/AdicCompletion/Functoriality.lean` (363–406) and the quotient-transition definitions in `RingTheory/Ideal/Quotient/PowTransition.lean`. These produce individual lifts or consume already compatible maps; they do not provide the item as an exact or one-line specialization. LeanSearch's single-splitting theorem is precisely the existing project's projective-module leaf. No unavailable search is passed off as a no-match result. Earlier imported search records are retained as historical records; none is claimed as a new Q89 invocation.
