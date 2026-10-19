# Q80: lem-pod-hom-chain-counit-formula

## Files written

- `dag/nodes/sec-six-functors/lem-pod-hom-chain-counit-formula.json`: statement, now split into six steps. No exact full-item Mathlib match; all component laws reuse existing nodes.
- `citations.json`: one literal statement quotation per proof-step citation.
- `searches.jsonl`, `search-0.txt` through `search-4.txt`: actual Q80 Mathlib searches and their full printed results. The item's inherited Q19 search records are retained, not attributed to Q80.
- `report.md`; `write_split.py` is sandbox-only preparation code.

There are **0 new nodes and 0 new Mathlib leaves**. The item statement, statement dependencies, creation record, chapter, unit and blueprint ancestry are unchanged. Only the split, search records and report fields are supplied. No unit realization changes are appropriate: this is an extracted calculation, not the unit key theorem.

## Attachments

None. Searched the whole project `WeilConjectures/` tree in `/home/ubuntu/weil-src-slopmaster2` for `lem-pod-hom-chain-counit-formula`, `hom.chain.counit`, `counit.formula`, and inverse tensor–Hom wording, then inspected the related adjunction/counit occurrences in `SixFunctors/` and the declarations of `SixFunctors/Etale/Derived/PoincarePairing.lean`. The latter concerns Poincare pairings with additional geometric hypotheses; it does not state this formula for arbitrary M,N,f and all five specified bijections. No exact project attachment was found. No compiler or Lake command was run, and upstream master was not used as evidence of a proof.

## WANTED

None: the blueprint, Stacks adjunction definition and Mathlib source used here are present locally.

## Findings and corrections

The imported item had no proof. Its mathematical statement is retained. The needed input is the actual exceptional adjunction stipulated by the item, not an assertion that an unrestricted ambient exceptional right adjoint exists. In particular, `fix-prop-adjunctions` is conditional in its exceptional clause; this split never drops that condition or tries to prove existence.

The five arrows have different directions: the first three are inverse Hom-equivalences, the fourth is precomposition with P_T (not its inverse), and the last is currying. The proof writes those directions explicitly. Writing q_N for evaluation after the ordinary counit isolates the only simplification: projection naturality takes Rf_!(1 tensor Lf^*t) across P_T, producing P_{A_N}(1 tensor t). This gives w_t=p_N(1 tensor t), so injectivity of uncurry identifies the final morphism.

Naturality is not left as an unnamed compatibility or a claim that transport preserves the calculation. Step 5 writes the equation for s:T' -> T. Step 6 writes the ordinary-counit, evaluation, exceptional-counit and projection equations for r:N -> N', obtaining p_{N'}(1 tensor a)=r p_N and then k_{N'} a=b k_N. The formulas are calculated in the actual category at each chosen coefficient stage; no finite-reduction detection or scalar-descent theorem is invoked. No statement dispute was found.

## Not duplicates

No new nodes. Existing generic components are reused: `lem-weil-pbc-adjunction-of-natural-bijection` supplies the inverse Hom-equivalence formula, and `lem-pod-closed-uncurry-laws` supplies evaluation and uncurry naturality. Whole-blueprint searches for `counit formula` and `Hom chain` found no blueprint nodes stating the full item. The broader `tensor–Hom` search found the existing restricted adjunction and tensor–Hom exchange nodes; an exchange-isomorphism theorem does not itself state this explicit representative for every t. The item's nearest blueprint ancestor remains `thm-pod-identification-of-the-comparison`, through `lem-pod-global-duality-map-identification`, as confirmed by `tools/blueprint_refs.py ancestor`.

## Mathlib searches

Ran `msearch.py Q80 lem-pod-hom-chain-counit-formula` with leanfinder, loogle, grep and leansearch, followed by a second semantic phrasing with leanfinder. Read all printed hits. All five services/calls succeeded. Loogle returned `CategoryTheory.Adjunction.homEquiv_counit`, the component already represented by the existing adjunction node. Read `Mathlib/CategoryTheory/Adjunction/Basic.lean`, lines 159–182: the inverse is literally F.map(g) followed by the counit. Read `Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean`, lines 145–194, including curry/uncurry, both naturality directions and the evaluation formula. The second leanfinder search returned parametrized Hom-equivalence naturality; read `CategoryTheory/Adjunction/Parametrized.lean` to verify that it states naturality of a supplied adjunction, not the five-equivalence composite with projection. The other hits concern slice-category exponentiable maps or underived module-sheaf pullback, so they cannot directly state this full item. Consequently the whole item is split, while its already-catalogued Mathlib components are cited without making new leaves. The query texts and outputs are copied verbatim into the appended search records.

## Review by Q80

I read the chapter record `dag/chapters/sec-six-functors.json` and the package unit `dag/units/sk-thm-sf-package.json`. This is the package's adjunction/projection calculation within duality; it does not replace the package route by a different duality theorem. I read `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md`, especially Step 1, and `thm-pod-identification-of-the-comparison.proof.md`, especially the third paragraph identifying the induced map. I also read the restricted-adjunction statement and proof in `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-adjunctions.md` and its `.proof.md`. They justify using the same adjunction bijections and counits on full finite-Tor subcategories. There are no new nodes whose sources require separate review.

For step 1 I opened all three cited DAG statements. `det-thm-sf-ctf-stability-adjunctions` explicitly places the ordinary, tensor–Hom and exceptional adjunctions on the full ctf subcategories, so the objects A_N and C used as finite-Tor inputs really have the required domains. `fix-prop-adjunctions` names the specified ordinary and exceptional counits; I use its exceptional clause only under the supplied exceptional adjunction. `fix-prop-projection-formula` applies with K=M and L=T (and later L=A_N); it explicitly asserts invertibility and naturality at all four stages. Its finite-Tor hypothesis holds by M,T and the restricted adjunctions. These are theorem interfaces, not properties inferred from definitions. Their uses outside the item's unit are declared in `split_report.tool_uses` as the existing adjunction/projection inputs; no proof route is replaced.

For step 2 I opened the statement of `lem-weil-pbc-adjunction-of-natural-bijection`, which explicitly contains Psi^{-1}(b)=epsilon composed with F(b), and the statement of `lem-pod-closed-uncurry-laws`, which explicitly identifies uncurry(v) with evaluation after 1 tensor v. I checked the former against Stacks Tag **0037**, `literature/stacks-project/categories.tex`, label `definition-adjoint` and the following paragraph: its third equivalent characterization is exactly the formula used. I checked the latter against its cited Mathlib lines 175, 180 and 194. The remaining equality in step 2 is merely functoriality of the fixed-left-input tensor functor; the tensor order remains M first throughout.

For step 3 the same generic inverse-adjunction statement applies to Rf_! left adjoint Rf^!, hence the third map is mu_N after Rf_!(v_t). The quoted projection statement explicitly says natural in K,L. At the arrow t:T -> A_N its naturality square has exactly the displayed equation, with P_T on the source and P_{A_N} on the target. Factoring q_N through that square gives p_N(1 tensor t); neither a projection formula for nonproper Rf_* nor a mate-invertibility principle is used.

For step 4 the closed-uncurry statement gives both uncurry(curry(p_N))=p_N and uncurry(k_N composed with t)=uncurry(k_N) composed with (1 tensor t). Since curry/uncurry are inverse bijections, equality of those uncurried maps proves the required equality, without Yoneda or any conservativity assertion. Step 5 uses only this already-established formula and associativity, so it has no external citation.

For step 6 the generic adjunction node explicitly calls units and counits natural transformations. Thus its two counit equations apply to h and r with precisely the displayed types. The closed-uncurry node explicitly states that its chosen Hom bijection is natural in the tensor variable and target. Inverse naturality in the target, evaluated at the identity of L_N and using its evaluation formula, gives the displayed evaluation equation. Substitution, Rf_! functoriality and the cited projection naturality give p_{N'}(1 tensor a)=r p_N. Applying the same chosen Hom bijection in its two variables gives k_{N'} a=b k_N, and composing with t proves naturality of Phi. I checked that a has source A_N and target A_{N'}, while b has source B_N and target B_{N'}; no variance is reversed.

Small cases checked: with f the identity and the canonical identity adjunctions, q_N and p_N reduce to evaluation and the formula is curry(evaluation) composed with t=t. With M=0, N=0, or T=0, the appropriate Hom sets have only the zero map and both sides are zero. The empty-source case likewise has zero compact-support object and causes no exception. For arbitrary shifts no symmetry or reassociation of tensor factors occurs, so no hidden Koszul sign is introduced. The proof uses no finite-dimensionality, properness, smoothness or perfection beyond the stated finite-Tor domains. Higher coefficients require no claim that arbitrary internal Homs commute with finite reduction: all formulas are internal to the adjunctions already supplied at that stage.

Against delivery-errors B–E: there are no new nodes, thus no new statement-only, notion-definition, duplicate-tag or source-tag issues. Every non-elementary input is an existing cited theorem, including the actual naturality and counit formulas; none is taken from a cited node's proof. Every citation is backed by a full verbatim statement in `citations.json`. The proof's content remains in the six computation steps and has not been moved into a new node or a restatement of the item. The only non-elementary step is setting up the existing bijections; the ensuing calculations are explicit applications of the cited laws and functoriality. All steps are shorter than 2000 characters, and I found no hidden comparison or auxiliary lemma requiring extraction. Imported metadata and the item statement remain unchanged. All work is confined to the item sandbox; no Lean, compiler, Lake, live-project write or direct git command was used.

## Unfinished work

None in the mathematical split. Required server dry run and direct delivery are the final validation actions; their result is reported by the delivery command.
