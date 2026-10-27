# Stage-1 report: lem-sf-adic-qbar-constructible-realization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-adic-qbar-constructible-realization.json`: statement, split into twelve proof steps; no Mathlib match. Existing statement, source, ancestry and earlier searches retained.
- `citations.json`: one verbatim statement quotation for each of the 47 step/node citations.
- No new DAG nodes and no Mathlib leaves. The source extracts, search log and writing script are sandbox working files only.

## Attachments

None. I searched the project library under `lean/WeilConjectures/` for the exact blueprint tag and for qbar/constructible realization, rationalization, tensor and Hom terminology. There is no declaration stating this item with all its clauses. The existing rationalization-formula results concern ordinary scalar extension on modules, not this equivalence of constructible derived categories and its closed tensor maps.

## WANTED

None. Both cited papers are available locally. I read Bhatt–Scholze Lemmas 3.4.9–3.4.11, Proposition 6.6.11, Definitions 6.8.6–6.8.10, Lemmas 6.8.12–6.8.13, Proposition 6.8.14 and Remark 6.8.15, and Hemo–Richarz–Scholbach Proposition 5.2 with its proof, the adic comparison immediately before Theorem 7.7, Theorem 7.7, and Lemma 7.9. No SGA source is used.

## Problems found and changes made

The item was statement-only. Its supplied source describes the comparison categories, but not all the evaluation normalization and coherence that this particular native presentation needs. The proof is consequently marked `proof_origin.by = agent`: it assembles the existing paper-based DAG results and writes the canonical-map arguments explicitly. I did not change the statement or its hypotheses.

The raw rationalization is important. HRS describes a generally idempotent-completed rationalization; that is not silently substituted for our raw category. On the Noetherian schemes here, Bhatt–Scholze Proposition 6.8.14(2), already exposed by `lem-weil-pbc-condensed-e-realization`, is the raw equivalence without adjoining retracts. `lem-weil-pbc-integral-stratified-perfect-characterization` identifies the two integral domains before this equivalence is used.

Likewise the coefficient ring is the finite-subextension-valued condensed colimit, not the discrete field and not the unrestricted continuous-function condensed ring of the norm topology. The existing qbar descent and local-triviality nodes explicitly use this ring. I avoided the differently worded general admissible-scalar-realization node that allows unrestricted continuous functions.

The finite rational realization theorem supplies pullback comparison only for k-morphisms. That does not on its own cover semilinear geometric Frobenius. Step 12 instead uses the general scheme-isomorphism reindexing, inverse-image and scalar-comparison nodes, whose hypotheses require no k-linearity. The Frobenius sentence is applied when a finite-field descent datum supplies that isomorphism; an arbitrary finite-type k-scheme is not assigned a new Frobenius datum.

No assumption that a constructible complex is globally site-perfect is made. Instead, after proving the monoidal equivalence, I use the existing completed/rational tensor–Hom bijection, its arbitrary-target scalar-transpose compatibility, and constructibility of the ambient target internal Hom to prove invertibility by testing Hom groups.

## Unfinished work

None for this one-level split. All proof dependencies are existing DAG nodes; no new unsplit claims are introduced. The unit record is not changed because this item is not the unit's key statement.

## Not duplicates

No new nodes. The whole imported blueprint was searched using `blueprint_refs.py search` for qlbar, realization and 6.8.14; the existing two-colimit theorem is reused rather than restated. DAG searches found the existing raw condensed realization, integral characterization, tensor completion and scalar comparison nodes. The ancestry command returns `None` for the nearest imported ancestor, as already recorded by the item's creator; its supplied provenance is preserved and `same_as` is empty.

## Mathlib search results

All five new searches are in `searches.jsonl`, copied without changing their query strings into `mathlib_searches`, in addition to the existing Q10 records. Two differently phrased LeanFinder searches returned general condensed-module and monoidal-category infrastructure; LeanSearch returned filtered module colimits, ind-object presentation and colimit exactness; Loogle returned no hits. The grep hits concern quadratic radicals, monadic adjunctions, local cohomology and adic completions. None states the comparison for constructible pro-etale sheaves or specializes to it in one line. The useful general tensor and derived-category infrastructure is already represented by existing DAG nodes, so these searches create no new leaves.

## Review by NW

I reviewed the written node against delivery-errors B–E, with the paper excerpts and each cited node's statement open. The proof uses existing statements, not facts hidden inside their proofs. There are no new-node source, notation, self-containedness or same-tag-duplicate obligations. Every step is below 2000 characters, and the two formal representative arguments are kept as steps, not manufactured into separate lemmas. The original statement and all eight statement dependencies are retained.

Step 1 uses the finite-type Noetherian-base and finite-dimension statements with base Spec(k); k is a field and hence has only two ideals. The integral characterization explicitly says that its conditions describe the same completed-ring full subcategory as `def-weil-derived-complete-integral-detailed`. Thus the rationalization definition really gives identical raw domains. Empty T is allowed; a dimension bound can be chosen arbitrarily for it, and ell remains invertible.

Step 2 uses the actual E-linear equivalence and locally-finite-free clause in `lem-weil-pbc-condensed-e-realization`. The qbar local-triviality statement explicitly converts local finite presentations to finite free modules on a Noetherian scheme; it can be applied separately to every locally closed stratum. The bounded-constructible and finite-valued qbar definitions match precisely the target's cohomology condition and coefficient ring.

Step 3 uses `lem-weil-finite-free-completed-scalar-comparison`, which identifies the specific strict-tower extension with ordinary derived change of completed rings, not merely an unrelated extension preserving constructibility. Its derived completeness hypothesis holds by step 1. The scalar calculus and internal multiplication normalization state the balanced multiplication comparisons and their unit/tower laws. The pure rational-arrow formula in the rationalization definition ensures that the square applies to all Hom groups. Step 4 then checks equality of representatives and composition at one common stage directly, with no extra existence assertion.

Step 5 uses exactly clauses (2) and (3) of `sk-thm-sfb-qlbar-two-colimit`: Hom colimit at r=0 and object descent. Both coefficients are first brought to the compositum, then the equivalences of step 2 identify their finite-stage Hom groups, and step 3 identifies the transition maps. Thus it proves full faithfulness and essential surjectivity of the functor actually constructed. Step 6 uses the exact derived change-of-rings functor and the common-stage distinguished-triangle definition; its shift map is the same derived scalar map.

Step 7 uses the canonical ordinary-to-completed tensor isomorphism for constructible inputs, which are in its qcqs, ell-invertible domain. I corrected the tensorator direction explicitly: J(K) tensor J(L) first maps by balanced multiplication to J(K tensor L), then by J(chi) to J(K completed-tensor L). I added the existing `lem-sf-ringed-finite-free-tensor-data` after checking that the generic change-of-rings theorem alone did not state preservation of K-flatness or supply a tensorator. Despite its name, this tensor-data statement applies to ANY ring-sheaf map, so there is no unsupported finite-free hypothesis on B_E to E_T. The cochain tensor statement gives exactly the displayed pure tensor formulas, Koszul symmetry, unit and composition equations. The remaining compatibility with chi is checked in its specified quotient-to-Roos chain model, whose shifted-product component is zero; this is not an inference from arbitrary choices of derived-limit cones. Step 8 extends these equations linearly and checks them at one common finite field, using the actual coefficient-passage tensor definition and scalar-localization monoidal theorem. Rank zero and the zero object cause no changes, and the unit maps by multiplication.

Step 9 uses the completed/rational transpose theorem under precisely its permitted constructible-Hom hypothesis. Its rational part concerns all rationalized arrows, not only integral maps. The scalar-transpose theorem is explicitly for any constructible target W, so using N rather than a dualizing object is legitimate. This is what makes the bijections pass to common-stage colimits. The signed symmetry changes its first-input evaluation convention to the item's Hom-first convention.

Step 10 uses the ambient Hom-preservation statement, whose coefficient list includes our finite-valued qbar ring through its defining node, and the closed derived tensor-Hom adjunction with its stated evaluation formula. Thus Q is in the full target and all tests are valid. I wrote the two-test inverse argument: surjectivity at Q produces d with cd=1; injectivity at rho(H) gives dc=1. This proves invertibility of the prescribed evaluation-transpose c in the ambient category, rather than replacing it with a separately chosen isomorphism.

Step 11 uses the actual evaluation-defined scalar Hom tower identity and its identity-ring clause, together with the tensor-tower normalization and arbitrary-target rational transpose statement. Their claims are identities of maps, so they supply the required finite-extension and naturality equations. The proof explicitly compares transposes under an injective adjunction; it does not assert compatibility merely because both paths are isomorphisms.

Step 12 uses the scheme-isomorphism inverse-image statement, which explicitly gives reindexing and an exact equivalence preserving all limits and colimits. The pulled-back coefficient theorem identifies the coefficient rings for every scheme morphism. The integral isomorphism-pullback and scalar-comparison statements apply to arbitrary scheme isomorphisms with ell invertible, not only k-morphisms. The inverse-image tensor/Hom statement supplies its tensor and coefficient formulas, and the cochain comparison supplies identity/composition and scalar/tensor compatibility. Applying the same evaluation-transpose uniqueness gives the Hom equation. This verifies the Frobenius clause without the missing k-linearity hypothesis.

I tested the proof on empty schemes, zero/rank-zero complexes, units, equal coefficient fields, two objects initially over different fields, torsion integral representatives killed by rationalization, and semilinear scheme isomorphisms. Nothing requires a nonempty stratum, an integral lattice that is lisse on all T, a globally perfect first Hom input, or a chosen splitting of a rational idempotent. All off-unit statement citations are declared as generic tools in `split_report.tool_uses`; no biduality route is replaced. The server `review_split` check and the first complete delivery dry run passed. A final dry run rechecks the tensorator direction correction before push.
