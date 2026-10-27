# Repair: algebraic-closure internal Hom coefficient comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-qlbar-internal-hom-coefficient-comparison.json`: item, split; its statement is byte-for-byte unchanged. The four assembly steps total 2360 characters, below 3000.
- `dag/nodes/sec-six-functors-basics/lem-sfb-qlbar-tail-finite-free-algebra-presentation.json`: statement, unsplit; no Mathlib match, 2151 statement characters. A coefficient-algebra/index/universal-property task independent of any derived inputs.
- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-section-hom-continuity-comparison.json`: statement, unsplit; no Mathlib match, 3075 statement characters. A derived-presentation/naturality/evaluation-normalization task independent of algebraic-closure colimits.
- `citations.json`: full verbatim cited statements, one entry per step/use.
- `searches.jsonl`: ten searches actually run, five per new node, retaining returned tool results/digests. No unavailable service is counted as a negative match.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the blueprint tag and coefficient/field/continuity concepts and read `lean/Sheaf/Paper/QlbarInternalHomCoefficientComparison.lean`. The main theorem at line 480 has `sorry` at line 486; `fieldDiagram`, `coefficientRingColimit`, `coefficientModules` and `coefficient_comparison_roof` likewise have `sorry`. These are useful interfaces, not finished attachments. No Lean file was changed and no compiler was run.

## WANTED

None. Sources needed for this extraction are available locally.

## Return repaired

The returned six-step proof carried 5920 characters according to the return (the live JSON has a few subsequent interface dependencies). Merely shortening it would not distribute work. New task A carries the complete content of old steps 1–3: the small cofinal field tail, finite freeness, actual field transitions, and the ring/S-algebra/module colimit with specified legs. New task B carries old step 5 and its normalization application in step 6: exact presentation equivalences, lower bounds, continuity maps, scalar adjunctions, the native evaluation-transpose map and every stage/transition square. The elementary exactness transfer of old step 4 remains written out as assembly step 2. The application of the already-existing general theorem from old step 6 remains as assembly step 4. The old six paragraphs are reproduced verbatim below with explicit assignment, so no argument or citation is lost to a summary. Both tasks are statement-only with `status: unsplit`, empty proof and proof_deps, null proof_origin, and actual recorded searches.

The sandbox initially contained only dispatcher marker files, despite the brief's statement that a delivery was retained. I copied the current live item as the returned head; it contains the exact six arguments and reviewer transport repair described in the return. The required initial dry run exited because report.md was missing. The live statement and maintainer-owned metadata were retained. The first standalone server review_split returned PASS (its count of new nodes was zero, so final deliver.py preflight remains the decisive check of the complete delivery).

The parent uses lem-sfb-qlbar-flat explicitly to verify the exact-extension hypothesis of the normalized scalar transport. This is available on every scheme, so it introduces no additional assumption on X, K, L. No statement dispute arose. No changes to the chapter, unit route, targets, or definitions were made. The inherited blueprint ancestor command returns None because the provenance chain ends at a module name; new nodes use that same null ancestor and explicit proof-place descriptions, with via beginning at this item. This preserves provenance instead of inventing an imported ancestor.

## Review by N5

I read AGENTS.md, the stage-1 brief, stage document, the three blueprint levels in SETUP, GOAL, the chapter and restricted-functor unit, and delivery-errors B–E. I read the current blueprint's final algebraic-closure paragraph of lem-sfb-dc-hom-preserves.proof.md, the coefficient finite-free proof, and Bhatt–Scholze Lemma 6.8.2(2) on pp. 58–59 and Proposition 6.8.14/Remark 6.8.15 on pp. 61–62. The latter motivate coefficient passage but do not assert our conditional unbounded internal-sheaf comparison verbatim. The extracted claims are explicitly agent formulations, using the existing general theorem. I read sites-modules 03CO/lemma-limits-colimits-abelian-sheaves, 03DA/lemma-abelian, 03DB/lemma-limits-colimits and 03EK/section-tensor-product, and sites-cohomology 08J9/lemma-internal-hom and 0A95/lemma-RHom-well-defined. No prohibited source was used.

For step 1 I checked every assertion supplied by task A: I and I_E are sets of subfields of the fixed coefficient set; E supplies nonemptiness, composita supply directedness and EH supplies a directed nonempty upper cone for cofinality. A finite E-basis gives finite freeness; F=E is rank one. Given a tail cocone t_F, the extension t_H=t_EH a_(H,EH) is compatible with inclusions because the maps a compose and the q maps agree; the full coefficient colimit gives a unique map. Its E-leg fixes the S-algebra structure. The existing tail-module-colimit statement identifies the underlying module cocone with exactly those legs, not an arbitrary object isomorphism. These are all conclusions of task A as stated. This task has no K or L and is strictly smaller than the parent.

For step 2 I reopened both cited statements. lem-weil-pbc-module-sheaves-colimits-forgetful explicitly gives faithful exact forget, existence of small colimits and preservation of them. lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact explicitly gives exactness for every small filtered category. Forget a diagram of short exact module sequences, use its abelian-sheaf exact colimit and reflect exactness by faithful exact forget; this is the elementary two/three-line transfer, so it is not another queued node. The diagram is small by step 1. No claim that section evaluation preserves arbitrary colimits is used.

For step 3 I checked lem-sfb-qlbar-flat: its conclusion is exact scalar extension for every scheme, which is precisely task B's extra coefficient-map hypothesis. I read the existing module-object/ringed-site-derived-comparison statement: it supplies a natural Hom isomorphism preserving evaluation, but says nothing about continuity diagrams or the simultaneous scalar comparison. I read internal-section-tensor-comparison: it supplies exactness, total tensor, K-flatness, units and symmetry. I read internal-section-scalar-adjunction: it preserves derived extension/restriction and the specified unit/counit with the pure-section formula. Together these are the interfaces for task B. Its statement actually asserts identification of both continuity maps and scalar evaluation transposes, all their diagram squares, and lower bounds; it does not replace these by a vague claim of transport. The direct proof to be written by the next worker is to apply the exact termwise equivalence to a functorial representative diagram, use its unchanged colimit cocone and natural Hom comparison, and compare evaluations. For the scalar map, transpose the two candidate maps; the normalized tensor and scalar-unit comparisons and Hom evaluation square give the same extended evaluation, so adjunction injectivity identifies them. Naturality and transition squares follow from these same natural equations; filtered cocones then give their composite equation. The old transport paragraph is retained below. This is a genuine simultaneous comparison argument, independent of finite fields, and no coefficient comparison isomorphism is assumed or concluded here.

For step 4 I reopened lem-sfb-dc-hom-filtered-colimit and checked its precise hypotheses: small filtered I; finite-free algebra stages; S-algebra and module colimits with compatible legs; exact filtered module colimits; continuity for that I; cohomologically bounded-below L. Task A, step 2 and task B give these respectively. The parent's hypothesis quantifies over every small filtered diagram, so it covers I_E. The cited theorem explicitly concludes the D(T) evaluation-transpose isomorphism, naturality, three-arrow formula, transition compatibility and basis independence. Task B identifies these exact maps with the native maps, so it gives every parent clause. The bounded-below representative is only for L; no lower bound for RHom(K,L), no constructibility, perfection or completion has been added.

I tested E=Q_l, F=E, a stationary diagram, X empty, K=0, L=0 and shifted bounded-below L. In task B the identity ring map gives the identity comparison; zero diagrams and diagrams with any common negative bound preserve the same bound. Arbitrary unbounded K is permitted, and continuity is not asserted for arbitrary K: it is transported as an equivalence of conditions. The finite-free tasks never choose bases for the maps themselves. New statements introduce every object and cite its defining notions. There is no proof sketch in a new statement, no dependency back to the parent, and the only remaining elementary argument stays in the parent. Each non-elementary assembly step is under 2000 characters; every new task is independently claimable. The parent statement was compared exactly with the live copy. After the first successful dry run I made the coefficient-diagram quantifier explicit in task B and verified stagewise exact extension in assembly step 3 by finite direct sums. These edits do not change either Mathlib search question. I corrected the inherited surplus proof_deps to equal the union of uses.

## Mathlib search review

Each new node has LeanFinder in two distinct phrasings, Loogle, source grep and LeanSearch, all through msearch.py. Task A's semantic hits concern field-embedding filtrations, ordinary ring colimit factorization or local cohomology; none includes pulled-back coefficient sheaves with the tail algebra/module cocone. Its Loogle and grep searches had zero hits. Its LeanSearch request was rate limited and is recorded unavailable. Task B's hits concern ordinary module scalar adjunctions, sheaf Hom sections, AB5 for condensed modules or underived light-condensed closed structures. They do not identify the derived internal-to-section continuity/evaluation maps. Its Loogle and grep searches had zero hits. Neither new node is a Mathlib leaf. The inherited item searches remain unchanged because its statement and search question did not change.

DAG and blueprint searches included cofinal finite, cofinal field, finite intermediate, continuity evaluation, section-ring, evaluation-normalized and internal Hom, plus whole-DAG statement scans for finite-field/cofinal and continuity/ringed-site combinations. No imported node states either extracted result. I read the existing field, coefficient, colimit and transport interfaces; the closest pairs are distinguished below. Definition-only diagram/cocone nodes assert no universal property, and the existing general comparison is ringed-site, so neither new node can be replaced by one of them.

## Not duplicates

lem-sfb-qlbar-tail-finite-free-algebra-presentation vs lem-sfb-qlbar-tail-module-colimit: The existing statement gives the directed tail and its section-ring module colimit. Task A also proves small cofinality in the full finite-field poset, finite freeness, and the ring/S-algebra universal property with the same specified legs.

lem-sfb-qlbar-tail-finite-free-algebra-presentation vs sk-prop-sfb-qlbar-colimit-x: The existing full-index coefficient-ring colimit has no fixed-E tail, cofinality or E-algebra universal-property clause; task A verifies that tail presentation with its actions.

lem-sfb-qlbar-tail-finite-free-algebra-presentation vs sk-prop-sfb-cartesian-coefficients: Its finite-free clause treats individual finite extensions, and its main clause is inverse-image compatibility; it gives neither a cofinal field-tail diagram nor its algebra colimit.

lem-sfb-qlbar-tail-finite-free-algebra-presentation vs def-sfb-qlbar-ring-object-cocone: This defines a bundled full-index ring cocone and explicitly asserts no colimit property; task A proves the fixed-E tail universal properties.

lem-sfb-qlbar-tail-finite-free-algebra-presentation vs det-def-sfb-qlbar-condensed-subextensions: Finite composita and union of fields are algebra facts; task A adds the fixed-E cofinal tail and the pulled-back finite-free algebra/sheaf colimit presentation.

lem-sfb-internal-section-hom-continuity-comparison vs lem-pe-internal-section-tensor-comparison: Exact monoidal/K-flat comparison for one ring, not continuity of derived internal Hom or its scalar evaluation-transpose comparison.

lem-sfb-internal-section-hom-continuity-comparison vs lem-pe-restricted-kflat-tensor-identification: Reorders scalar-first/last tensor representatives across three ring sheaves; it does not compare internal-module and section-ring Hom or continuity.

lem-sfb-internal-section-hom-continuity-comparison vs lem-pe-successive-quotient-flat-complex-sequence: Constructs a degreewise short exact sequence for principal-power quotients tensored with a flat-term complex; it has no internal-to-section derived Hom assertion.

lem-sfb-internal-section-hom-continuity-comparison vs def-sfb-scalar-extension-pure-tensor-section: Defines ordinary sheafified pure tensor sections only, without any derived Hom or continuity assertion.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sf-completed-tensor-finite-shift: A signed total tensor shift isomorphism for completed integral coefficient towers, not a Hom comparison across the two module presentations.

lem-sfb-internal-section-hom-continuity-comparison vs lem-weil-ramified-finite-pullback-comparison: A finite pullback/base-change isomorphism at ramified coefficient indices, not internal-to-section Hom/continuity transport.

lem-sfb-internal-section-hom-continuity-comparison vs lem-weil-finite-pullback-transition-generators: Computes pullback-tower maps on pure generators under quotient reduction; it does not concern derived Hom continuity or section reconstruction.

lem-sfb-internal-section-hom-continuity-comparison vs def-sf-unrestricted-reduction-complex-constructions: Defines ordinary coefficient reductions and K-flat computation maps of towers, not continuity and scalar-Hom comparison under a module equivalence.

lem-sfb-internal-section-hom-continuity-comparison vs lem-trf-site-balanced-tensor-chain: An ordinary chain-level associativity/balancing isomorphism for two ring sheaves and one degree-zero module, with no derived internal-to-section Hom statement.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sf-finite-intrinsic-tensor-generators: Compares ordinary tensor across the etale-to-proetale finite-constant-coefficient realization, not the internal-module/section-ring equivalence or derived Hom continuity.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sf-finite-intrinsic-chain-tensor-generators: Compares total tensor complexes across the finite-coefficient site realization, not scalar-Hom and continuity maps across module presentations.

lem-sfb-internal-section-hom-continuity-comparison vs lem-weil-ramified-coefficient-quotient-comparison: Constructs ramified quotient coefficient data and transition equations, with no internal-to-section derived Hom or continuity comparison.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sfb-module-object-ringed-site-derived-comparison: Provides a natural evaluation-preserving Hom isomorphism for one coefficient ring (and slices); task B proves the simultaneous scalar extension square and continuity-map comparison, neither stated there.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sfb-internal-section-scalar-adjunction: Compares extension/restriction and their unit/counit, not the resulting derived Hom scalar transpose or continuity comparisons.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sfb-hom-flat-evaluation-roof: Identifies a ringed-site scalar-Hom map with a strict evaluation roof; it never compares native internal-module and section-ring presentations or continuity.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sfb-dc-hom-filtered-colimit: Proves invertibility under continuity for finite-free ringed-site diagrams; task B does not prove invertibility and instead compares the two presentations and their hypotheses/maps.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sfb-rhom-colimit-source-transport: Compares source isomorphisms and signed source shifts within one ringed-site presentation, not an equivalence between internal and section-ring modules.

The final dry run used the server current DAG, whose tag-match order differs from this read clone; I opened each of its twelve additional matches and compared the full statements. None says task B.

lem-sfb-internal-section-hom-continuity-comparison vs lem-pc-sheaf-modules-tensor-closed: Closed symmetric monoidal structure on ordinary sheaves of modules; no derived presentation equivalence, scalar-Hom square or filtered-continuity comparison.

lem-sfb-internal-section-hom-continuity-comparison vs lem-pc-sites-sheaf-tensor-bilinear-universal: The ordinary sheaf tensor universal property for bilinear maps; task B concerns derived Hom and scalar/continuity maps under internal-to-section equivalence.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sc-hom-tensor-comparison-natural: Naturality of ordinary sheafification/tensor comparison for two module maps; it has no derived internal-Hom or change-of-presentation claim.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sc-hom-tensor-reverse-pair: Ordinary sheaf-Hom currying on local pure sections in one ringed-site category; it does not compare module presentations or derived continuity/scalar transposes.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sc-hom-tensor-section-natural: An equality of presheaf module maps involving the ordinary tensor-section unit; it asserts no derived equivalence or Hom continuity comparison.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sc-hom-tensor-summand-localized-ext: An extensionality criterion for ordinary maps into sheaf Hom of a single tensor; task B compares derived Hom/scalar/continuity transformations.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sc-hom-tensor-summand-restriction-ext: An extensionality criterion using total tensor summand inclusions in one degree; task B has no such summand criterion and concerns derived presentation equivalence.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sc-internal-hom-coproduct-fan: Ordinary contravariant Hom takes a coproduct cofan to a product fan in one module-sheaf category; no module-presentation or derived scalar comparison is asserted.

lem-sfb-internal-section-hom-continuity-comparison vs lem-sc-internal-hom-product-fan: Ordinary covariant sheaf Hom preserves a product fan within one module category; it says nothing about internal-to-section derived continuity or scalar-Hom maps.

lem-sfb-internal-section-hom-continuity-comparison vs def-pd-proetale-section-module-functors: Defines ordinary direct/inverse image and open-extension structures and tensor normalizations across section reconstruction; it does not assert the derived Hom continuity or coefficient scalar square.

lem-sfb-internal-section-hom-continuity-comparison vs def-pd-section-module-operations-data: Defines geometric module direct/inverse image and open extension data; task B is a theorem about derived internal-Hom/scalar/continuity maps at a fixed site.

lem-sfb-internal-section-hom-continuity-comparison vs lem-pd-ringed-direct-image-pairing-lax: Uniquely specifies an ordinary ringed direct-image lax monoidal structure by pure tensors; no derived internal-to-section Hom continuity or scalar transpose assertion.

## Preserved returned proof and task handoff

The following is the complete returned argument, not proposed proof steps inside new unsplit node files. Each task can reuse the cited interfaces after independently checking them.

### Returned step 1 → Task A

Let $I$ be the poset of finite intermediate fields of $\Omega/\mathbf Q_\ell$, and $I_E$ its full subposet on fields containing $E$. These are small in the stipulated coefficient universe: an intermediate field is a subfield of the fixed set $\Omega$, hence these collections are sets there. The finite-compositum statement gives $FG\in I_E$ for $F,G\in I_E$, while $E\in I_E$. Thus $I_E$ is nonempty and filtered. For $H\in I$, $EH$ is finite and contains both $E$ and $H$. More explicitly, the poset of objects of $I_E$ above $H$ contains $EH$ and is directed by composita. Hence the inclusion $I_E\subseteq I$ is cofinal. These assertions require no condition on $X$.

Uses: def-weil-size-convention, det-def-sfb-qlbar-condensed-subextensions.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Lemma 6.8.2(2), finite-subextension index; explicit finite-compositum and smallness verification.

### Returned step 2 → Task A

For $F\in I_E$ put $A_F=F_X$ with its $S=E_X$-algebra structure induced by inclusion. For $F\ne E$, the finite-free coefficient lemma gives $A_F\cong S^{\oplus[F:E]}$; for $F=E$ use the identity $S\cong S^{\oplus1}$. This only chooses bases to verify the finite-free hypothesis. It does not define any comparison map using those bases. All coefficient transitions and cocone legs are the maps induced by the actual field inclusions.

Uses: sk-prop-sfb-cartesian-coefficients, def-sfb-subfield-coefficient-map, def-sfb-subfield-to-qlbar-coefficient-map.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/_section.md; Assertion (2), finite-free coefficient sheaves; identity extension treated separately.

### Returned step 3 → Task A

Write $a_{H,J}:H_X\to J_X$ for an inclusion and $q_H:H_X\to T$ for the closure coefficient map. The coefficient-composition lemma gives $q_Ja_{H,J}=q_H$; the maps $a$ themselves compose as their field inclusions do. The full ring-sheaf colimit is $T$ by the coefficient-colimit theorem. Its restriction to $I_E$ has the same universal property: given a ring-sheaf cocone $t_F:F_X\to B$ on $I_E$, extend it to $I$ by $\widetilde t_H=t_{EH}a_{H,EH}$. If $H\subseteq J$, then $EH\subseteq EJ$ and the cocone equation gives $\widetilde t_Ja_{H,J}=\widetilde t_H$. The full colimit therefore gives a unique $t:T\to B$. For $F\in I_E$, $EF=F$, so $tq_F=t_F$; conversely these equations force $tq_H=t_{EH}a_{H,EH}$ for every $H$, proving uniqueness. Thus the ring-sheaf colimit of the tail is $T$ with the specified $q_F$. For an $S$-algebra cocone, $tq_E=t_E$ is its structural map from $S$; the same universal map is therefore $S$-linear and gives the $S$-algebra colimit. The tail-module-colimit lemma supplies the underlying $S$-module colimit with these very same maps and actions. In particular $q_Fa_{E,F}=q_E$, as needed for a diagram of $S$-algebras.

Uses: lem-sfb-subfield-coefficient-map-comp, sk-prop-sfb-qlbar-colimit-x, def-weil-pbc-category-colimit, lem-sfb-qlbar-tail-module-colimit.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Lemma 6.8.2(2); explicit restriction of its coefficient-ring colimit to F containing E, followed by the existing tail module comparison.

### Returned step 4 → assembly step 2 (elementary exactness)

Filtered colimits of $S$-module sheaves are exact on the chosen small site. Indeed, forget a small filtered diagram of short exact sequences to abelian sheaves. The module forgetful functor is exact and preserves its colimit, and filtered colimits of abelian sheaves are exact. It is faithful, so the vanishing of the underlying kernel/image quotient implies its vanishing as a module sheaf; it therefore reflects exactness as well. This proves the required exactness for precisely the small filtered index $I_E$. These are sheaf colimits, rather than an assertion that arbitrary section functors preserve colimits.

Uses: lem-weil-pbc-module-sheaves-colimits-forgetful, lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact.

Source: literature/stacks-project/sites-modules.tex; Tag 03DA (lemma-abelian), Tag 03DB (lemma-limits-colimits), and Tag 03CO (lemma-limits-colimits-abelian-sheaves).

### Returned step 5 → Task B

Transport to ringed-site module sheaves. The item's $D(S)$, $D(T)$, $\otimes^{\mathrm L}$ and $R\mathcal Hom$ are those of module objects over the ring objects $S=E_X$ and $T=\Omega_X$ [sk-def-sfb-derived-tensor-hom], while the general comparison of step 6 is stated for sheaves of modules over a sheaf of rings, its K-flat tensor and the K-injective model $H_R$. Apply the module-object/ringed-site comparison to $B=S$ and to $B=T$: the equivalence $F$ leaves underlying abelian sheaves, sections and maps unchanged, its termwise extension $D(F)$ identifies the K-flat relative tensor with the ringed-site one (the tensor comparison: $F$ is exact, matches total tensor complexes and preserves and reflects K-flat complexes, so $T\otimes^{\mathrm L}_S-$ goes to derived scalar extension along the section-ring map $S_{\mathrm{sec}}\to T_{\mathrm{sec}}$), and gives isomorphisms $D(F)R\mathcal Hom_B(K,N)\cong H_{B_{\mathrm{sec}}}(D(F)K,D(F)N)$, natural in both variables and carrying evaluation to evaluation. Hence: (a) the finite-free and colimit statements of steps 2-3 hold verbatim for the section-ring sheaves, since $F$ does not change underlying sheaves or maps; (b) termwise colimits of complexes are unchanged by $D(F)$, and naturality in $N$ carries the evaluation-induced continuity map of the hypothesis on $K$ to the evaluation-induced map $\varinjlim_iH(D(F)K,M_i^\bullet)\to H(D(F)K,\varinjlim_iM_i^\bullet)$, which is therefore an isomorphism; (c) since the evaluation-transpose comparison is defined from evaluation morphisms and the scalar adjunction, the comparison of step 6 for $D(F)K,D(F)L$ corresponds under these isomorphisms to the item's displayed map, and likewise each stage map of the three-arrow formula. The lower bound of $L$ is unchanged.

Uses: lem-sfb-module-object-ringed-site-derived-comparison, lem-pe-internal-section-tensor-comparison, sk-def-sfb-derived-tensor-hom.

Source: literature/stacks-project/sites-modules.tex; Tags 03DA/03DB (module sheaves over a ringed topos), used through the existing module-object/ringed-site comparison nodes; no SGA source.

### Returned step 6 → assembly step 4, using Task B for map normalization

After the transport of step 5, apply the general filtered finite-free internal-Hom comparison to $D(F)K$ and $D(F)L$, with its base ring $R=S=E_X$, coefficient diagram $(S_i)=(A_F)_{F\in I_E}$, and colimit algebra equal to our $T$. Step 1 verifies a small filtered index, step 2 verifies finite freeness, step 3 verifies both the algebra and underlying module colimits with their given legs, and step 4 verifies exact filtered colimits. The hypothesis on $K$ applies to every small filtered diagram, hence to this particular index; the required lower-bound hypothesis on $L$ is exactly the one assumed here. The general theorem gives the canonical evaluation-transpose isomorphism in $D(T)$ (transported back by step 5), natural in both inputs, and identifies its restriction with the three-arrow formula in the statement. Its formula uses a bounded-below representative of $L$; no bound on a representative of $R\mathcal Hom_S(K,L)$ is required. The same theorem states that the finite-stage comparisons are induced by evaluation, commute with every transition of the algebra diagram, and are independent of finite bases. They give all the remaining clauses for our field diagram. No constructibility, completeness or site-perfectness hypothesis has entered this specialization.

Uses: lem-sfb-dc-hom-filtered-colimit.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.14 and Remark 6.8.15 as motivation; apply the existing explicit-continuity general comparison, an agent formulation rather than a verbatim assertion of those results.

## Remaining work

Stage 1 only: prove/split the two new unsplit statement nodes in parallel in later assignments. Nothing is left unfinished in this extraction. The final delivery tool performs the server-side DAG, route, citation and preflight checks before pushing.

## Validation

Server deliver.py dry run at d03e63fa696 passed before the final precision edits; final dry run and push follow with the same tool. No local check_dag, review_split or preflight script was run.
