# Worker report: lem-sf-adic-qbar-constructible-realization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-adic-qbar-constructible-realization.json`: unchanged statement and statement dependencies; four assembly steps, 1880 characters.
- `dag/nodes/sec-six-functors/lem-sf-adic-finite-realization-cocone.json`: statement, unsplit; no Mathlib match; no proof or proof dependencies.
- `dag/nodes/sec-six-functors/lem-sf-adic-common-stage-descent-equivalence.json`: statement, unsplit; no Mathlib match; no proof or proof dependencies.
- `dag/nodes/sec-six-functors/lem-sf-adic-completed-tensor-realization-descent.json`: statement, unsplit; no Mathlib match; no proof or proof dependencies.
- `dag/nodes/sec-six-functors/lem-sf-adic-common-stage-hom-transpose.json`: statement, unsplit; no Mathlib match; no proof or proof dependencies.
- `dag/nodes/sec-six-functors/lem-sf-adic-ambient-hom-evaluation-comparison.json`: statement, unsplit; no Mathlib match; no proof or proof dependencies.
- `dag/nodes/sec-six-functors/lem-sf-adic-realization-isomorphism-normalization.json`: statement, unsplit; no Mathlib match; no proof or proof dependencies.

`citations.json` contains one verbatim statement quotation for each of the six new-node citations in the four assembly steps. Searches and full service results remain in `searches.jsonl` and the six `*.search-results.json` files. No Lean, compiler, Lake, git command, repository write, launcher edit, or sub-agent was used.

## Attachments

None. Searches under `lean/WeilConjectures/` for the exact blueprint tag, constructible realization, adic realization and Hom transpose found no declaration stating this item or any of the six new statements. The AdicSystem realization is a normalized-system realization, not the asserted category equivalence and normalized tensor/Hom/isomorphism comparisons. Existing sorry declarations are not attachments.

## Wanted

None. Both BS and HRS are available in the supplied literature. Their text was read in the retained `bs.txt` and `hrs.txt`; the custom comparison normalizations are explicitly agent-written, as in the returned proof. No SGA source is used.

## Fault and repair

The released stage-1 repair note and the supplied return reopen the node despite its earlier pass. The sandbox item was byte-for-byte the current live item, including its twelve-step proof. The first required dry run was run before edits and exited with the missing `report.md` / `## Review by Q53` diagnostic. The earlier search plan and extracted sources were retained, not discarded. There were no earlier search-result files or searches.jsonl to reuse; the six planned sets of searches have now run and their full results were read.

The returned proof is 11382 characters. I did not shorten it into an unproved slogan: every old step is assigned below to a distinct new statement-only obligation, and every old argument is retained verbatim in this report. The six obligations separate the finite-stage cocone, object/Hom/triangle descent, normalized tensor transport, common-stage Hom transpose, ambient Hom comparison and isomorphism normalization. No obligation states the whole parent. Each is independently usable and introduces its objects and hypotheses; the last four explicitly state which realization or transpose data they assume, so workers need not mine this report to identify their hypotheses. The parent keeps precisely its original statement and stmt_deps. No statement dispute or blueprint route change was needed.

## Unfinished work

The six new lemmas are intentionally unsplit, with proof [], proof_deps [], proof_origin null, and status unsplit. Their proofs are the next parallelizable work; this delivery repairs stage 1 of the parent, not the proofs of these children. The original reviewed/tool-use/provenance records are retained as history; the current repair is described in split_report and this report.

## Review by Q53

I read the current six-functors chapter and biduality unit; the unit has no detailed proof steps to replace. The imported-ancestor query prints None for this maintainer-created obligation. Each new node records that exact result and its supplied evaluation/biduality provenance, with the parent in via. I read BS Definition 3.4.10, Lemma 3.4.11, Definition 6.8.8, Proposition 6.8.14 and Remark 6.8.15, and HRS Proposition 5.2, Theorem 7.7 and Lemma 7.9. In particular BS 6.8.14(2), not an implicit idempotent completion, justifies the raw rational domain on the topologically noetherian schemes in this item. HRS discusses an idempotent-completed localization in general, so I kept that distinction explicit instead of silently changing the project category. HRS 7.9 uses the colimit topology, matching finite-extension-valued coefficients rather than the discrete algebraic closure.

Assembly step 1 cites finite-realization-cocone for the noetherian finite-dimensional integral-domain identification, equality of constructibility conventions, exact J, quotient scalar comparison and its identity/tower equations. I checked those assertions occur in that new statement. It then cites common-stage-descent-equivalence: its hypotheses are exactly that exact J and those normalized scalar comparisons. Its statement supplies the object and arrow formulas, the canonical Hom-colimit bijection, essential surjectivity, shifts and distinguished triangles. No full faithfulness or essential surjectivity is inferred from a definition.

Assembly step 2 cites completed-tensor-realization-descent. Its statement fixes the actual chi quotient map, the balanced tensorator and its inverse before chi, the completed associator/action/signed symmetry and their coherent reductions, and the rational/common-field descent. It supplies the unit multiplication and scalar coherence used by the step. The input J and rho are precisely those of step 1, so this is not an application to arbitrary unspecified tensor data.

Assembly step 3 cites common-stage-hom-transpose for the permitted pair, the right-evaluation formula and its bijection for every test object, including the finite rational scalar comparison for arbitrary constructible target. It then cites ambient-hom-evaluation-comparison. I checked its hypotheses: rho is exact and fully faithful/essentially surjective by step 1, its symmetric tensorator is step 2, and its assumed transpose is the preceding citation. Its conclusion is an ambient derived isomorphism, not merely a degreewise or global-Hom comparison, with the exact evaluation equation, naturality and coefficient/symmetry normalization required here.

Assembly step 4 cites realization-isomorphism-normalization. It assumes the same derived-scalar object formula, quotient tensorator and evaluation-defined Hom map already obtained. Its conclusion expressly covers arbitrary scheme isomorphisms without k-linearity, the mixed coefficient square, identity and composition, tensor and Hom. Thus it covers geometric Frobenius with descent datum, without mistaking a semilinear isomorphism for a k-morphism. Each of the six uses has a verbatim quote in citations.json; I checked the strings against the new files.

For the retained argument of each child I opened the statements of all thirty-one old proof dependencies. The finite-type noetherian and dimension statements give the domain bounds; the integral stratified-perfect statement identifies both full integral categories with identical reductions; condensed-e-realization gives an actual raw rational equivalence and the free-cohomology convention; qbar-lfp-local-triviality applies on noetherian strata. Finite-free-completed-scalar-comparison fixes the quotient map and its identity-field case, whereas flat-coefficient-calculus supplies exact scalar functors and balanced unit/pentagon equations. The internal tensor normalization identifies multiplication with the adjunction comparison. I also found the existing scalar-completion-associator node, which records normalization against the actual completed scalar associator and is available when splitting the cocone child.

The coefficient-descent citation sk-thm-sfb-qlbar-two-colimit actually has both the Hom statement with all integer shifts (use r=0) and object descent. The common pair definition supplies representatives and triangles over a common finite field. The generic derived-change-of-rings theorem supplies exactness on K-flat representatives, not a tensor-Hom conclusion. For tensor I checked constructible-tensor-completion fixes the quotient comparison, ringed-finite-free-tensor-data allows any coefficient map and preserves K-flatness, cochain-pullback-tensor-coherence includes signed symmetry and scalar composition, and normalized-tensor-constraint-transport handles re-resolved inner completed expressions. The completeness identity-field comparison is used to reflect those constraint equations from coherent reduction. Scalar-localization-monoidal handles localized arrows, not just integral arrows.

For Hom, completed-tensor-hom-transpose includes the raw rationalized bijection for constructible completed Hom; rational-hom-scalar-transpose applies to an arbitrary constructible target, not only a dualizing target. Hom-preservation gives bounded constructibility over the finite-extension-valued qbar ring. The ringed closed-symmetric-monoidal theorem supplies the ambient right-evaluation adjunction with its specified symmetry. Scalar-hom-comparison-tower explicitly asserts naturality and identity/tower equations of evaluation-defined maps without an invertibility hypothesis. Tensor coherence states the needed equations for the actual normalized scalar comparisons. The two-test inverse argument is preserved below in full.

For isomorphisms I checked proetale-isomorphism-inverse-image gives reindexing, exactness and all limits/colimits; cartesian-coefficients identifies the point-pulled rings; isomorphism-derived-pullback identifies integral derived pullback with inverse image; isomorphism-comparison-scalar-extension is an equality for the specified integral comparison; inverse-image-tensor-hom has tensor, Hom and limit formulas. Cochain composition then supplies the prescribed rather than arbitrary identity/composition maps. None of these citations is being used only for material hidden in its proof.

Small cases: T empty gives the zero category and vacuous stratifications; T a geometric point recovers finite-dimensional coefficient objects and scalar multiplication. E=F makes each scalar map the multiplication/completeness unitor; a tower with repeated fields obeys the stated unit equations. K=0, L=0 and the rank-zero coefficient module satisfy tensor and transpose statements. An integral torsion object may become zero after raw rationalization; no Karoubi object is adjoined and no integral faithfulness is asserted. Hom statements retain the permitted-pair hypothesis and require no site-perfectness. For the ambient inverse the test Q is allowed because Hom-preservation puts Q in the full target; the second test is rho H. For g=id and inverse isomorphisms the reindexing comparisons give the identity/cocycle, and Frobenius is considered only with a supplied descent datum. These checks preserve every hypothesis used by the returned proof.

All new nodes are statement-only (B1), give their own coefficient rings, schemes, categories, map formulas and hypotheses (B2/B3), have singly escaped mathematical TeX (B4), and cite BS/HRS at named propositions/lemmas (B5). No Mathlib leaf is claimed (B6/B8). They are not proof sketches inside statements: their formulas specify the assertions later workers must prove, while the actual old proofs are below. For C1/C4 each current assembly claim is literally in its cited statement; no uncited non-elementary comparison remains in the assembly. For D1/D2 the human re-split order requires smaller obligations, and these six divide the twelve old steps rather than reproducing the whole conclusion in one child. There is no new proof step over 2000 characters (the entire assembly is 1880).

## Searches and Mathlib verdicts

For each child I ran exactly the commands in search_plan.json: LeanFinder, Loogle, grep, LeanSearch and a second differently worded LeanSearch. The search command wrote the authoritative log; I did not invent entries. Every service returned OK. The records in each node contain the exact query texts and hit names/signatures from the retained output. The finite-cocone hits concern condensed free/solid objects, ordinary adic completions or limits of schemes, not equivalences of these raw constructible categories. The descent hits concern local cohomology, finite-presentation descent of ring maps, field closure equivalences or Galois fiber functors. The tensor hits concern ordinary tensor associators and localization, sheafification monoidality or adic completions of ordinary modules. The transpose hits concern ordinary ModuleCat adjunctions, direct limits or abstract Closed structures. The ambient comparison search found expComparison, whose source in Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean:81 assumes cartesian monoidal categories and product preservation; ordinary derived module tensor is not cartesian. Closed/Ideal.lean:249 is a reflective exponential-ideal construction. Neither is a one-line specialization to this native comparison. The isomorphism hits concern scheme limits/covers or reindexing ordinary tensor products. I read the potential tensor-completion and cartesian-closed sources; none states these constructible quotient-model comparisons.

DAG and blueprint discovery used blueprint_refs search for realization, transpose, common-stage, completed tensor, scalar.*realization, isomorphism.*realization, evaluation.*transpose and continuous.*coefficient, together with whole-DAG statement and source-place searches and Lean notion/tag searches. Before writing each id I checked it did not exist. I opened the plausible nodes listed below rather than identifying them solely by title. The original item searches were retained unchanged because its statement and search question are unchanged.

## Not duplicates

lem-sf-adic-finite-realization-cocone vs lem-weil-pbc-condensed-e-realization: gives individual finite-E equivalences and k-morphism comparisons; the new lemma identifies the framework integral domain and proves a simultaneous cocone for the actual completed coefficient transitions, including normalized scalar towers.
lem-sf-adic-finite-realization-cocone vs lem-weil-pbc-integral-stratified-perfect-characterization: identifies integral categories but contains neither the continuous finite-E equivalence nor its scalar cocone.
lem-sf-adic-finite-realization-cocone vs lem-weil-pbc-condensed-qbar-lfp-local-triviality: is the local presentation/free criterion for a single qbar sheaf, not the combined finite-realization diagram.
lem-sf-adic-finite-realization-cocone vs lem-weil-finite-free-completed-scalar-comparison: gives the integral completion isomorphism, not its realization as a coherent diagram of raw rational categories.
lem-sf-adic-finite-realization-cocone vs lem-fix-scalar-completion-associator: normalizes integral completion associators only; it does not identify constructibility conventions or continuous realization equivalences.
lem-sf-adic-common-stage-descent-equivalence vs sk-thm-sfb-qlbar-two-colimit: descends the continuous module-object coefficient categories; the new node constructs and checks the specific functor from the raw integral common-stage pair category, including its exact-triangle normalization.
lem-sf-adic-common-stage-descent-equivalence vs prop-weil-pbc-qbar-condensed-two-colimit: is the bare two-colimit assertion; it does not give the required normalized common-stage functor and map/triangle assembly.
lem-sf-adic-common-stage-descent-equivalence vs lem-fd-common-stage-comparison-descent: compares two literal finite-stage pair categories and assumes finite framework/PBC equivalences; this node targets the ambient continuous R_T-module subcategory and must use its coefficient object/Hom descent.
lem-sf-adic-common-stage-descent-equivalence vs lem-sf-locally-finite-adic-constructible-realization: uses the locally finite algebraic coefficient sheaf and locally defined strata, and has no tensor/Hom normalization; the new node fixes the finite-extension-valued point-pulled ring and constructs descent of a specified coherent cocone.
lem-sf-adic-completed-tensor-realization-descent vs lem-fix-constructible-tensor-completion: states invertibility of chi, not its compatibility with all actual completed constraints or its rational/common-field descent.
lem-sf-adic-completed-tensor-realization-descent vs lem-pur-normalized-tensor-constraint-transport: compares normalized-system and quotient-model constraints, not continuous realization tensorators or rational/common-field descent.
lem-sf-adic-completed-tensor-realization-descent vs lem-sf-ringed-finite-free-tensor-data: constructs ordinary derived scalar tensorators on ring-sheaf models, not the specified completed constraint identification and common-stage realization.
lem-sf-adic-completed-tensor-realization-descent vs lem-sf-scalar-localization-monoidal: is generic scalar localization only; it does not establish the integral completion constraint square or common-field independence.
lem-sf-adic-completed-tensor-realization-descent vs def-sf-rational-tensor-comparison-system: defines a record and asserts no existence; the new lemma proves normalized comparisons for a continuous coefficient realization rather than a supplied perfect-point-valued record.
lem-sf-adic-common-stage-hom-transpose vs lem-coef-completed-tensor-hom-transpose: gives the integral and single-field raw rational bijection, not its passage through the common-stage Hom colimits and actual coefficient comparisons.
lem-sf-adic-common-stage-hom-transpose vs lem-coef-rational-hom-scalar-transpose: gives compatibility for one finite extension, not the all-test-object representing bijection in the common-stage category.
lem-sf-adic-common-stage-hom-transpose vs lem-zl-specified-hom-scalar-evaluation: identifies a completed/rational Hom coefficient comparison at finite fields, not the common-stage transpose bijection.
lem-sf-adic-ambient-hom-evaluation-comparison vs lem-sf-ringed-derived-closed-symmetric-monoidal: provides the ambient adjunction, not invertibility of the native realization comparison between the specified Hom objects.
lem-sf-adic-ambient-hom-evaluation-comparison vs lem-sfb-dc-hom-preserves: gives bounded constructibility only, not the specific evaluation-transpose isomorphism and its normalization.
lem-sf-adic-ambient-hom-evaluation-comparison vs lem-pur-scalar-hom-comparison-tower: gives tower equations of ordinary scalar Hom maps without invertibility; the new lemma identifies the permitted common-stage Hom with ambient Hom via the realization equivalence.
lem-sf-adic-realization-isomorphism-normalization vs lem-weil-isomorphism-derived-pullback: identifies integral pullback with inverse image; it does not normalize the continuous realization and its tensor/Hom maps.
lem-sf-adic-realization-isomorphism-normalization vs lem-weil-isomorphism-comparison-scalar-extension: states the integral mixed scalar comparison equation, not the full realized qbar comparison with tensor, Hom and all isomorphism identity/composition maps.
lem-sf-adic-realization-isomorphism-normalization vs lem-weil-proetale-isomorphism-inverse-image: gives exact site reindexing and limits/colimits; it contains no assertion about the specified completed/rational realization comparisons.
lem-sf-adic-realization-isomorphism-normalization vs lem-pur-isomorphism-inverse-image-tensor-hom: is the sheaf-level tensor/Hom/limit formula, not the quotient-normalized derived realization and its common-stage/isomorphism coherence.

## Complete retained arguments, assigned to the new obligations

These are the old twelve steps verbatim, including every normalization argument, source and dependency. This appendix is proof material for subsequent workers, not proof steps of the unsplit new nodes. Grouping is 1--3, 4--6, 7--8, 9, 10--11, 12; no argument was omitted or compressed.

### lem-sf-adic-finite-realization-cocone

Old step 1:

First check the domains. The spectrum of the field $k$ is Noetherian (its only ideals are $0$ and $k$), and the finite-type Noetherian-base theorem makes $T$ Noetherian. The finite-type dimension theorem gives finite dimension; finite type gives quasi-compactness and separatedness gives quasi-separatedness. Also $\ell$ is a unit in every local ring, since it is already a nonzero element of $k$. Thus the integral stratified-perfect characterization applies. It identifies the integral category underlying $\mathcal C_T$ with the integral category used in the rational realization, as the same full subcategory over $B_{E,T}=\varprojlim_n(\mathcal O_E/\varpi_E^n)_T$, with the same morphisms and reductions. Their raw localizations therefore have the same objects and $\operatorname{Hom}\otimes_{\mathcal O_E}E$; there is no idempotent completion to compare.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, lem-weil-pbc-integral-stratified-perfect-characterization, def-weil-rationalization-karoubi.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.6.11 and Proposition 6.8.14(2): identify the integral category and its raw rationalization.

Old step 2:

Put $E_T=p_T^*\underline E$. The rational realization theorem gives an $E$-linear equivalence $J_{E,T}:D^b_c(T,E)\simeq D^b_{\rm cons}(E_T)$ induced by $E_T\otimes^L_{B_{E,T}}-$. Its target consists precisely of bounded complexes with stratified locally finite free cohomology, as asserted in that theorem. The cohomological locally-finitely-presented convention in the coefficient-descent theorem also agrees with this convention: for $\Omega$ apply the local-triviality theorem on each Noetherian stratum; the converse holds because a finite free module has a finite presentation. Thus the $\Omega$ target in that descent theorem is exactly the full subcategory in this item. The coefficient sheaf throughout is the finite-extension-valued $R_T$, not the constant sheaf of the discrete scalar field.

Uses: lem-weil-pbc-condensed-e-realization, lem-weil-pbc-condensed-qbar-lfp-local-triviality, sk-def-sfb-bounded-constructible, sk-def-sfb-qlbar-condensed.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Definition 6.8.8 and Proposition 6.8.14(2); HRS Theorem 7.7 and Lemma 7.9 for the condensed interpretation.

Old step 3:

For a finite extension $E\subset F$, the canonical finite-free completion comparison identifies the specified integral scalar extension of $K$ with $B_{F,T}\otimes^L_{B_{E,T}}K$. After applying $J_{F,T}$ it becomes $F_T\otimes^L_{B_{E,T}}K$. On the other hand $F_T\otimes^L_{E_T}J_{E,T}K$ is canonically the same object by balanced tensor multiplication. These identifications commute with all maps: the completion comparison is natural, and on a rational arrow $u\otimes a$ both paths give the image of $u$ multiplied by the image of $a\in E$. In a tower $E\subset F\subset G$, both scalar-composition routes send $g\otimes(f\otimes(e\otimes x))$ to $gfe\otimes x$. The identity extension acts by $1\otimes x\mapsto x$. The derived tensor comparisons have these same formulas on K-flat representatives, so their pentagon and unit equations are the scalar-associativity equations. Consequently the $J_{E,T}$ intertwine the actual rational transition functors, not a newly chosen system.

Uses: lem-weil-finite-free-completed-scalar-comparison, lem-weil-pbc-condensed-flat-coefficient-calculus, lem-sfb-internal-tensor-composition-unit-normalization, lem-pur-derived-change-of-rings, def-weil-rationalization-karoubi.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.14; finite-extension compatibility of its scalar-localization realization.

### lem-sf-adic-common-stage-descent-equivalence

Old step 4:

Define $\rho_T(E,K)=R_T\otimes^L_{E_T}J_{E,T}K$. For an arrow represented by $u$ at a common finite extension $F$, apply $J_{F,T}$ to $u$, extend to $R_T$, and conjugate by the scalar comparisons of the preceding step. Their unit and tower equations show that enlarging $F$ gives the same arrow. If two representatives agree after further extension, their images therefore agree. Composition and identities can be computed at one common stage and are preserved by the finite-stage functors. This defines the stated canonical functor, with precisely the object and arrow formulas in the item.

Uses: def-weil-algebraically-closed-coefficients, lem-weil-pbc-condensed-flat-coefficient-calculus.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.14; HRS Lemma 7.9: the scalar-extension cocone.

Old step 5:

Let $(E,K),(E',L)$ be two objects and first pass to the compositum $F_0$ of their fields. At every finite $F\supset F_0$, full faithfulness of $J_{F,T}$ identifies the common-stage Hom group with the Hom group between the corresponding continuous $F$-coefficient realizations. Step 3 identifies all transition maps in these Hom groups. Assertion (2) of the coefficient-descent theorem, with shift $r=0$, identifies their colimit with the ambient Hom group between the two $R_T$-realizations. This is exactly the map on Hom groups constructed in step 4. It is bijective, so $\rho_T$ is fully faithful. For any target object $P$, assertion (3) gives a finite $E$ and $Q\in D^b_{\rm cons}(E_T)$ with $R_T\otimes^L_{E_T}Q\cong P$. Essential surjectivity of $J_{E,T}$ gives $K$ with $J_{E,T}K\cong Q$, hence $\rho_T(E,K)\cong P$.

Uses: lem-weil-pbc-condensed-e-realization, sk-thm-sfb-qlbar-two-colimit, def-weil-algebraically-closed-coefficients.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.14; HRS Proposition 5.2 and Lemma 7.9: full faithfulness and essential surjectivity.

Old step 6:

The finite-stage realizations are derived changes of rings, hence exact triangulated functors, and $E_T\to R_T$ is flat with exact derived scalar extension. A distinguished triangle in the common-stage category is isomorphic to the image of a distinguished triangle at one finite stage. Its image under $\rho_T$ is therefore distinguished. The same K-flat constructions give its shift comparison. Together with step 5 this proves that $\rho_T$ is an exact equivalence of the displayed triangulated categories.

Uses: lem-pur-derived-change-of-rings, lem-weil-pbc-condensed-flat-coefficient-calculus, def-weil-algebraically-closed-coefficients.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.14: equivalence of triangulated categories.

### lem-sf-adic-completed-tensor-realization-descent

Old step 7:

To compare the specified tensor, first work integrally. For constructible $K,L$, the ordinary-to-completed tensor comparison $\chi_{K,L}$ is invertible. The strong tensorator $J_{E,T}K\otimes^L_{E_T}J_{E,T}L\to J_{E,T}(K\widehat\otimes^L L)$ is the ordinary derived scalar tensorator followed by $J_{E,T}(\chi_{K,L})$. The latter is the balanced map $(a\otimes x)\otimes(b\otimes y)\mapsto ab\otimes(x\otimes y)$, with inverse $a\otimes(x\otimes y)\mapsto(a\otimes x)\otimes(1\otimes y)$. The generic ring-sheaf scalar-tensor theorem supplies preservation of K-flat complexes and the normalized derived tensorator, for any coefficient map. Its associativity, unit and symmetry equations follow from the K-flat cochain tensor comparison. These are also the constraints of the specified completed tensor. Apply the normalized constraint-transport theorem to the coherent reductions $(K\otimes^L B_{E,T,n})_n$, which are normalized (their transition adjoints are the tensor associativity isomorphisms), so its primitive comparisons and their counit composites are invertible: the canonical completed reassociation, unitors and signed symmetry are the derived limits of the levelwise total-complex maps $(x\otimes y)\otimes z\mapsto x\otimes(y\otimes z)$, $b\otimes x\mapsto bx$, $x\otimes y\mapsto(-1)^{pq}y\otimes x$, and their coherent reductions are these levelwise maps. The level-$n$ component of $\chi$ is the quotient map of total complexes, so after coherent reduction both routes of each constraint square through $\chi$ are the same levelwise map. By the case $L=E$ of the finite-free completion comparison, every derived-complete object is the derived limit of its coherent reduction, so coherent reduction is faithful on these objects and the squares commute before reduction. This verifies coherence for this particular $\chi$, rather than choosing new completed constraints.

Uses: lem-fix-constructible-tensor-completion, lem-sf-ringed-finite-free-tensor-data, lem-pur-cochain-pullback-tensor-coherence, lem-pur-derived-change-of-rings, def-weil-derived-pullback-tensor-hom, lem-pur-normalized-tensor-constraint-transport, lem-weil-finite-free-completed-scalar-comparison.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Definition 3.4.10; Remark 6.8.15: tensor under the rational realization.

Old step 8:

Rationalize the preceding tensor comparisons. A pure rational arrow in each input has coefficients $a,b$, and both tensor routes multiply them to $ab$, so the integral naturality and coherence equations remain true for arbitrary sums of pure rational arrows. For objects represented at different fields, extend them to their compositum and apply this comparison there, then extend to $R_T$. Step 3 and the cochain coefficient/tensor square make this independent of the common field: both scalar routes have the same product of scalar factors and the same Koszul sign. The descended tensorator therefore compares exactly the common-stage tensor of the item with ordinary derived tensor over $R_T$. The unit, represented by $\mathcal O_E$, maps to $R_T\otimes_{E_T}E_T\cong R_T$ by multiplication. Associativity, unit and signed symmetry equations can all be checked at one common finite stage as in step 4. This gives the symmetric strong monoidal equivalence asserted.

Uses: def-weil-derived-pullback-tensor-hom, lem-sf-scalar-localization-monoidal, lem-pur-cochain-pullback-tensor-coherence, lem-weil-pbc-condensed-flat-coefficient-calculus.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Remark 6.8.15; HRS Lemma 7.9: descent of the specified tensor and its constraints.

### lem-sf-adic-common-stage-hom-transpose

Old step 9:

Fix a permitted pair $M,N$ and its coefficient-passage $H$. At a common finite field, the rational completed tensor-Hom transpose theorem identifies $\operatorname{Hom}(L,H)$ with $\operatorname{Hom}(M\otimes L,N)$; using the signed symmetry, this is $\operatorname{Hom}(L\otimes M,N)$. The finite scalar-transpose theorem says exactly that extending a pairing and then transposing agrees with extending its transpose followed by the specified Hom comparison, for any constructible target. Therefore these bijections commute with every transition in the common-stage Hom groups. Taking their directed colimit yields, for every $L\in\mathcal C_T$, the natural bijection
$$\operatorname{Hom}_{\mathcal C_T}(L,H)\cong\operatorname{Hom}_{\mathcal C_T}(L\otimes M,N),\quad a\mapsto\operatorname{ev}\circ(a\otimes1_M).$$
Only a finite stage witnessing the permitted Hom pair is used; no assertion that $M$ is site-perfect is needed.

Uses: lem-coef-completed-tensor-hom-transpose, lem-coef-rational-hom-scalar-transpose, def-weil-derived-pullback-tensor-hom, def-weil-algebraically-closed-coefficients.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Lemma 3.4.11, rationalized and passed to common finite stages.

### lem-sf-adic-ambient-hom-evaluation-comparison

Old step 10:

Put $Q=R\mathcal Hom_{R_T}(\rho_TM,\rho_TN)$ in the ambient derived category. It is bounded constructible by the condensed Hom-preservation theorem, so it belongs to the full target category (use step 2 for its local-free convention). Let $c:\rho_TH\to Q$ be the transpose of $\rho_T(\operatorname{ev})$ under the tensorator of step 8. For a test object $\rho_TL$, full faithfulness, step 9, the tensorator and ambient tensor-Hom adjunction give a bijection
$$\operatorname{Hom}(\rho_TL,\rho_TH)\cong\operatorname{Hom}(\rho_TL\otimes\rho_TM,\rho_TN)\cong\operatorname{Hom}(\rho_TL,Q).$$
By their evaluation formulas this bijection is postcomposition with $c$. Essential surjectivity makes it a bijection for every target test object. In particular, testing at $Q$ gives $d:Q\to\rho_TH$ with $cd=1_Q$; injectivity at $\rho_TH$ then gives $dc=1_{\rho_TH}$, since $c(dc)=c$. Thus the specified $c$ is invertible in the full target and therefore in the ambient derived category. Its defining transpose equation is exactly preservation of module evaluation.

Uses: lem-sfb-dc-hom-preserves, lem-sf-ringed-derived-closed-symmetric-monoidal, sk-def-sfb-bounded-constructible.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Lemma 3.4.11 and Remark 6.8.15: evaluation-normalized identification with ambient internal Hom.

Old step 11:

Naturality of $c$ in both variables follows by transposing the naturality equation for evaluation; the ambient tensor-Hom bijection is injective, so equality of these transposes is equality of the original maps. In a coefficient tower the two candidates likewise have the same transpose: balanced multiplication identifies their tensorators, and the scalar Hom comparison is defined by scalar extension of evaluation. The scalar Hom tower theorem supplies exactly this identity and its identity-ring case. Together with the finite rational transpose theorem, this proves finite coefficient-extension compatibility for the actual $c$. Symmetry compatibility follows by the same argument using the signed swap already verified in step 8.

Uses: lem-pur-scalar-hom-comparison-tower, lem-sfb-scalar-hom-tensor-coherence, lem-coef-rational-hom-scalar-transpose, lem-sf-ringed-derived-closed-symmetric-monoidal.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Remark 6.8.15: naturality and coefficient coherence of the evaluation comparisons.

### lem-sf-adic-realization-isomorphism-normalization

Old step 12:

Finally let $g:T\xrightarrow{\sim}U$ be any scheme isomorphism between schemes in question; it need not be a $k$-morphism. Its inverse image is the exact equivalence obtained by reindexing $(V\to T)$ as $(V\to U)$, and commutes with all limits and colimits. Coefficients pulled back from the point are identified by the canonical ring isomorphisms. The integral derived pullback agrees with this inverse image, and its finite scalar comparison commutes with that identification. Hence $g^{-1}$ carries the quotient maps defining completion, the K-flat tensor formulas, and balanced scalar multiplication to the same formulas over $T$. The resulting comparison $\rho_Tg^*\cong g^*\rho_U$ respects the tensorator and unit; the Hom comparison respects it because their evaluation transposes agree. For identity and composite isomorphisms, reindexing is identity and composite reindexing, respectively, and the cochain pullback/tensor composition equation identifies the scalar maps. Thus these are the specified identity and composition comparisons. In particular this applies to the geometric Frobenius isomorphism whenever the scheme is supplied with the relevant finite-field descent datum; no $k$-linearity of that isomorphism is being assumed.

Uses: lem-weil-proetale-isomorphism-inverse-image, sk-prop-sfb-cartesian-coefficients, lem-weil-isomorphism-derived-pullback, lem-weil-isomorphism-comparison-scalar-extension, lem-pur-isomorphism-inverse-image-tensor-hom, lem-pur-cochain-pullback-tensor-coherence.
Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Remark 6.8.15: functoriality under scheme isomorphisms, including semilinear Frobenius.
