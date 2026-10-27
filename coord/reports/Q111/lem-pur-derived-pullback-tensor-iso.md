# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-derived-pullback-tensor-iso.json`: existing statement, unchanged; re-split into a short six-step assembly.
- `dag/nodes/sec-smooth-purity/lem-pur-finite-derived-comparison-normalization.json`: statement, unsplit; no Mathlib match. Independent argument: localization and representative normalization of the finite coefficient comparison, including its derived coefficient square.
- `dag/nodes/sec-smooth-purity/lem-pur-completed-comparison-quotient-realization.json`: statement, unsplit; no Mathlib match. Independent argument: simultaneous normalized quotient expressions and actual limit comparisons, with reductions, structural diagrams and the completed scalar square.
- `dag/nodes/sec-smooth-purity/lem-pur-bilinear-comparison-coefficient-descent.json`: statement, unsplit; no Mathlib match. Independent argument: arbitrary separately linear bifunctor comparisons under scalar localization and common-field Hom colimits.
- `citations.json`: one exact quotation for each citation of each assembly step. `searches.jsonl` and `search-results/` retain all actual queries and complete responses.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag and tensor/pullback names. The canonical finite derived counit identities in `SixFunctors/ProEtale/FiniteCoefficient/Derived/TensorSheaf.lean` and scalar compatibility in `Derived/ScalarExtension.lean` are components, not the four-stage statement. `lean/Sheaf/Paper/DerivedPullbackTensorIso.lean:1276` states the item, but its proof ends in `sorry` at line 1372 and several higher-coherence declarations in that module remain sorry. No attachment is claimed.

## WANTED

None. Sources used are present in the repository; the elaborations beyond their displayed definitions are explicitly agent arguments, not attributed to a source as unproved quotations.

## Returned issue and repair

The 2026-10-22 return requires spreading the 7,525-character proof across at least two comparable statement-only tasks, while retaining the statement and every argument and reducing the assembly to at most 3,000 characters. The sandbox initially contained only dispatcher marker files, so I copied the current live node, which still has the returned twelve-step proof and the same Sheaf.Paper.DerivedPullbackTensorIso module. There was no retained report or search log to overwrite. The complete returned proof is preserved below, including its source places and every dependency. The new tasks partition its substantive arguments as follows:

| Original steps | New task | Argument retained |
|---|---|---|
| 1-3 | lem-pur-finite-derived-comparison-normalization | Ordinary ringed-topos comparison, K-flat tensor closure, localization on the resolving class, signed constraints, composition, and coefficient-change equations. The constant-ring identification remains explicit in assembly step 1. |
| 4-10 | lem-pur-completed-comparison-quotient-realization | The actual P_n,Q_n,T_n,U_n,V_n,W_n models, normalization, strict map and inverse, functorial derived limit, representative independence, coherent counit reduction, completed structural diagrams and ramified scalar square. The elementary restriction to the full constructible subcategory remains explicit in assembly step 3. |
| 11-12 | lem-pur-bilinear-comparison-coefficient-descent | Hom tensor E with separately linear morphism formulas, localized inverse and equations, common-field conjugation, independence of common fields and arrow representatives, and finite-diagram descent. |

There are three new tasks of substantive size, not a single renamed version of the item. They carry no proof, proof dependencies, proof origin, Lean implementation or hidden proof sketch in their statements. They expose the representative, system-map and Hom-colimit conclusions that independent workers must establish. No target or parent statement has changed. No SGA source or purity/trace theorem is used.

## Review by Q111

I read the item against Stacks `sites-cohomology.tex`, Tag 07A4 (`lemma-pullback-tensor-product`, statement and K-flat proof), Tag 0G7E (`lemma-pullback-K-flat`), the current main-20261015 derived-operation, rationalization and common-stage definitions, the live detailed definition nodes, the original chapter and conventions-unit records, and ancestor `def-weil-frobenius-coefficient-twists` clause 5. This is the comparison used before theta_K tensor theta_m, not a new route to smooth purity. I preserved the parent's coefficient categories, arbitrary scheme morphism, and finite ambient unbounded domain. In particular I did not incorrectly assert boundedness of tensor products over a finite quotient DVR.

For the finite new node, 07A4 supplies the ambient unbounded comparison and its actual K-flat representative, not all coefficient coherence for free. The new task explicitly includes localization of the cochain coefficient square, with typed functors F'E_R and E_SF and the orientation of kappa specified. The chain comparison and inverse have the same pure-tensor formulas as the existing cochain node. The sign is (-1)^(pq); scalars have degree zero. The existing ringed monoidal lemma supplies structural coherence but does not state this derived coefficient square. Resolution existence and tensor closure are already separate cited results in the retained proof; these have not been silently reproved by definitions. New statement dependencies name the actual module, complex, K-flat and ringed-topos notions.

For the completed new node, I read `def-pur-integral-derived-operations` and `def-pur-completed-pullback-tensor-comparison` together with the complete statements of `lem-pur-completed-operation-tower-substitution`, `lem-pur-integral-tower-limit-comparison`, `lem-pur-integral-coherence-tower`, `lem-pur-coefficient-extension-reduction-model`, `lem-pur-scalar-extension-tower-coherence`, K-flat change of rings and well-definedness. The new task is simultaneous representative realization: it supplies the actual quotient models for nested completed expressions and identifies their structural and scalar maps before and after limit. The old limit lemma instead assumes its normalized towers and strict c are already supplied; the old coherence lemma assumes the chosen quotient complexes; the scalar lemma is a strict-system square. None alone states this combined representative-normalized conclusion. I wrote beta_s and beta_t and conjugated L(c) explicitly as gamma_E, so the reduction equation is an equation with the actual completed source and target. The completed sheaf R_W is an inverse limit of finite constant sheaves, not the discrete constant O_E. All towers keep their actual transitions, and no claim that separate level evaluations are faithful occurs. The scalar models are derived via K-flat representatives, even when A_E,n to A_L,n is not flat.

For the descent new node, I read the main-20261015 raw rationalization and algebraically closed definitions and the existing linear category and raw scalar localization statements. The new task assumes coefficient unit/tower cocycles and the eta/lambda square, and asserts their bilinear and finite-diagram descent. It treats arbitrary linear categories and separately linear bifunctors, not only functors to Perf or unary exact functors between scheme categories. No Karoubi completion is smuggled into the statement. Its displayed conjugate has source S^D(U_K) and target S^D(V_K); at L=K it reduces to eta_K after the specified unit identifications. A different initial field is compared only at a further common extension. This is a real construction and representative-independence task, not the assertion that a comparison exists for our particular f.

Assembly citation check, step by step:

1. `prop-weil-pbc-proetale-constant-exact` explicitly gives the transported finite constant action, identifies it with module inverse image for commutative coefficients, and proves exactness. The finite new node explicitly gives the canonical derived comparison on arbitrary unbounded inputs and every structural/coefficient equation. `def-weil-derived-pullback-tensor-hom` identifies those operations with the project's finite operations. All its finite hypotheses hold for A_E,n and the given f.
2. `lem-pc-kflat-resolution` supplies flat-term K-flat representatives in the ambient module category. The completed new node supplies the strict c and inverse, the actual completed substitution, and naturality/independence for all derived arrows. These are exactly the facts assembly step 2 takes from its statements, not from their proofs.
3. `lem-pur-integral-operations-preserve-constructible` states preservation by both completed tensor and pullback. `def-weil-derived-complete-integral-detailed` explicitly defines the integral category as a full subcategory. Restricting the map and inverse once the vertices lie there is the elementary argument retained here, not a new node. This step does not conclude constructibility merely from effectivity.
4. The completed new node states the whole-system counit equation, identification of the structural diagrams, the completed scalar square and identity/successive-extension compatibility. These are exactly the assertions used for integral coherence and reduction. Its source and target functors are the prescribed ones, so no unrelated isomorphism is substituted.
5. The descent new node applies to separately linear bifunctors U_E and V_E; the project's morphism action in `def-weil-derived-pullback-tensor-hom` is explicitly linear separately. The completed realization supplies the mixed scalar square from step 4 and the canonical coefficient comparisons. Rationalization therefore has the specified components mu tensor 1 and localized inverse, with all equations. No assertion about tensoring jointly linear product Hom modules is made.
6. The same descent statement gives the conjugated representative at every common finite field, field and arrow independence, inverse, and preservation of finite equations. Thus every coherence diagram is represented at one finite field and descends. Only those explicit conclusions, not any theorem about general two-colimits, are used.

Small-case checks: for finite coefficients take u=id and R'=R, or R to R/(t); the formulas reduce to multiplication/insertion of 1 and do not require quotient flatness. For a point and A=Z/ell^2, modules killed by ell may have unbounded derived tensors; the finite task stays in the ambient derived category. For the completed task take f=id, a zero input, the coefficient unit, m=n, or E=L: the strict inverse, reduction square and scalar square become the corresponding identities. For a ramified extension of index e, varpi_E^n maps to a multiple of varpi_L^(en), hence there is the stated map to the n-th L quotient; no flatness is inferred. For descent, zero Hom modules and torsion Hom modules need no cancellation, and every scalar identity is an image under tensoring. For equal input fields the common-stage formula at that field is eta; for two unequal fields the conjugate is compared at a containing compositum, with inverse conjugated in the reverse order. The associativity clause concerns finite three-input diagrams using separately linear building blocks, covered by the stated preservation of whiskering in each variable.

I checked delivery-errors B-E against the node files: all objects and hypotheses are introduced, all new nodes are statement-only, and definitions they use are named in stmt_deps. Existing chain, limit, substitution, scalar, unary localization and Perf-target descent nodes were opened, not replaced with duplicate aliases. There are no new definitions or per-degree stand-ins for derived isomorphisms. All searches were executed with msearch.py, their complete responses retained, and each new task has LeanFinder (twice), Loogle, LeanSearch and source grep records. I read the nearby Mathlib declarations: ordinary `distribBaseChange` (Tower.lean:441), abelian Tor (Tor.lean:44), finite-module adic completion (AsTensorProduct.lean:328), unary localization linearity and NatTrans evaluation. Their hypotheses and conclusions do not give any new task in one line. There are no non-elementary assembly steps over 2,000 characters. The duplicate gate named ten additional same-tag candidates; I opened all ten and also the ringed-square tensor and exchange statements before adding the distinctions below. The only mathematical correction during self-review was making the completed reduction equation explicitly conjugated, rather than suppressing the substitution maps; the parent statement remains byte-for-byte unchanged.

## Not duplicates

- lem-pur-finite-derived-comparison-normalization vs lem-pur-derived-pullback-tensor-iso: the item concerns four coefficient stages on pro-etale schemes; this task concerns arbitrary small ringed topoi, exact K-flat representative normalization and the derived coefficient-square identity, with no completion, rationalization or common-stage descent.
- lem-pur-finite-derived-comparison-normalization vs lem-pe-constructible-comparison-tensor-test-reflection: the existing statement reflects vanishing of ordinary tensor homology along etale/pro-etale comparison, not a derived tensor pullback coefficient square.
- lem-pur-finite-derived-comparison-normalization vs def-sf-point-fibre-tensor-common-stage: the existing node defines point-fibre common-stage canonicality; it does not prove arbitrary ringed-topos derived comparison normalization.
- lem-pur-finite-derived-comparison-normalization vs lem-weil-pbc-ringed-slice-normalized-comparisons: the existing statement supplies slice tensor/Hom model comparisons for one restriction, not the derived coefficient-change square for an arbitrary ringed-topos morphism.
- lem-pur-finite-derived-comparison-normalization vs def-sf-finite-open-tensor-operations: the existing node defines fixed finite-scalar open operations and tensorPullIso; it does not establish varying-coefficient coherence on arbitrary ringed topoi.
- lem-pur-finite-derived-comparison-normalization vs lem-derived-right-exact-tensor-comparison: the existing statement provides one natural tensorator with a resolving counit equation; it has no derived coefficient-square equation or coefficient/pullback compositors.
- lem-pur-finite-derived-comparison-normalization vs def-coef-semilinear-derived-calculus: the existing node defines a strict-system calculus interface; this task proves derived comparison normalization and equations on a given ringed-topos morphism.
- lem-pur-finite-derived-comparison-normalization vs lem-sf-point-integral-completed-tensor-comparisons: the existing statement constructs completed point-fibre tensor data, not the ambient arbitrary ringed-topos comparison with derived coefficient change.
- lem-pur-finite-derived-comparison-normalization vs lem-sf-completed-tensor-rational-naturality: the existing statement derives rational naturality from an equivalence commuting with a reflector; this finite task uses arbitrary ringed-topos pullback and has no rationalization.
- lem-pur-finite-derived-comparison-normalization vs def-coef-semilinear-geometry-derived: the existing node defines a system geometry interface; this task proves normalization and coefficient equations of the ambient unbounded comparison.
- lem-pur-finite-derived-comparison-normalization vs lem-sf-ringed-finite-free-tensor-complex: the existing statement is an ordinary scalar-extension chain isomorphism and explicitly asserts no derived comparison; this task is in the derived category and includes the coefficient square.
- lem-pur-finite-derived-comparison-normalization vs def-sf-point-fibre-tensor-rational-compatibility: the existing node defines rational point-fibre normalization, not an arbitrary unbounded ringed-topos derived coefficient comparison.
- lem-pur-finite-derived-comparison-normalization vs lem-pur-cochain-pullback-tensor-coherence: that node gives chain equations before localization; the new task includes resolving-class localization, identification with canonical derived maps and the derived coefficient square on arbitrary inputs.
- lem-pur-finite-derived-comparison-normalization vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: that node gives a bifunctorial derived isomorphism, not its simultaneous coefficient-square and structural normalization equations.
- lem-pur-finite-derived-comparison-normalization vs lem-sfb-ringed-derived-monoidal-comparisons: that node supplies monoidal and compositional/adjunction coherence but no varying-ring derived coefficient square.
- lem-pur-finite-derived-comparison-normalization vs lem-pur-constant-native-pullback-monoidal: that node concerns native constant coefficients and a single monoidal edge; this task includes general structural ring maps and derived coefficient changes.
- lem-pur-completed-comparison-quotient-realization vs lem-pur-integral-tower-limit-comparison: that node assumes a normalized strict quadruple (T,U,V,c); this task supplies the simultaneous actual completed-expression representatives and their scalar/structural diagram identifications.
- lem-pur-completed-comparison-quotient-realization vs lem-pur-integral-coherence-tower: that node addresses structural equations on given quotient complexes; this task additionally identifies their actual completed comparison and coherent counits and scalar square through simultaneous representative realization.
- lem-pur-completed-comparison-quotient-realization vs lem-pur-scalar-extension-tower-coherence: that node states a strict quotient scalar square; this task identifies it with the actual completed comparison square, together with nested-operation and counit realization.
- lem-pur-completed-comparison-quotient-realization vs lem-pur-completed-operation-tower-substitution: that node identifies objects and specified structural arrows of completed expressions; this task specifies the particular c, its localized inverse and whole-system reduction, and identifies its scalar-extension square.
- lem-pur-completed-comparison-quotient-realization vs lem-pur-normalized-scalar-comparison-realization: that node realizes alpha_F and alpha_T; this task realizes the tensor/pullback c and the square between c and those alpha maps, on the same simultaneous quotient representatives.
- lem-pur-completed-comparison-quotient-realization vs lem-pur-derived-pullback-tensor-iso: the new task has representatives, strict systems, actual maps, counit and scalar-square normalization as its objects; it does not state the rational or common-field conclusion, nor independently assert constructible closure.
- lem-pur-bilinear-comparison-coefficient-descent vs lem-pur-semilinear-scalar-localization: that node extends unary functors and their transformations through scalar localization; this task handles separately linear two-variable morphisms and arbitrary common-field pair categories with specified conjugation and field independence.
- lem-pur-bilinear-comparison-coefficient-descent vs lem-sf-completed-tensor-rational-naturality: that node assumes an equivalence compatible with one reflector and addresses its particular rational tensor comparison; this task treats arbitrary pairs of bilinear functors and a coefficient-indexed family of common-stage transformations.
- lem-pur-bilinear-comparison-coefficient-descent vs lem-sf-tensor-comparison-localization-descent: that node has target Perf(O_E) and its point-field colimit, with a monoidal realization functor; this task permits arbitrary output linear categories and arbitrary bilinear functors, as required for pullbacks between scheme categories.
- lem-pur-bilinear-comparison-coefficient-descent vs lem-sf-framework-common-stage-descent: that node is for unary exact functors between scheme coefficient categories; a tensor bifunctor is separately linear and is not an additive exact functor on the product category with its product Hom modules.
- lem-pur-bilinear-comparison-coefficient-descent vs lem-fd-common-stage-comparison-descent: that node descends specific framework/PBC equivalences and unary isomorphism pullbacks on noetherian finite-dimensional schemes; no such equivalence or dimension hypothesis occurs in this bilinear task.

- lem-pur-finite-derived-comparison-normalization vs def-pd-section-derived-realization: defines section-equivalence tensor/pullback normalization for condensed coefficients, not the arbitrary varying-ring coefficient-square theorem.
- lem-pur-finite-derived-comparison-normalization vs def-pd-section-derived-tensor-data: defines conjugate tensor and localization factors under a section equivalence; it does not assert the derived coefficient-change equation.
- lem-pur-finite-derived-comparison-normalization vs lem-pd-module-ringed-topos-derived-comparison: compares internal condensed modules with ringed section-module operations on finite-type schemes; it does not address arbitrary structural ring maps and their coefficient square.
- lem-pur-finite-derived-comparison-normalization vs lem-pd-section-derived-tensor-normalization: identifies internal oplax arrows under a fixed section equivalence; this task instead establishes simultaneous derived coefficient-change and compositor equations for arbitrary ringed topoi.
- lem-pur-finite-derived-comparison-normalization vs def-weil-pbc-normalized-origin-scalar-comparisons: defines quotient scalar identity and associator maps from adjunctions, and asserts no tensor/pullback comparison coherence.
- lem-pur-finite-derived-comparison-normalization vs def-weil-pbc-ringed-projection-restriction-data: defines projection/restriction model data; it is not a theorem about the derived tensor coefficient square.
- lem-pur-finite-derived-comparison-normalization vs def-weil-pbc-ringed-tensor-square-presentation: defines a compatible ordinary ringed square and explicitly includes no derived-square tensor coherence as data; this task states such derived coefficient coherence.
- lem-pur-finite-derived-comparison-normalization vs lem-weil-pbc-augmented-cech-tensor-pullback: concerns augmentation-compatible tensor actions by chosen Cech complexes and locally finitely generated ideals, not the two-variable varying-coefficient comparison.
- lem-pur-finite-derived-comparison-normalization vs lem-weil-pbc-augmented-diagram-projection-mate: concerns a pushforward/reduction projection mate and its coaugmentation equation in strict towers, not the pullback/tensor coefficient square.
- lem-pur-finite-derived-comparison-normalization vs lem-weil-pbc-cochain-pullback-tensor-shift: states signed cochain shift compatibility; it does not give localization to arbitrary derived inputs or varying-coefficient squares.
- lem-pur-finite-derived-comparison-normalization vs lem-weil-pbc-ringed-square-tensor-compatibility: assumes a representative-normalized theta and proves its tensor equation only on two K-flat representative inputs; the new task constructs and normalizes the coefficient comparison and descends all equations to arbitrary derived inputs.
- lem-pur-finite-derived-comparison-normalization vs lem-weil-pbc-ringed-exchange-tensor-coherence: states a projection/exchange mate identity, not the derived coefficient-change tensor comparison and its full representative normalization.

The whole-DAG searches included tags 07A4 and 0G7E and tensor/pullback/coefficient, normalized quotient, rational natural transformation, scalar localization and common-stage comparison concepts. Whole-blueprint searches used those tags and the same concepts with `tools/blueprint_refs.py search`; no blueprint statement is the same as a new task. The ancestor command returns def-weil-frobenius-coefficient-twists; every new node records the item as its via entry and clause 5 as its place. I kept existing more specialized components as references in the retained work instead of creating replacements.

## Preserved original twelve arguments and worker handoff

These paragraphs are copied verbatim from the returned live proof. They are argument handoffs in the report, not proof steps hidden in the statement-only nodes. Every original cited fact remains visible here, with its actual source. A future worker splitting a new task can reconstruct exactly what work was moved, and can use the existing supporting nodes rather than duplicate them.

### Original step 1 -> lem-pur-finite-derived-comparison-normalization

At finite level choose compatible small representatives of the pro-etale sites as in [def-weil-proetale-inverse-image]. The inverse image and its constant-ring map make $f_n$ a morphism of ringed topoi. By [prop-weil-pbc-proetale-constant-exact], module pullback is exact and agrees with inverse image with the coefficient action transported through $f^{-1}(A_{E,n})_Y\cong(A_{E,n})_X$. Thus its derived functor is precisely the finite operation in [def-weil-derived-pullback-tensor-hom]. Apply [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] with $R=(A_{E,n})_Y$ and $S=(A_{E,n})_X$. Its displayed isomorphism, natural in both arguments, is $\mu_{f;M,N}$. That theorem is unbounded, so it applies to all the finite-level inputs claimed here; no finite Tor dimension of $A_{E,n}$ is assumed.

Dependencies: def-weil-proetale-inverse-image, prop-weil-pbc-proetale-constant-exact, def-weil-derived-pullback-tensor-hom, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

Source: literature/stacks-project/sites-cohomology.tex; Tag 07A4 (lemma-pullback-tensor-product), applied to the small pro-etale ringed topoi.

### Original step 2 -> lem-pur-finite-derived-comparison-normalization

Choose flat-term K-flat resolutions $P,Q$ by [lem-pc-kflat-resolution]. The closure assertion [lem-pur-kflat-total-tensor-model] shows that $\operatorname{Tot}(P\otimes Q)$ is K-flat with flat terms, so all iterated tensors below compute derived tensors. On these models the comparison is totalized from the module map of [lem-weil-pbc-ringed-topoi-module-pullback-tensor], with the signed differential from [def-pc-tensor-complex-sheaves].

Dependencies: lem-pc-kflat-resolution, def-pc-tensor-complex-sheaves, lem-pur-kflat-total-tensor-model, lem-weil-pbc-ringed-topoi-module-pullback-tensor.

Source: literature/stacks-project/sites-cohomology.tex; Tag 07A4, proof; direct K-flatness argument.

### Original step 3 -> lem-pur-finite-derived-comparison-normalization

Use the chain maps of [lem-pur-cochain-pullback-tensor-coherence]. Their pure-tensor formula and inverse are the ordinary comparison of [lem-weil-pbc-ringed-topoi-module-pullback-tensor], and the chain lemma supplies associativity, signed symmetry, units, composition and coefficient-change equations. By [lem-weil-pbc-site-derived-tensor-descent] these maps and equations descend from the K-flat resolving class to arbitrary finite-level derived inputs.

Dependencies: lem-pur-cochain-pullback-tensor-coherence, lem-weil-pbc-ringed-topoi-module-pullback-tensor, lem-weil-pbc-site-derived-tensor-descent.

Source: literature/stacks-project/sites-cohomology.tex; Tag 07A4, total-complex construction and resolving-class descent.

### Original step 4 -> lem-pur-completed-comparison-quotient-realization

For integral $M,N$, choose flat-term K-flat representatives $P,Q$ by [lem-pc-kflat-resolution]. Set $P_n=P\otimes_{R_Y}B_{Y,n}$ and $Q_n=Q\otimes_{R_Y}B_{Y,n}$, with actual quotient transitions. Put $T_n=\operatorname{Tot}(P_n\otimes Q_n)$, $U_n=f_n^*P_n$, $V_n=f_n^*Q_n$, and $W_n=\operatorname{Tot}(U_n\otimes V_n)$. The quotient and pullback models are flat-term K-flat by [lem-pur-kflat-change-of-rings, lem-weil-pbc-ringed-pullback-preserves-kflat], and the tensor totals by step 2. The normalization and coherent reduction assertions of [lem-pur-completed-operation-tower-substitution] and [lem-coef-normalized-dvr-effectivity] identify these systems with the reductions of the completed operations in [def-pur-integral-derived-operations]. Here $B_{Y,n}=(A_{E,n})_Y$ and $R_Y=\varprojlim B_{Y,n}$, as in the normalized tower convention [def-coef-normalized-dvr-tower].

Dependencies: lem-pur-kflat-change-of-rings, def-pur-integral-derived-operations, lem-weil-pbc-ringed-pullback-preserves-kflat, def-coef-normalized-dvr-tower, lem-coef-normalized-dvr-effectivity, lem-pur-completed-operation-tower-substitution, lem-pc-kflat-resolution.

Source: literature/stacks-project/sites-cohomology.tex; Tags 06YS (lemma-K-flat-resolution), 0G7E (lemma-pullback-K-flat), 07A4 (lemma-pullback-tensor-product); coherent quotient towers and normalized DVR effectivity.

### Original step 5 -> lem-pur-completed-comparison-quotient-realization

The cochain maps of [lem-pur-cochain-pullback-tensor-coherence] give the strict tower isomorphism $f_n^*T_n\to W_n$ and its strict inverse. Apply [lem-pur-integral-tower-limit-comparison] to the $T,U,V$ of step 4. With the substitution identifications of [lem-pur-completed-operation-tower-substitution], its actual derived-limit map is the required comparison between completed pullback of $M\widehat\otimes^L N$ and completed tensor of $Lf^*M,Lf^*N$. The functor is [lem-weil-pbc-ringed-strict-tower-homotopy-limit]; its naturality and the resolution comparisons of [lem-pur-integral-operations-well-defined] give naturality in $M,N$ and independence of the chosen representatives.

Dependencies: lem-pur-cochain-pullback-tensor-coherence, lem-pur-completed-operation-tower-substitution, lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-pur-integral-operations-well-defined, lem-pur-integral-tower-limit-comparison.

Source: literature/stacks-project/sites-cohomology.tex; Tag 07A4, strict quotient comparison; completed-operation substitution.

### Original step 6 -> lem-pur-completed-comparison-quotient-realization

By [lem-pur-integral-operations-preserve-constructible], $M\widehat\otimes^L N$ is constructible on $Y$ and its pullback is constructible on $X$. The same lemma first puts $Lf^*M,Lf^*N$ in $D^b_c(X,\mathcal O_E)$ and then puts their completed tensor there. This is a full subcategory of the ambient derived category [def-weil-derived-complete-integral-detailed], so the ambient comparison and its inverse are morphisms of that subcategory.

Dependencies: lem-pur-integral-operations-preserve-constructible, def-weil-derived-complete-integral-detailed.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Bhatt--Scholze, Lemmas 6.5.4, 6.5.5, 6.5.9 (5).

### Original step 7 -> lem-pur-completed-comparison-quotient-realization

The finite associativity, signed symmetry, unit and pullback-composition equations from [lem-pur-cochain-pullback-tensor-coherence] are compatible with every quotient transition. The tower-level assertion [lem-pur-integral-coherence-tower] therefore identifies them as equalities of strict normalized systems and gives their integral images after applying [lem-pur-completed-operation-tower-substitution] and [lem-weil-pbc-ringed-strict-tower-homotopy-limit].

Dependencies: lem-pur-cochain-pullback-tensor-coherence, lem-pur-completed-operation-tower-substitution, lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-pur-integral-coherence-tower.

Source: literature/stacks-project/sites-cohomology.tex; Tag 07A4, chain coherence realized on normalized systems.

### Original step 8 -> lem-pur-completed-comparison-quotient-realization

The coherent counit comparisons of [lem-coef-normalized-dvr-effectivity], applied to the source and target systems of the strict comparison, identify its reduction with the finite comparison. Their naturality applies to this actual map of systems, and [lem-pur-completed-operation-tower-substitution] carries the counits to the completed operations. No faithfulness assertion for individual finite-reduction functors is needed.

Dependencies: lem-coef-normalized-dvr-effectivity, lem-pur-completed-operation-tower-substitution.

Source: literature/stacks-project/sites-cohomology.tex; Coherent normalized-tower counits and reduction of the strict comparison.

### Original step 9 -> lem-pur-completed-comparison-quotient-realization

For $E\subset L$ put $B_m=\mathcal O_L/\varpi_L^m$. The strict quotient models of [def-weil-integral-scalar-extension] and the coherent reduction model [lem-pur-coefficient-extension-reduction-model] give the normalized $B_\bullet$-tower, including ramified extensions. The quotient K-flatness is [lem-pur-kflat-change-of-rings], and the scalar-association and transition equations are exactly [lem-pur-scalar-extension-tower-coherence].

Dependencies: def-weil-integral-scalar-extension, lem-pur-coefficient-extension-reduction-model, lem-pur-kflat-change-of-rings, lem-pur-scalar-extension-tower-coherence.

Source: literature/stacks-project/sites-cohomology.tex; Quotient scalar-extension models and successive derived coefficient normalization.

### Original step 10 -> lem-pur-completed-comparison-quotient-realization

Use the pullback and tensor scalar-extension isomorphisms of [lem-pur-integral-operations-scalar-extension] in their canonical quotient-model form. The tower coherence statement [lem-pur-scalar-extension-tower-coherence] says that both routes around the comparison square send $b\otimes(x\otimes y)$ to $(b\otimes x)\otimes(1\otimes y)$ and commute with every quotient and coefficient square. Applying [lem-weil-pbc-ringed-strict-tower-homotopy-limit] and [lem-pur-completed-operation-tower-substitution] gives the integral scalar-extension square.

Dependencies: lem-pur-integral-operations-scalar-extension, lem-pur-completed-operation-tower-substitution, lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-pur-scalar-extension-tower-coherence.

Source: literature/stacks-project/sites-cohomology.tex; Canonical quotient comparisons and strict system scalar-extension square.

### Original step 11 -> lem-pur-bilinear-comparison-coefficient-descent

By [def-weil-rationalization-karoubi], every rational object is an integral object and every morphism is a finite sum of $u\otimes a$, with $u$ integral and $a\in E$. Define $\mu^E$ to be the image $\mu^{\mathcal O_E}\otimes1$; its inverse is the image of the integral inverse. The operations on rational morphisms are the scalar extensions specified in [def-weil-derived-pullback-tensor-hom]. The integral naturality identity for $u,v$, multiplied by the corresponding scalars, gives rational naturality; add the resulting identities for sums. Every integral coherence equation remains an equality after tensoring Hom groups with $E$, so the rational associativity, symmetry, unit and composition equations follow. The scalar-extension square of the preceding scalar-extension steps likewise remains commutative, since the rational scalar-extension functor is the one induced from the integral scalar-extension functor.

Dependencies: def-weil-rationalization-karoubi, def-weil-derived-pullback-tensor-hom.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-rationalization-karoubi.md; The raw scalar-localization definition: Hom tensor E; all identities are images of the integral identities.

### Original step 12 -> lem-pur-bilinear-comparison-coefficient-descent

For objects $(E,M),(E',N)$ at the algebraically closed level, choose a common finite coefficient field $L$ and form the rational comparison there, conjugated by the scalar-extension comparisons as prescribed in [def-weil-derived-pullback-tensor-hom]. Represent the inverse by the inverse rational comparison with the inverse conjugating comparisons. In [def-weil-algebraically-closed-coefficients], morphisms are classes over common finite fields, and two representatives agree if they agree after passage to a further common field. The scalar-extension calculation after rationalization says precisely that passing from $L$ to any larger field sends this comparison to the same comparison there; hence the class and its inverse are independent of $L$. Represent any finite naturality or coherence diagram over a single common finite field; the rational identity proved in the preceding rationalization step gives its equality in the colimit Hom group. This proves all the asserted compatibilities at $\Qlb$, including scalar extension into $\Qlb$.

Dependencies: def-weil-derived-pullback-tensor-hom, def-weil-algebraically-closed-coefficients.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-algebraically-closed-coefficients.md; The common-stage Hom colimit and equality rule; finite-stage definition of the operations.

## What remains

The three new statement-only tasks intentionally remain unsplit for parallel stage-1 workers. No mathematics of the existing item is abandoned. Server dry run and delivery results are recorded by the required delivery tool; no local checker or compiler is run.
