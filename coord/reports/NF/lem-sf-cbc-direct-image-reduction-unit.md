# Worker report — NF, 2026-10-22

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-cbc-direct-image-reduction-unit.json`: unchanged statement and statement dependencies; three-step assembly, 2629 characters.
- `dag/nodes/sec-smooth-purity/lem-sf-cbc-normalized-augmentation-transport.json`: statement, status unsplit, no Mathlib match; the four-category normalized transport calculation, including both unit equations and naturality.
- `dag/nodes/sec-smooth-purity/lem-sf-cbc-constant-perfect-projection-models.json`: statement, status unsplit, no Mathlib match; explicit bounded constant-sheaf models, finite-free retract data and canonical evaluated projection for arbitrary individually perfect algebra coefficients.
- `citations.json`: literal statement quotations for every use in the parent assembly.

## Attachments

None. Searching all of `lean/WeilConjectures` for the blueprint tag and directImageReductionUnit found no exact finished declaration. The project's `lean/Sheaf/Paper/SfCbcDirectImageReductionUnit.lean:129` states the item, but its proof ends in `sorry`; its docstring still records the five returned steps. It is reference material and cannot justify ATTACH. No Lean was written or compiled.

## WANTED

None. The source paragraphs and blueprint needed here are present.

## What was wrong and what changed

The return is the human's 2026-10-21 work-spreading decision, applied to this node on 2026-10-22: 4462 proof characters must be distributed across at least two independent statement-only nodes and an assembly of at most 3000 characters. There are no numbered mathematical corrections in this return. The sandbox initially contained only the brief markers, with no item, report or searches to reuse. I copied the current reviewed repository item, including its citations, searches, source and Lean metadata; the inherited statement is byte-for-byte unchanged.

Old Step 1 remains the explicit strict augmentation square in assembly Step 1. Old Steps 2 and 3 become the argument of normalized-augmentation-transport, which states the complete categorical pasting problem with all functors, natural comparisons, normalization and naturality hypotheses. Old Step 4 becomes the constant-perfect-projection-models argument with arbitrary perfect algebra coefficients. Old Step 5 remains the explicit levelwise cohomology detection in assembly Step 3. Assembly Step 2 checks every hypothesis of the transport lemma. Both new nodes have proof=[], proof_deps=[], proof_origin=null and status=unsplit. Their proof briefs are below, outside the node statements; another worker can start on either one independently. None of the inherited mathematical argument has been discarded or hidden behind a summary: all five returned steps are copied verbatim at the end of this report.

The extracted arguments have approximately 1491 and 1436 characters in the old proof. The remaining two original arguments total 1535 characters; their assembly with the new lemmas totals 2629. The first extraction is formal categorical algebra, deliberately separated under this explicit work-spreading return even though its individual rewrites are elementary. The second includes the actual constant-model construction, not an assumption that a constant sheaf is already perfect. Neither node restates the whole item; in particular the first assumes the strict augmentation square rather than constructing it, and the second has no completion or total-limit equation and does not assert that the whole strict tower projection is invertible.

## Proof brief for normalized-augmentation-transport

This is an agent-written abstraction of returned Steps 2 and 3, not a claim that Stacks directly states this four-category theorem. I read fix-lem-exchanges Step 5 and the first, diagram-site proof of Stacks 0A07 (lemma-Rf-commutes-with-Rlim) in sites-cohomology.tex: that proof normalizes the derived comparison by the common underived composite. Its naturality is the input to this extraction.

Write composition right-to-left, exactly as in the node. Apply L_V to h_F i_{V,PF}=Q(i_{U,F}) chi_F, and precompose by j_{V,PF}^{-1}. The assumed normalization replaces L_V(chi_F) j_{V,PF}^{-1} by b_{Delta_U F} P(j_{U,F}^{-1}). Naturality of b at i_{U,F}:Delta_U F -> B_U F gives L_VQ(i_{U,F}) b_{Delta_U F}=b_{B_U F} P L_U(i_{U,F}). Functoriality of P now gives L_V(h_F) eta_{V,PF}=b_{B_U F} P(eta_{U,F}). Composing with the inverse of b_{B_U F} gives rho_F eta_{V,PF}=P(eta_{U,F}). The first equation is retained separately because the parent also requires it.

For t:F -> F', naturality of b at B_U(t) gives P(C_Ut)b_{B_U F}^{-1}=b_{B_U F'}^{-1}L_VQ(B_Ut). Naturality of h gives Q(B_Ut)h_F=h_{F'}B_V(Pt). Applying L_V and substituting gives P(C_Ut)rho_F=rho_{F'}C_V(Pt), exactly the specified natural transformation. These calculations require no limit universal property and no faithfulness of any evaluation. They also show why unrelated choices of b or the constant identifications j would be wrong. All objects and arrows in each equation have been type-checked in words; j is not silently set to the identity in the general statement.

## Proof brief for constant-perfect-projection-models

I read the precise perfect-object hypothesis and counit-defined map in Stacks 0944 (lemma-projection-formula) and Equation 0B56, plus exact sheafification in sites-modules.tex 03EI (lemma-sheafification-exact). For the parent context I read proetale.tex 099N (lemma-pushforward-Noetherian-case), parts (3),(4), and its proof using 0A07. Neither the extra finite-cardinality hypothesis nor derived completeness is needed for this extracted model argument.

For each n choose a bounded finite-projective A-complex E_n representing B_n[0]. Every finite-projective term admits a split finite-generating surjection A^m -> E_n^r; the resulting section and projection have p s=1. The exact constant module functor and its finite-power identification of lem-sfb-constant-finite-free-presentation-extension carry the complex, its zero terms and every splitting identity to sheaves. Exactness makes the realized derived representative isomorphic to the constant B_n[0], including when the original marking was only an isomorphism in D(A). This is precisely the strict-perfect package of def-weil-pbc-strict-perfect-coefficient-package; the split maps are degreewise, not asserted to be maps into a single free complex.

Apply lem-sbc-ringed-site-perfect-projection-formula to this constant target coefficient and arbitrary unbounded F. The structural ring identification makes pullback of that constant coefficient the corresponding constant coefficient on the source. The canonical diagram morphism is already constructed using the actual algebra tower and its transitions, independently of the E_n choices. The evaluation conclusion of lem-weil-pbc-augmented-diagram-projection-mate identifies its evaluated arrow, with the normalized chi and direct-image evaluation comparisons, with exactly the preceding counit-tensor projection, not an arbitrary isomorphism having the same endpoints. It is therefore invertible and natural in F. Each n is handled separately; no transition lift between perfect resolutions, common amplitude, or common rank is required. This is the whole returned Step 4 argument.

## Searches and duplicate checks

I searched all DAG statements and the blueprint for augmentation/limit transport, completion units, strict perfect projection, and constant perfect models. `tools/blueprint_refs.py ancestor` returns fix-lem-exchanges; both created-node via chains are the item followed by lem-sf-cbc-compact-support-composition-limit. Blueprint searches for augmentation, perfect.*tower, completion.*unit, strict projection, constant perfect, normalized, and projection formula were read. No blueprint node states either full extracted comparison/model statement. Lean source searches of WeilConjectures by the item tag, directImageReductionUnit, constant/perfect and augmentation/transport produced no exact finished attachment. Related Sheaf generic strict-projection declarations were read through their DAG statements and are not mistaken for the concrete constant models.

All new Mathlib searches were run with msearch.py and the exact tool/query pairs and actual returned names are recorded in their nodes and searches.jsonl. Each node has LeanSearch, Loogle, grep and two LeanFinder phrasings. The initial Loogle query using CategoryTheory.NatIso was rejected with unknown identifier and was replaced by the valid CategoryTheory.NatTrans.naturality query; the raw rejected search remains logged. Naturality/whiskering declarations supply individual rewrites, not the whole normalized four-category transport theorem. Perfect-ring-in-characteristic-p, ordinary adic completion, tilde stalks, flat/projective algebra modules, light condensed internal projectivity, and Cantor-Bendixson derived sets do not state the constant sheaf/diagram projection theorem. No unavailable service was recorded as absence. No Mathlib leaf is claimed.

## Review by NF

I checked B through E with the node statements and the cited source paragraphs open. B1: the new files contain statements only and introduce every variable and functor; their argument briefs are solely in this report. B2/B3: the first node defines the categorical naturality convention inline and cites the category definition; the second introduces A, sites, u, all coefficient algebras, the exact realization, strict tower and the actual counit map, with definition nodes for its notions. Their TeX uses one decoded backslash. Their sources explicitly distinguish agent refinements from literal Stacks statements. The item statement, its finite/perfect hypotheses, its unbounded category and specified maps are unchanged.

Assembly Step 1 uses only two statements: ringed-projection-mate-exact explicitly says its structures are natural in E and P; constant-tower-direct-image-normalization provides natural chi and clause (4)'s exact strict augmentation equation for the same quotient tower. I checked both maps against the definition of h. I did not infer equality of derived arrows from equality of their components.

Assembly Step 2 uses normalized-augmentation-transport with exactly the four derived categories and the already specified P,Q,L,R. I checked its normalized j equation against clause (3) of constant-tower-direct-image-normalization, including the inverse orientation; the generic pushforward-limit-comparison statement supplies a natural isomorphism induced from the underived composite, not just unspecified objectwise isomorphisms. The parent convention L(i)=eta is exactly the transported eta after j. Thus both equations and the naturality conclusion used here are literally clauses of the new statement. I checked that no hidden requirement of completeness or invertibility of h appears in this argument.

Assembly Step 3 uses constant-perfect-projection-models only for its asserted actual evaluated counit map and its invertibility. The complete coefficient datum provides perfectness of each A/I^n; its unital quotient transition maps are the algebra transitions required by the new statement. Module inverse image for constant rings has the required ring identification, and arbitrary schemes/morphisms are allowed. The levelwise-abelian statement explicitly gives exact evaluations and levelwise kernels and cokernels; consequently evaluated cohomology of h is invertible in every degree. Zero-component kernels/cokernels are zero tower objects, so each cohomology map is invertible. The unbounded-derived-iso-cohomology statement is precisely the criterion for h to be invertible in the whole derived tower category. Restriction to complete K and substitution into Step 2 are then literal specializations; no completeness premise was used prematurely.

For the first new statement I checked all arrow types and the tests where all functors/comparisons are identities, where B is the zero functor in Ab and eta is noninvertible, and where the categories are empty. All are allowed and the equations hold; no cancellation of eta or h occurs. Changing b by a nontrivial scalar shows the normalization hypothesis is necessary, and the stated hypothesis rules that out. For the second I checked zero algebras/zero complexes, rank zero terms, identity u, I=A (all quotient coefficients zero), I=0 when the parent coefficient conditions hold, and B_n=Z/p^n as perfect but nonflat Z-modules. The proof uses derived tensor, never flatness of the quotients, and permits perfect models of varying lengths. A zero coefficient site causes no reflection-of-constant-sheaves assertion. Finite-power splittings survive even there.

C1/C4: every non-elementary result in the assembly is cited with a literal statement quotation in citations.json; the extracted model lemma supplies the formerly inline perfect-coefficient argument, and the abstract transport lemma supplies the formerly inline normalized pasting calculation. The short explicit cohomology detection does not introduce another sublemma. D1/D2: the new nodes divide different arguments and neither contains the entire conclusion. The first is an abstract conditional transport theorem, the second a constant-model/evaluation theorem; the parent supplies strict augmentation and derived conservativity. Every assembly step is below 2000 characters. No SGA source or alternative proof route is used. Generic off-unit tools are declared in split_report, without changing the maintainer's tool_uses field.

The only repair requested was work-spreading: it is implemented by two independently queued unsplit nodes, with original arguments preserved below, instead of a cosmetic shorter re-push. The statement has not been disputed or changed. Nothing mathematical remains unfinished at stage 1; the new nodes deliberately await their own split workers.

## Not duplicates

lem-sf-cbc-normalized-augmentation-transport vs lem-sf-cbc-direct-image-reduction-unit: the item constructs the strict projection for adic quotient coefficients and proves its invertibility; the new four-category lemma assumes a strict augmentation square, has no sites, coefficients, perfectness or derived structure, and isolates only its normalized transport calculation.

lem-sf-cbc-normalized-augmentation-transport vs lem-sbc-strict-perfect-tower-projection: asserts projection invertibility for normalized ringed data; the new lemma has arbitrary four categories and proves augmentation equations without any perfectness or invertibility premise.

lem-sf-cbc-normalized-augmentation-transport vs lem-sbc-strict-reduction-pullback-square: compares two paths of coefficient pullback in a four-site square; the new lemma transports one augmented transformation through a normalized natural isomorphism.

lem-sf-cbc-normalized-augmentation-transport vs lem-sbc-strict-projection-coaugmentation: is the ringed-site projection coaugmentation conclusion for supplied normalized coefficient/adjunction data; the new lemma states the general four-category pasting calculation for arbitrary functors, i and h, including naturality and inverse-b transport, rather than another specialization of that ringed statement.

lem-sf-cbc-normalized-augmentation-transport vs def-sbc-strict-projection-tower-data: defines normalized derived-limit/direct-image records, whereas the new lemma proves equations for arbitrary functors and natural transformations.

lem-sf-cbc-normalized-augmentation-transport vs lem-sbc-strict-tower-mate-evaluation: identifies evaluation of a four-site square mate, whereas the new lemma concerns transport of augmentations and never evaluates a tower.

lem-sf-cbc-normalized-augmentation-transport vs def-sbc-tower-derived-evaluation-interchange: defines a localization/evaluation interchange for an exact functor; the new lemma proves normalized unit equations without exactness or localization.

lem-sf-cbc-normalized-augmentation-transport vs lem-weil-pbc-direct-image-roos-normalization: identifies Roos-triangle maps under exact-product hypotheses; the new lemma uses no products or cones and treats arbitrary natural comparisons.

lem-sf-cbc-normalized-augmentation-transport vs def-weil-pbc-flat-scalar-koszul-models: defines finite Koszul coordinate and scalar-change models; the new lemma has no Koszul, flatness or scalar-change data.

lem-sf-cbc-normalized-augmentation-transport vs lem-weil-pbc-ringed-strict-tower-projection-morphism: constructs a projection for finite-free augmented complex towers and its Roos normalization; the new lemma applies to arbitrary categorical transformations with no complex representatives or Roos triangles.

lem-sf-cbc-normalized-augmentation-transport vs lem-weil-pbc-ordered-exchange-coefficient-comparison: compares completed and constant coefficient square mates for an adic scheme square; the new lemma isolates an arbitrary four-category augmentation transport with no scalar restriction or base-change square.

lem-sf-cbc-normalized-augmentation-transport vs lem-weil-pbc-flat-scalar-koszul-tower-comparison: compares flat ring-change Koszul towers and their limit units; the new lemma has no ring-change or Koszul hypotheses and proves the general two-square transport law.

lem-sf-cbc-constant-perfect-projection-models vs lem-sfb-constant-finite-free-presentation-extension: supplies exact constant realization and finite-power/matrix identities; the new lemma constructs bounded representatives of derived perfect coefficients and identifies the actual evaluated diagram projection, which is not a clause of the presentation statement.

lem-sf-cbc-constant-perfect-projection-models vs lem-sbc-strict-perfect-tower-projection: assumes locally perfect sheaf coefficients and supplied normalized tensor-corner data and concludes strict invertibility; the new lemma constructs the required constant bounded finite-projective sheaf models from algebraic representatives and identifies their evaluated counit maps. It does not conclude whole-tower invertibility.

lem-sf-cbc-constant-perfect-projection-models vs lem-sbc-projection-mate-slice-presentation: compares projections after restriction to a target slice; the new lemma realizes algebraic perfect models as constant coefficients and identifies evaluation on an inverse sequence.

lem-sf-cbc-constant-perfect-projection-models vs def-sbc-quotient-exchange-scalar-comparisons: defines quotient square-mate scalar comparisons; the new statement allows arbitrary perfect algebra towers and proves a representative/evaluated-projection claim, with no square.

lem-sf-cbc-constant-perfect-projection-models vs def-sbc-strict-augmented-coefficient-presentation: defines normalized reduction data but does not prove that algebraic finite-projective representatives realize the desired constant coefficients or make evaluated projections invertible.

lem-sf-cbc-constant-perfect-projection-models vs lem-sbc-strict-reduction-pullback-square: is a four-site pullback coherence equation; the new lemma constructs constant perfect coefficient models and identifies a one-edge evaluated projection.

lem-sf-cbc-constant-perfect-projection-models vs lem-sbc-strict-projection-coaugmentation: asserts a total-limit unit identity with no perfectness; the new lemma has no completion or limit-unit equation and concerns explicit algebraic models and evaluated isomorphisms.

lem-sf-cbc-constant-perfect-projection-models vs lem-sbc-ringed-site-perfect-projection-formula: assumes an already perfect coefficient sheaf; the new lemma constructs that hypothesis from a perfect algebraic module, with its explicit finite-free splittings, and identifies the existing whole-diagram arrow under evaluation.

lem-sf-cbc-constant-perfect-projection-models vs lem-sbc-strict-tower-mate-evaluation: evaluates square mates for abstract normalized data; the new lemma handles a single projection edge, realizes the coefficient models and proves the evaluated map invertible.

lem-sf-cbc-constant-perfect-projection-models vs lem-sbc-strict-quotient-exchange-unit-equation: is a four-site square-mate/completion equation for supplied perfect coefficients; the new lemma constructs perfect constant models and their evaluated projection and has no square or total-limit equation.

lem-sf-cbc-constant-perfect-projection-models vs def-sbc-strict-coefficient-exchange-arrows: defines exchange arrows from supplied normalized data; the new statement proves constant-model and projection-evaluation properties without a square.

lem-sf-cbc-constant-perfect-projection-models vs lem-sf-projection-bounded-finite-free-constant: treats a single bounded finite-free coefficient complex on small etale sites of schemes; the new lemma admits arbitrary small topoi and individually perfect algebra towers with finite-projective retract models, and specifies evaluation of the actual strict diagram arrow.

Additional close statements read in full:

lem-sf-cbc-constant-perfect-projection-models vs lem-pur-perfect-quotient-exchange-normalization: that theorem handles adic quotients, quotient-linear restriction and completion-unit compatibility. The new statement allows arbitrary perfect algebra coefficients, constructs the actual finite-projective constant representative/splitting data, and isolates the evaluated projection without a completion-unit or quotient-linear comparison.

lem-sf-cbc-constant-perfect-projection-models vs def-weil-pbc-strict-perfect-coefficient-package: that definition describes sheafifying a supplied package; the new theorem asserts that it represents the specified constant coefficient in the derived category and identifies the specified evaluated diagram projection as an isomorphism.

Server-source-order pairs inspected after the first dry run:

lem-sf-cbc-constant-perfect-projection-models vs lem-weil-pbc-site-r-module-presheaf-sheafification-exact: proves exact presheaf sheafification for site R-modules; the new statement adds finite-projective derived representatives and identifies evaluated counit projection maps for a coefficient tower.

lem-sf-cbc-constant-perfect-projection-models vs lem-weil-pbc-module-presheaf-sheafification-exact: is exact sheafification for O_X-module presheaves on scheme opens; the new theorem is a constant coefficient perfect-model and evaluated diagram projection theorem on arbitrary small sites.

lem-sf-cbc-constant-perfect-projection-models vs lem-weil-pbc-sheaf-tensor-closed: constructs the exact symmetric monoidal sheafification and closed tensor structure; the new statement identifies bounded constant coefficient representatives and the specific evaluated derived direct-image projection.

lem-sf-cbc-constant-perfect-projection-models vs lem-sfb-constant-to-continuous-scalar-flat: is flatness of discrete-to-continuous coefficient extension for a topological PID on profinite sets; the new statement uses constant ring sheaves, arbitrary A, and perfect algebra coefficient towers.

lem-sf-cbc-constant-perfect-projection-models vs lem-sfb-etale-stalk-constant-complex-exactness: gives stalk/constant cohomology comparisons on scheme etale sites; the new theorem has no stalk, admits arbitrary small topoi, and constructs perfect models with their evaluated strict projection.

lem-sf-cbc-constant-perfect-projection-models vs lem-sfb-flat-constant-module-scalar-mono: proves scalar monomorphisms on flat constant modules; the new statement requires algebraic perfectness instead of flatness and concerns bounded representatives and derived projection maps.

lem-sf-cbc-constant-perfect-projection-models vs lem-sf-intrinsic-realization-origin-comparison: identifies an intrinsic finite-coefficient realization after restriction on a scheme; the new statement concerns arbitrary individually perfect A-algebra coefficients and their explicit bounded sheaf representatives and diagram projections.

lem-sf-cbc-constant-perfect-projection-models vs lem-pur-constant-two-term-resolution: constructs a particular Z_l/l^N constant K-flat resolution and its ordinary tensor augmentation; the new statement allows arbitrary bounded finite-projective models of arbitrary perfect algebra coefficients and identifies the evaluated diagram direct-image map.

lem-sf-cbc-constant-perfect-projection-models vs lem-sf-proetale-residue-module-tensor-homology: transfers tensor homology vanishing from a principal residue field coefficient to annihilated modules; the new statement constructs perfect constant models and identifies projection evaluations, without a maximal ideal or homology-vanishing premise.

lem-sf-cbc-constant-perfect-projection-models vs def-weil-pbc-four-arrows: defines finite square-exchange arrows over the completed coefficient sheaf and requires a proper scheme square with etale-origin witnesses; the new statement treats a single arbitrary topos morphism with constant A and arbitrary perfect algebra towers, and constructs their constant representatives.

lem-sf-cbc-constant-perfect-projection-models vs def-weil-pbc-four-corners: defines four objects of a proper scheme base-change square over completed adic coefficients; the new theorem uses constant A on arbitrary small sites, has no square, and proves perfect-model and evaluated projection properties.

lem-sf-cbc-normalized-augmentation-transport vs def-weil-pbc-derived-tower-models: defines universal right-derived models for additive functors on tower complexes; the new theorem is an augmentation-pasting equation for arbitrary categories and functors with no derived-model hypothesis.

lem-sf-cbc-normalized-augmentation-transport vs lem-weil-pbc-constant-tower-pushforward-normalization: constructs and normalizes chi and the constant-tower counit for ringed topoi; the new lemma assumes chi and its compatibility with b and proves the augmented unit transport and naturality for arbitrary categories.

lem-sf-cbc-normalized-augmentation-transport vs lem-weil-pbc-exact-adjoint-tower-models: constructs K-injective tower models and product/limit comparisons from an exact module adjunction; the new statement assumes natural comparisons and proves augmentation equations without modules, K-injectivity, products or adjunctions.

lem-sf-cbc-normalized-augmentation-transport vs lem-weil-pbc-flat-scalar-tower-limit-square: proves a flat scalar-restriction/direct-image/limit square with specified coefficient rings; the new theorem has no scalar extension and proves arbitrary augmentation unit transport from its two stated squares.

lem-sf-cbc-normalized-augmentation-transport vs lem-weil-pbc-strict-scalar-koszul-comparison: compares actual ordered Koszul tensor complexes before deriving; the new statement has no Koszul coordinates or scalar restriction and transports arbitrary augmented transformations through b.

lem-sf-cbc-normalized-augmentation-transport vs lem-weil-pbc-tower-derived-evaluation-normalization: constructs the evaluation/direct-image comparison with its normalized counit; the new lemma never evaluates and proves total augmentation transport for arbitrary categorical data.


## Retained returned proof, verbatim

### Returned Step 1

Put $B_T=(\underline{P_n}_T)_n$. On the diagram sites the projection morphism is natural in both the source object and the coefficient object by [lem-weil-pbc-ringed-projection-mate-exact]. Its value at $\Delta_UF$, followed on the source by the natural constant-tower comparison $\chi_{u,F}\otimes1$, is exactly the specified $h_{u,F}$; consequently $h$ is natural in $F$. Clause (4) of [lem-sf-cbc-constant-tower-direct-image-normalization], with $f=u$ and $M=F$, applies to precisely these constant coefficient sheaves, quotient augmentation and counit-defined diagram projection. It gives, in $D(\mathcal T_V)$,
$$h_{u,F}i_{V,PF}=Q(i_{U,F})\chi_{u,F}.$$
This is an equality of strict derived-tower morphisms, valid for arbitrary $F$.

### Returned Step 2

Write $b_N=b_{u,N}$ and $\chi_F=\chi_{u,F}$. Naturality of the canonical comparison in [lem-weil-ringed-tower-pushforward-limit-comparison], applied to the actual tower morphism $i_{U,F}:\Delta_UF\to\mathcal R_UF$, gives
$$\mathcal L_VQ(i_{U,F})\,b_{\Delta_UF}=b_{\mathcal R_UF}\,P\mathcal L_U(i_{U,F}).$$
Clause (3) of [lem-sf-cbc-constant-tower-direct-image-normalization] gives $\mathcal L_V(\chi_F)^{-1}b_{\Delta_UF}=1$, under the stipulated constant-tower limit identifications, hence $b_{\Delta_UF}=\mathcal L_V(\chi_F)$. Apply $\mathcal L_V$ to the equality of Step 1, substitute this naturality square, and use the specified $\mathcal L_T(i_{T,H})=\eta_H$. The resulting equality is
$$\mathcal L_V(h_{u,F})\eta_{PF}=b_{\mathcal R_UF}P(\eta_F).$$
Left composition with $b_{\mathcal R_UF}^{-1}$ proves $\rho_{u,F}\eta_{PF}=P(\eta_F)$. Every substitution took place before evaluating any tower morphism.

### Returned Step 3

The comparisons $b$ are natural isomorphisms by [lem-weil-ringed-tower-pushforward-limit-comparison]. Together with naturality of $h$ from Step 1 and functoriality of $\mathcal L_V$, this proves naturality of $\rho=b^{-1}\mathcal L_Vh$. Explicitly, for $t:F\to F'$ the naturality squares for $h$ and $b$ give
$$P(C_Ut)\rho_{u,F}=\rho_{u,F'}C_V(Pt).$$
Indeed insert $b_{\mathcal R_UF'}b_{\mathcal R_UF'}^{-1}$ on the left, move $P(C_Ut)$ across $b^{-1}$ using its naturality square, and then move $\mathcal L_V(Q\mathcal R_Ut)$ across $\mathcal L_V(h_{u,F})$ using the square for $h$.

### Returned Step 4

Fix $n\geq1$. The perfectness hypothesis [def-weil-pbc-complete-coefficient-datum] supplies a bounded finite-projective $A$-complex representing $P_n$. In each degree choose a finite generating surjection from $A^{r}$ and split it by projectivity. The exact constant-module functor and its finite-power identifications [lem-sfb-constant-finite-free-presentation-extension] carry the representing complex and these splitting identities to sheaves. Thus $\underline{P_n}_V$ is represented by a bounded complex of direct summands of finite free $\underline A_V$-modules, so it satisfies precisely the perfectness hypothesis of [lem-sbc-ringed-site-perfect-projection-formula]. That theorem, for $u$, $E=F$ and $P=\underline{P_n}_V$, makes the canonical counit-tensor projection an isomorphism for every $F\in D(U,A)$. In the general augmented-diagram theorem [lem-weil-pbc-augmented-diagram-projection-mate], specialize the coefficient algebra tower to $B_V$ with its unital quotient transitions. Its projection mate, source comparison and augmentation are the ones used here. Its evaluation conclusion identifies $\operatorname{ev}_n(h_{u,F})$ with this very projection morphism, using the canonical constant-coefficient pullback identification. Therefore every evaluation of $h_{u,F}$ is the required perfect-$P_n$ projection-formula isomorphism. The bounded representative was chosen separately for each $n$; no common interval is used.

### Returned Step 5

By [lem-weil-tower-category-levelwise-abelian], kernels and cokernels in $\mathcal T_V$ are computed levelwise. Hence for every degree $r$, evaluation identifies $\operatorname{ev}_n H^r(h_{u,F})$ with $H^r(\operatorname{ev}_n h_{u,F})$, which is invertible by Step 4. The kernel and cokernel of $H^r(h_{u,F})$ therefore have every component zero and are zero tower objects. Thus every $H^r(h_{u,F})$ is invertible. The cohomology criterion [lem-weil-pbc-unbounded-derived-iso-cohomology] now implies that $h_{u,F}$ is invertible in $D(\mathcal T_V)$. This proves the required assertion for complete $K$ (and actually for all $F$). Specializing the equality of Step 2 to $F=K$ gives exactly the final displayed equation of the statement. Naturality on complete objects is the restriction of Step 1.
