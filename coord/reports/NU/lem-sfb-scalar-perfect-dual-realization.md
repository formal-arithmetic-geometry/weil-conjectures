# Worker report: lem-sfb-scalar-perfect-dual-realization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-perfect-dual-realization.json: statement unchanged; split into five assembly steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-dual-evaluation-descent.json: statement, unsplit; no Mathlib match for the normalized comparison on all scalar modules.
- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-dual-evaluation-inverse.json: statement, unsplit; no Mathlib match for the restriction-compatible finite-projective inverse after constant sheaf scalar extension.
- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-dual-signed-assembly.json: statement, unsplit; no Mathlib match for signed assembly under an arbitrary additive functor equipped with a natural dual comparison.
- citations.json: verbatim statements for each citation of each assembly step.
- report.md and searches.jsonl: review and actual search evidence. Helper scripts remain sandbox-only and are not delivery files.

## Attachments

None. I searched the live WeilConjectures source for the item tag and scalar-dual concepts; it has no exact finished declaration. Sheaf.Paper.ScalarPerfectDualRealization is additional reference material. Its evaluation_existsUnique, evaluation_natural_isIso and derived_comparison_natural have sorry. The already implemented coordinates and assembly still rely on those open evaluation results; they do not finish the whole item. No Lean file was written and no compiler, Lake or build was run.

## WANTED

None. The current blueprint and Stacks sources used here are present locally.

## Returned point and repair

The return requires at least two comparable, statement-only tasks, retaining the item statement and all existing arguments, with at most 3000 characters of parent proof. This delivery adds three tasks. Evaluation descent and uniqueness works for every module; the inverse task assumes a normalized evaluation map and proves invertibility by finite-projective coordinates; signed assembly assumes an arbitrary additive functor and a natural termwise comparison. They are independent arguments with self-contained hypotheses, not three copies of the original derived-duality statement. Each has proof=[], proof_deps=[], proof_origin=null, status=unsplit. The item statement is byte-identical to the current repository. Its five proof texts total 2254 characters. The derived-category clause remains an assembly using the existing arbitrary-resolution quasi-isomorphism criterion.

The sandbox initially held only dispatcher markers, with no retained node, report or searches. I copied the live item, which contains the returned seven-step proof, and preserved it verbatim below. There was no earlier local work to discard. I read GOAL.md, SETUP.md's three levels, the worker and stage-1 contracts and delivery-errors B--E. The unit is sk-thm-sf-ctf-stability; the current main-20261015 unit and its internal-Hom proof, paragraph 2 final sentence, give the locally constant perfect-dual route. No chapter or unit route was changed and no unit realized field is owed by this non-key node.

## Review by NU

I read Stacks sites-cohomology.tex at lemma-Rhom-strictly-perfect (08JH), lemma-dual-perfect-complex (08JJ), especially its final finite-free/direct-summand reduction, and section-hom-complexes (0A8X), including the actual signed differential. I also read the current blueprint sk-thm-sf-ctf-stability-internal-hom.proof.md and the relevant evaluation, scalar coordinate, comparison and derived-comparison docstrings in the live Sheaf module. These sources justify the same route; the scalar sheafification formulas and generalized additive-functor formulation are agent-written expansions, not claims that Stacks states these exact variants.

For new evaluation-descent I checked that B is a sheaf of commutative algebras over the constant ring, that the formula uses alpha(phi(v)), and that both tensor factors are balanced. The statement requires descent on all localized sites, uniqueness and the naturality square for every f:V->W, without incorrectly adding finite projectivity. The two naturality composites evaluate to bb'psi(f(v)). I read the definitions of constant module functor, module sheafification, sheaf tensor and internal Hom. The sheafification adjunction alone does not state this comparison; the new task includes extending the balanced pairing in both inputs and checking restriction and uniqueness on local tensor generators.

For new evaluation-inverse I checked the scalar finite-projective hypothesis and the supplied normalized sheaf morphism. The section i of a finite free surjection p gives v_j=p(e_j), lambda_j=e_j^*i. Both dual-generator identities are explicitly in the statement, as is gamma(h)=sum h(1 tensor v_j) tensor lambda_j. I evaluated beta gamma(h) on b' tensor v: the result is b' sum h(1 tensor v_j)lambda_j(v)=h(b' tensor v). In the other order it is sum b phi(v_j) tensor lambda_j=b tensor phi. Restriction commutes with this finite sum, and local tensor generation extends the identities beyond pure tensors. The independence assertion is uniqueness of the inverse. This is an ordinary scalar-dual versus sheaf-dual identification, which cannot be obtained by merely citing the internal sheaf retract duality theorem: that theorem's input dual is already a sheaf Hom, while ours starts with the constant sheaf of the scalar dual.

For new signed-assembly I read the scalar total Hom and signed sheaf dual definitions. Its input is any additive T, with a supplied natural eta, so it makes no finite-projectivity or sheaf scalar-flatness assertion. Applied to d_F^(-q-1), the naturality square gives the required signed chain identity after multiplication by -(-1)^q. The (-q,0) scalar coordinate is the only surviving scalar Hom factor; its inverse is the single cochain. Naturality for cochain maps follows from the same precomposition square. The statement includes an actual chain map, an isomorphism when all relevant eta are isomorphisms, and its derived-category image, rather than only degreewise homology groups. Bounds use Hom(0,R)=0 and T(0)=0. The separate product-Hom-to-signed-dual presentation is already the statement of lem-sc-hom-complex-to-single and was not recreated.

Parent step 1 uses def-sf-site-constant-module-functor and def-weil-presheaf-modules-sheafification for the functor and uniqueness, def-pur-sheaf-tensor-product for tensor balancing, and lem-sfb-constant-finite-free-presentation-extension for C_B(R^N)=B^N without flatness. I opened the latter statement: its flatness condition applies only to the later exact-sequence clause, not the finite-power or matrix clauses used here. Applying a functor to the supplied splitting of def-weil-pbc-strict-perfect-coefficient-package gives C_B(p)C_B(i)=1. Additivity is checked on generators and extended by sheafification, a routine elementary step. This reuses the old finite-product/unit/biproduct calculation rather than creating a duplicate lemma for it.

Parent step 2 uses exactly the short-exactness clause of lem-sfb-ringed-site-finite-retract-dual-exact, with coefficient B and T=E^r. Its hypotheses are supplied by step 1. It says internal sheaf Hom is exact; I did not infer exactness of global sections or global Hom.

Parent step 3 cites both new evaluation statements. Descent gives beta for every scalar module and naturality; the inverse task applies because V is finite projective and beta satisfies its precise normalization. The inverse task assumes the morphism rather than calling the descent theorem in its own proof, so the two tasks can be worked on independently.

Parent step 4 cites new signed-assembly, def-sc-signed-sheaf-dual-complex, lem-sc-hom-complex-to-single and def-pur-hom-complex. I opened all of their statements. Additivity, contravariant naturality and isomorphism of each eta_F^r are exactly the assumptions established in steps 1 and 3. The existing Hom-to-single lemma states an isomorphism of complexes, not merely degreewise coordinates. Projection to the only nonzero factor commutes with precomposition by f^(-q), which verifies the naturality needed when switching presentations; the differential is explicitly the one in the cited definition.

Parent step 5 uses lem-pc-bounded-exact-term-hom-quasi-iso and def-pur-derived-internal-hom. I checked the former allows arbitrary unbounded source/target complexes of the quasi-isomorphism; E, not I, must be bounded, and E's termwise internal Hom must be exact. These are steps 1 and 2. The latter statement explicitly supplies the fixed functorial K-injective model and the canonical independence of other resolutions. Thus the comparison is natural, and every chosen K-injective augmentation is allowed. We never assert tensoring an arbitrary short exact sequence with B is exact.

Edge cases: V=0 and N=0 make both sums empty and both sides zero. R=0 forces the unital coefficient B to be zero, so the assertions remain valid. The empty site likewise gives zero sheaves. For non-flat R=Z to B=Z/2, the finite-free coordinates and inverse still hold. A nonfree projective is handled by splitting, without choosing a basis for V. In a two-term complex Z --2--> Z in degrees 0,1, the reversed dual is in degrees -1,0 with differential +2, agreeing with -(-1)^(-1). In characteristic 2 the signs reduce consistently. For a>b the support is empty and all complexes in the bound clause are zero. No boundedness on the K-injective target is used.

I checked C1/C4 by opening every cited statement and copying it into citations.json, and checked B1--B10, C1--C8, D1--D5 and E1--E7 against the actual files. The current statement needed no dispute or correction. No new node has proof steps; all three have real distinct input hypotheses. No parent step is longer than 2000 characters. All new statement references are recorded in stmt_deps and parent proof_deps is exactly the union of uses. The source and blueprint ancestor of every new node are explicit. Off-unit generic tools are declared in split_report.tool_uses, preserving the already accepted bounded-Hom tool and explaining the scalar-coordinate and presentation tools. There is no new dependency back to the item.

## Mathlib and duplicate search review

I used msearch.py for every Mathlib search and read the returned hits. All recorded queries are copied exactly from searches.jsonl, with unavailable LeanSearch requests recorded as unavailable (HTTP rate limit). Two phrasings were tried for evaluation and signed assembly; the all-module descent and normalized inverse were also searched separately. I read PresheafOfModules.sheafificationHomEquiv in Presheaf/Sheafification.lean, dualTensorHomEquiv in LinearAlgebra/Contraction.lean and the toSingleEquiv definition and inverse in HomComplexSingle.lean. These respectively give a generic sheafification adjunction, ordinary module tensor-Hom, and external cochain coordinates. None is a one-line specialization to the new internal sheaf comparisons with the stated normalization, restriction or generic signed assembly. Generic mapHomologicalComplex preserves covariant additive functors, while this task compares two contravariant dual constructions with degree reversal; the signed and coordinate checks remain work.

I searched the whole DAG by source tags, scalar/constant dual, realization, free retract and the existing Lean declaration names, and ran blueprint_refs ancestor and search on scalar dual, finite free, signed, constant module, dual comparison, evaluation, Hom complex, constant sheaf dual, evaluation descent, dual generators and dual complex. I read the candidate statements, including the finite-free presentation extension, scalar sheaf dual evaluation, finite-projective internal-Hom evaluation, Hom-to-single and bounded dual/evaluation assembly nodes. No blueprint node states any of the three new tasks. The finite-free scalar result was reused, not recreated. New nodes have same_as=[] and the exact inherited blueprint ancestor and via chain.

## Not duplicates

lem-sfb-scalar-dual-evaluation-descent vs lem-sfb-split-perfect-dual-tor-window: that node starts with a sheaf complex and proves a Tor window; it gives no comparison from the constant sheaf of an ordinary scalar dual. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-sfb-ringed-site-perfect-duality: that node is intrinsic derived tensor-Hom duality for a sheaf-perfect object, without the ordinary scalar dual/sheafification comparison or a supplied additive functor. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-sfb-ringed-site-bounded-evaluation-assembly: that node assembles Tot(F tensor sheaf-dual(E)) into Hom(E,F), over one sheaf of rings; there is no ordinary scalar dual or change from scalar modules to sheaves. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-sfb-scalar-perfect-dual-realization: the parent combines finite-free realization, internal-Hom exactness, every K-injective comparison and the natural derived dual isomorphism; this task isolates a strict subargument with different input hypotheses. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-sfb-ringed-site-bounded-dual-components: that node computes coordinates of the dual and bidual of a sheaf complex; it provides no comparison under a scalar-to-sheaf functor. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-sfb-ringed-site-finite-retract-dual-exact: that node begins with T and its internal SHEAF dual; it proves biduality and exactness, not descent or identification of the constant ORDINARY scalar dual. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-sfb-ringed-site-strict-perfect-hom: that node gives intrinsic sheaf-complex bidual and tensor-Hom isomorphisms; it has no ordinary scalar dual and no comparison eta under T. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-weil-pbc-condensed-internal-hom-sections: that node identifies condensed sections of internal Hom with additive-group Hom, without scalar constant modules, normalized dual tensors or signed assembly. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-weil-pbc-condensed-finite-free-tensor-exact: that node asserts exactness of tensor with a locally finite-free condensed module; it does not construct any dual comparison. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-weil-pbc-derived-coyoneda-evaluation: that node computes global derived Hom by homology of an additive-group-valued derived functor; it has no internal scalar-dual sheaf comparison. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-weil-pbc-ringed-site-locally-free-derived-hom: that node computes derived global maps from a locally finite-free sheaf via hypercohomology, not a constant-module scalar-dual comparison. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-fix-site-perfect-scalar-hom: that node is derived extension of scalar SHEAF internal Hom on a scheme pro-etale site; it neither starts with the ordinary scalar dual nor supplies its normalized ordinary sheaf comparison on arbitrary sites. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-pur-completed-line-complete: that node is derived completeness of a completed integral rank-one coefficient sheaf; it makes no scalar-dual evaluation or signed assembly assertion. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-descent vs lem-fix-ringed-site-perfect-duality-for-model: that node proves intrinsic derived duality in a supplied ringed-site model, without ordinary scalar duals, constant-module descent or an additive realization comparison. The new task constructs the normalized map and naturality for every scalar module, and asserts no invertibility or complex result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-sfb-split-perfect-dual-tor-window: that node starts with a sheaf complex and proves a Tor window; it gives no comparison from the constant sheaf of an ordinary scalar dual. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-sfb-ringed-site-perfect-duality: that node is intrinsic derived tensor-Hom duality for a sheaf-perfect object, without the ordinary scalar dual/sheafification comparison or a supplied additive functor. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-sfb-ringed-site-bounded-evaluation-assembly: that node assembles Tot(F tensor sheaf-dual(E)) into Hom(E,F), over one sheaf of rings; there is no ordinary scalar dual or change from scalar modules to sheaves. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-sfb-scalar-perfect-dual-realization: the parent combines finite-free realization, internal-Hom exactness, every K-injective comparison and the natural derived dual isomorphism; this task isolates a strict subargument with different input hypotheses. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-sfb-ringed-site-bounded-dual-components: that node computes coordinates of the dual and bidual of a sheaf complex; it provides no comparison under a scalar-to-sheaf functor. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-sfb-ringed-site-finite-retract-dual-exact: that node begins with T and its internal SHEAF dual; it proves biduality and exactness, not descent or identification of the constant ORDINARY scalar dual. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-sfb-ringed-site-strict-perfect-hom: that node gives intrinsic sheaf-complex bidual and tensor-Hom isomorphisms; it has no ordinary scalar dual and no comparison eta under T. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-weil-pbc-condensed-internal-hom-sections: that node identifies condensed sections of internal Hom with additive-group Hom, without scalar constant modules, normalized dual tensors or signed assembly. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-weil-pbc-condensed-finite-free-tensor-exact: that node asserts exactness of tensor with a locally finite-free condensed module; it does not construct any dual comparison. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-weil-pbc-derived-coyoneda-evaluation: that node computes global derived Hom by homology of an additive-group-valued derived functor; it has no internal scalar-dual sheaf comparison. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-weil-pbc-ringed-site-locally-free-derived-hom: that node computes derived global maps from a locally finite-free sheaf via hypercohomology, not a constant-module scalar-dual comparison. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-fix-site-perfect-scalar-hom: that node is derived extension of scalar SHEAF internal Hom on a scheme pro-etale site; it neither starts with the ordinary scalar dual nor supplies its normalized ordinary sheaf comparison on arbitrary sites. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-pur-completed-line-complete: that node is derived completeness of a completed integral rank-one coefficient sheaf; it makes no scalar-dual evaluation or signed assembly assertion. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-evaluation-inverse vs lem-fix-ringed-site-perfect-duality-for-model: that node proves intrinsic derived duality in a supplied ringed-site model, without ordinary scalar duals, constant-module descent or an additive realization comparison. The new task assumes a normalized map for one finite projective scalar module and gives the explicit inverse for every splitting, with no cochain or derived result.

lem-sfb-scalar-dual-signed-assembly vs lem-sfb-split-perfect-dual-tor-window: that node starts with a sheaf complex and proves a Tor window; it gives no comparison from the constant sheaf of an ordinary scalar dual. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-sfb-ringed-site-perfect-duality: that node is intrinsic derived tensor-Hom duality for a sheaf-perfect object, without the ordinary scalar dual/sheafification comparison or a supplied additive functor. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-sfb-ringed-site-bounded-evaluation-assembly: that node assembles Tot(F tensor sheaf-dual(E)) into Hom(E,F), over one sheaf of rings; there is no ordinary scalar dual or change from scalar modules to sheaves. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-sfb-scalar-perfect-dual-realization: the parent combines finite-free realization, internal-Hom exactness, every K-injective comparison and the natural derived dual isomorphism; this task isolates a strict subargument with different input hypotheses. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-sfb-ringed-site-bounded-dual-components: that node computes coordinates of the dual and bidual of a sheaf complex; it provides no comparison under a scalar-to-sheaf functor. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-sfb-ringed-site-finite-retract-dual-exact: that node begins with T and its internal SHEAF dual; it proves biduality and exactness, not descent or identification of the constant ORDINARY scalar dual. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-sfb-ringed-site-strict-perfect-hom: that node gives intrinsic sheaf-complex bidual and tensor-Hom isomorphisms; it has no ordinary scalar dual and no comparison eta under T. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-weil-pbc-condensed-internal-hom-sections: that node identifies condensed sections of internal Hom with additive-group Hom, without scalar constant modules, normalized dual tensors or signed assembly. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-weil-pbc-condensed-finite-free-tensor-exact: that node asserts exactness of tensor with a locally finite-free condensed module; it does not construct any dual comparison. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-weil-pbc-derived-coyoneda-evaluation: that node computes global derived Hom by homology of an additive-group-valued derived functor; it has no internal scalar-dual sheaf comparison. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-weil-pbc-ringed-site-locally-free-derived-hom: that node computes derived global maps from a locally finite-free sheaf via hypercohomology, not a constant-module scalar-dual comparison. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-fix-site-perfect-scalar-hom: that node is derived extension of scalar SHEAF internal Hom on a scheme pro-etale site; it neither starts with the ordinary scalar dual nor supplies its normalized ordinary sheaf comparison on arbitrary sites. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-pur-completed-line-complete: that node is derived completeness of a completed integral rank-one coefficient sheaf; it makes no scalar-dual evaluation or signed assembly assertion. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-signed-assembly vs lem-fix-ringed-site-perfect-duality-for-model: that node proves intrinsic derived duality in a supplied ringed-site model, without ordinary scalar duals, constant-module descent or an additive realization comparison. The new task assumes an arbitrary additive T and supplied natural eta, and assembles its signed chain map; it constructs no scalar evaluation or finite-projective inverse.

lem-sfb-scalar-dual-evaluation-descent vs lem-sp-scalar-extension-dual-evaluation: the existing node starts from a module SHEAF and its internal SHEAF dual; the new source is constant sheafification of an ordinary module dual. Their agreement is a comparison requiring construction, not an identification by definition.

lem-sfb-scalar-dual-evaluation-inverse vs lem-pc-finite-projective-internal-hom-evaluation: the existing source is B tensor internal SHEAF Hom(E,R), over one ring sheaf, while the new source is B tensor the constant sheaf of ordinary Hom_R(V,R); an additional constant-sheaf dual identification would be needed.

lem-sfb-scalar-dual-signed-assembly vs lem-sc-hom-complex-to-single: that node identifies a sheaf product Hom with the signed sheaf dual for one sheaf complex; it does not compare application of an arbitrary additive scalar-to-sheaf T to an ordinary module dual. Its presentation change is reused in the parent.

lem-sfb-scalar-dual-signed-assembly vs lem-sc-hom-complex-single-natural: that node concerns a sheaf in degree zero in the FIRST argument on a scheme and a varying second argument; this task concerns the dual with the coefficient in degree zero in the SECOND argument and an arbitrary scalar-module functor T.

lem-sfb-scalar-dual-signed-assembly vs new-g3-signed-sheaf-dual-coefficient-map: that node changes the coefficient morphism N->N' inside signed sheaf duality; this task changes ordinary scalar duals into sheaf duals under an additive functor, contravariant in the source complex.

lem-sfb-scalar-dual-evaluation-inverse vs lem-pc-ring-projective-internal-hom-exact: the existing node is exactness of ordinary projective Hom on a one-object bottom-topology site, not an inverse to the constant scalar-dual comparison on arbitrary sites.

lem-sfb-scalar-dual-evaluation-inverse vs def-weil-pbc-projective-module: the existing node defines projectivity and its splitting characterizations; the new task uses that definition to give the sheaf-dual inverse, and cites it in stmt_deps.

lem-sfb-scalar-dual-evaluation-inverse vs lem-weil-pbc-free-module-projective: the existing node proves ordinary free modules projective; the new task assumes finite projectivity and constructs the inverse after sheafification and scalar extension.

lem-sfb-scalar-dual-evaluation-inverse vs lem-weil-pbc-projective-direct-summand: the existing node proves stability of ordinary projectivity under retracts; it makes no sheaf scalar-dual comparison or inverse assertion.

lem-sfb-scalar-dual-evaluation-inverse vs lem-weil-pbc-projective-ext-criterion: the existing node characterizes projectivity by ordinary Ext vanishing; the new task uses neither Ext nor such a criterion, but computes a sheaf-dual inverse.

lem-sfb-scalar-dual-evaluation-inverse vs lem-weil-pbc-ses-projective-quotient-splits: the existing node gives ordinary splitting maps of a short exact sequence; it does not give the normalized evaluation inverse or its restriction compatibility.

lem-sfb-scalar-dual-evaluation-inverse vs lem-sfb-dvr-projective-complex-matrix-model: the existing node replaces a scalar complex over a DVR by a finite free matrix model; the new task has an arbitrary commutative ring, one module, and an internal sheaf-dual inverse.

## Allocation of the returned arguments

Old steps 1 and 5 become the finite-projective inverse task, including existence of splittings, both scalar dual-generator identities, both inverse computations, sheaf restriction and independence of splitting. Old step 4 becomes the all-module descent task, including balanced evaluation, extension through both sheafifications, uniqueness and naturality. Old step 6 becomes the signed-assembly task, including the scalar (-q,0) coordinate and its single-cochain inverse, the sign, cochain-map naturality, uniqueness and both reversed bounds. The existing Hom-to-single lemma carries its product-Hom presentation change. Old step 2 is already contained in the no-flatness finite-power/matrix clauses of the existing scalar-presentation extension node; the parent's elementary functorial splitting calculation applies that statement. Old step 3 is the existing finite-retract internal-Hom exactness statement. Old step 7 is the existing bounded-exact-term quasi-isomorphism statement followed by the derived internal-Hom definition, with arbitrary resolutions and functoriality kept in the parent. Thus no part of the old calculation has been dropped merely to reduce the character count.

The three new tasks are comparable: sheafification descent and naturality, finite-projective inverse descent, and the signed coordinate/cochain assembly. Each is a separate mathematical argument. Reusing the already existing finite-free, exactness and quasi-isomorphism tasks avoids recreating elementary or duplicate nodes. The old Lean implementation remarks in steps 2 and 6 are retained below as guidance for those tasks; they are not additional mathematical hypotheses.

## Returned seven-step proof, preserved verbatim

### Old step 1

For any finite projective scalar module $V$, finite generators give a surjection $p:R^N\to V$, and the projective lifting property lifts $1_V$ to $i:V\to R^N$, with $pi=1_V$. Put $v_j=p(e_j)$ and $\lambda_j=e_j^*i\in V^*=\operatorname{Hom}_R(V,R)$. Then $v=\sum_j\lambda_j(v)v_j$ and, by applying $\phi\in V^*$, $\phi=\sum_j\phi(v_j)\lambda_j$. For the terms of $F^\bullet$ use the supplied splittings. These identities also cover $V=0$ with $N=0$.

Uses: def-weil-finitely-generated-module, def-weil-pbc-projective-module, def-weil-pbc-strict-perfect-coefficient-package.

### Old step 2

Constant module sheafification and ordinary change of rings are additive functors: the sheafification adjunction gives additivity and identities/composition are checked before sheafification on pure tensors. Identify the constant scalar unit with the constant ring sheaf using the locally bijective coefficient unit. Tensor multiplication identifies its scalar extension with B. Additive functors preserve finite products, so the resulting unit comparison gives C_B(R^N) ≅ B^N, including N=0. Applying C_B to the supplied scalar maps i_r,p_r preserves their splitting relation and gives the required finite-free retract terms. The finite product is identified with the lifted-index finite free coproduct by the biproduct comparison and reindexing. No tensor-exactness assertion is used.

Uses: def-weil-pbc-strict-perfect-coefficient-package, def-pur-sheaf-tensor-product, def-weil-presheaf-modules-sheafification.

### Old step 3

Apply the finite-retract internal-dual lemma with coefficient sheaf $B$, $T=E^q$, and the splitting just constructed. Its exactness clause states that $\mathcal Hom_B(E^q,-)$ carries every short exact sequence of module sheaves to a short exact sequence. This is exactness of internal sheaf Hom, not exactness of global Hom or of sections.

Uses: lem-sfb-ringed-site-finite-retract-dual-exact.

### Old step 4

For a scalar $V$, the evaluation formula $\beta_V(b\otimes\phi)(b'\otimes v)=bb'\phi(v)$ is additive and balanced in both tensor expressions, is $B$-linear, and commutes with restriction. Finite-product preservation of sheafification extends the bilinear evaluation, so the tensor universal property gives a map into the sheaf Hom. Explicitly, first define evaluation on constant local sections and extend along the two sheafifications; the formula is unchanged after restriction. For $f:V\to W$, the two composites from $C_B(W^*)$ to $\mathcal Hom_B(C_B(V),B)$ both send $b\otimes\psi$ and $b'\otimes v$ to $bb'\psi(f(v))$. The uniqueness part of sheafification extends this equality to all sections. Thus $\beta$ is contravariantly natural in $V$.

Uses: def-pur-sheaf-tensor-product, def-weil-presheaf-modules-sheafification, def-pur-sheaf-hom, lem-weil-pbc-sheafification-sets-exact.

### Old step 5

Use the dual generators from step 1. On every localized site, for $h:C_B(V)|_U\to B|_U$, set $\gamma_V(h)=\sum_j h(1\otimes v_j)\otimes\lambda_j\in C_B(V^*)(U)$. The finite sum commutes with restriction, hence defines a sheaf morphism. On tensor generators,
$$\beta_V\gamma_V(h)(b'\otimes v)=b'\sum_jh(1\otimes v_j)\lambda_j(v)=h(b'\otimes v),$$
while
$$\gamma_V\beta_V(b\otimes\phi)=\sum_jb\phi(v_j)\otimes\lambda_j=b\otimes\phi.$$
The dual-generator identities and sheafification uniqueness make these identities hold on all sections. Therefore $\gamma_V$ is the inverse of $\beta_V$. The comparison is independent of the chosen splitting because its defining evaluation formula is; its inverse is then uniquely determined.

Uses: def-pur-sheaf-hom, def-pur-sheaf-tensor-product, def-weil-presheaf-modules-sheafification.

### Old step 6

In degree $q$, the only possibly nonzero factor of $\mathcal Hom_B^\bullet(E^\bullet,B[0])$ is $\mathcal Hom_B(E^{-q},B)$, and the Hom-complex differential is $h\mapsto-(-1)^q h\,d_E^{-q-1}$. Use $\beta_{F^{-q}}$ for its degree-$q$ comparison. Naturality from step 4 applied to $d_F^{-q-1}:F^{-q-1}\to F^{-q}$ gives, on generators,
$$d_{\mathcal Hom}\beta(b\otimes\phi)(b'\otimes v)=-(-1)^qbb'\phi(d_F^{-q-1}v)=\beta C_B(d_{F^\vee})(b\otimes\phi)(b'\otimes v).$$
Hence the degreewise isomorphisms form the claimed cochain isomorphism. They are natural in cochain maps by the same precomposition identity. If $F^r=0$ outside $[a,b]$, $F^{-q}=0$ outside $[-b,-a]$; $C_B(0)=0$ and the displayed unique-factor formula give the stated vanishing for both dual complexes, including the zero complex. In Lean, the scalar coordinate map is constructed from the (-q,0) cochain component, with inverse given by a single cochain; Mathlib's cochain differential formula verifies the sign. The evaluation naturality clause assembles the uniquely normalized signed comparison. The ordinary comparison uses the existing Hom-to-single isomorphism. Vanishing of Hom from a zero term follows from the zero identity and precomposition additivity.

Uses: def-pur-hom-complex, def-pur-sheaf-tensor-product.

### Old step 7

The complex $E^\bullet$ is bounded since its zero terms remain zero, and each term has exact internal Hom by step 3. Apply the bounded-exact-term Hom lemma to $P=E^\bullet$ and the quasi-isomorphism $B[0]\to I^\bullet$ of any K-injective resolution. Its hypotheses allow arbitrary unbounded source and target complexes of this map, so it gives precisely the asserted quasi-isomorphism of Hom complexes for every such resolution. By the definition of derived internal Hom the target represents $R\mathcal Hom_B(E^\bullet,B)$, with the canonical identification for any K-injective resolution. Composing its inverse in $D(B)$ with the cochain isomorphism of step 6 gives the required derived isomorphism. Taking the fixed functorial resolution makes the comparison natural; the definition's canonical independence of resolution identifies the other choices with it. All constructions used only finite splittings and internal-Hom exactness, so no flatness of $B$ over $\underline R$ was used.

Uses: lem-pc-bounded-exact-term-hom-quasi-iso, def-pur-derived-internal-hom.

## What remains

The three new statement-only nodes are deliberately unsplit for future workers. No mathematical part of this assigned re-split remains unfinished. Delivery-tool validation and push are the remaining operational checks, recorded after running them.
