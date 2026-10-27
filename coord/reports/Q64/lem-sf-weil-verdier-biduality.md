# Q64 repair: lem-sf-weil-verdier-biduality

2026-10-22. Direct stage-1 delivery; no Lean edits or compiler commands.

## Files written

- dag/nodes/sec-six-functors/lem-sf-weil-verdier-biduality.json: statement unchanged, five-step assembly, 2100 proof characters.
- dag/nodes/sec-six-functors/lem-sf-weil-dual-realization-comparison.json: statement, unsplit; the counit-normalized dualizing-object and internal-Hom realization comparison, with bounded constructible underlying output. No Mathlib match.
- dag/nodes/sec-six-functors/lem-sf-weil-bidual-evaluation-realization.json: statement, unsplit; construction of the native evaluation transpose and its equality with the realized geometric transpose, conditional on Hom preservation. No Mathlib match.
- citations.json: exact statement excerpts for each node cited by each parent proof step.
- searches.jsonl: retained actual msearch.py log. returned-proof.json and prior-report-Q10.md preserve the previous argument and report for repair review.

## Attachments

None. The exact project declaration AlgebraicGeometry.WeilComplex.nonempty_iso_verdierDual_rightOp_comp_verdierDual, lean/WeilConjectures/WeilSheaf/VerdierDual.lean:141, still has sorry at line 143. The preservation theorem in the same file also has sorry. Whole-project searches for the declaration, blueprint id, biduality and Hom found no finished declaration giving these comparisons.

## WANTED

None. Both current blueprint proof files cited below are present, as are the native Lean sources. The new statements are agent-formulated intermediate claims of the returned reviewed proof; they are not falsely attributed to a Stacks theorem or a theorem verbatim in a paper.

## Repair of the return

The return requires at least two new independent, comparably sized statement-only obligations, with every old argument retained and parent assembly at most 3000 characters. The sandbox initially contained only dispatcher marker files, so I copied the current reviewed item (the seven-step returned version) and the historical Q10 report from the read-only repository. No retained sandbox node/report/search was overwritten; this run's actual searches were retained across provider interruptions. The current item's statement, source and maintainer fields remain unchanged.

Returned steps 1-3 (1960 characters of argument) go into lem-sf-weil-dual-realization-comparison: realizing the underlying category, comparing the actual chosen exceptional dualizing object using its counit and the point unit, and applying both Hom comparisons to identify the underlying native dual with a bounded constructible common-stage dual. The new node states the concrete comparison, its evaluation normalization and naturality, not merely preservation of Weil complexes. The elementary cohomology detection part of old step 3 remains explicitly in parent step 2.

Returned steps 4-5 (1422 characters) go into lem-sf-weil-bidual-evaluation-realization: construct the ambient evaluation transpose, restrict to the full native category once preservation is known, and compare the actual double-dual morphism through the two Hom comparisons. Its statement introduces the transpose equation, the iterated comparison b_K and the equality b_K U(delta_K) j_K = rho(delta_M). It assumes the preservation established in parent step 2 and does not assert invertibility. Its proof can be worked on with this stated hypothesis independently of the proof of the first new node.

Returned step 6 remains parent step 4: geometric biduality is invertible, its realization is invertible, the actual-arrow equation makes the forgotten native map invertible, and conservativity reflects it. Returned step 7 remains as parent step 5, with its cross-reference updated to step 3: invert the naturality equation to obtain natural inverses and assemble the isomorphism. Thus neither new node restates either clause of the parent; neither gives native biduality. The first gives an underlying derived-object comparison; the second gives a morphism comparison without invertibility. The full old arguments appear below, unchanged, rather than being abbreviated or silently discarded.

Each new node has empty proof and proof_deps, null proof_origin and status unsplit. Their full statements have 4994 and 5445 characters, mostly shared self-contained native setup; the two distinct argument blocks have comparable scope. No parent step exceeds 2000 characters. The parent statement is byte-for-byte the current reviewed statement. The repair preserves the geometric coefficient-duality route and makes no chapter/unit change.

## Not duplicates

- lem-sf-weil-dual-realization-comparison vs lem-sf-weil-verdier-dual-preserves-weil-complexes: the existing node is now correctly native (its historical ambiguity has been repaired). It asserts only native Hom preservation and restriction; the new node asserts the normalized derived isomorphism to the common-stage dual, including its evaluation equation, h and c_K. I do not duplicate the preservation conclusion as the new lemma; the parent derives it from the comparison and exact forgetting.
- lem-sf-weil-dual-realization-comparison vs lem-sf-weil-native-exceptional-forgetful: the existing node compares exceptional functors and supplies h but says nothing about applying native internal Hom to arbitrary K or identifying that Hom's output with a common-stage dual. It is reused for its actual exceptional comparison.
- lem-sf-weil-dual-realization-comparison vs lem-sf-weil-native-closed-forgetful: the existing node compares native Hom with ordinary module Hom for arbitrary inputs; it has no chosen dualizing object or common-stage dual identification. It is reused for its stated native Hom comparison and conservativity.
- lem-sf-weil-dual-realization-comparison vs lem-sf-adic-qbar-constructible-realization: the existing node concerns ordinary geometric module objects and a common-stage equivalence, not native Frobenius-equivariant derived objects or their chosen exceptional dualizing object.
- lem-sf-weil-bidual-evaluation-realization vs lem-sf-evaluation-bidual-comparison-transport: the existing node assumes that F restricts to an equivalence on the chosen subcategories. Native forgetting U is conservative but is not such an equivalence. The new node compares a native transpose through forgetting AND geometric coefficient realization, including native extension morphisms, with the actual h and c_K. The general existing node can serve the rho part of a future proof; it does not give the whole new statement in one specialization.
- lem-sf-weil-bidual-evaluation-realization vs lem-sf-weil-native-closed-forgetful: the existing node constructs an ambient transpose and compares it with ordinary module duality; the new node restricts it to native constructibles and compares its actual arrow with common-stage geometric biduality, with dualizing-object transport and two successive Hom comparisons.
- lem-sf-weil-bidual-evaluation-realization vs thm-coef-qbar-verdier: the existing theorem is common-stage geometric duality; it gives no native equivariant derived morphism comparison. It is reused for geometric invertibility in parent step 4.
- Both new nodes vs lem-sf-weil-verdier-biduality: neither asserts the native biduality isomorphism; the two comparisons plus cohomology detection and reflection/assembly are required. This is not moving the whole parent into one new node.

I searched the whole DAG and imported blueprint by bidual, realization, native, transpose, forgetful, evaluation/transport and dual/realization, and read the above candidate statements, including the generic categorical transport lemma. None states either new claim. There are no Stacks tags in the new source fields: these are native refinements of the blueprint proof, and no new duplicate-by-tag is being hidden. Existing Stacks-based infrastructure stays in the existing nodes.

## Mathlib searches and results read

For each new id I ran a dedicated LeanFinder semantic query, a second natural-language phrasing in LeanSearch, Loogle and Mathlib grep via the required msearch.py command. The command's log has each exact tool/query; the node records those exact queries. All services used in these final records answered. The initial Loogle query with two unseparated strings produced a syntax error, so I did not treat it as absence evidence; the recorded replacement is the valid expComparison query. The interrupted semantic requests completed and logged their hit names before the provider error; I read those records and inspected their relevant source rather than repeating the same requests.

The first search returns underived LightCondensed.ihomPoints and coev_expComparison, not a native constructible Weil dual. The second returns FGModuleCatEvaluation and Module.Dual.eval_naturality, not a derived Hom comparison into a geometric dualizing object. I read Mathlib/Condensed/Light/InternallyProjective.lean:53-86, Algebra/Category/FGModuleCat/Basic.lean:210-236 and LinearAlgebra/Dual/Defs.lean:177-179. The common potential categorical hit expComparison and its evaluation/naturality lemmas were read in CategoryTheory/Monoidal/Closed/Functor.lean:43-44,85-132: they assume CartesianMonoidalCategory and concern product exponentials, so cannot specialize in one line to the derived tensor categories here. The two grep queries found no Weil/dualizing objects and only unrelated module, character and normed-space double-dual declarations. These are unsplit obligations, zero Mathlib leaves.

## What was wrong and what remains

The reviewed mathematical statement is retained. The return concerns proof granularity, repaired by the two new obligations and the short parent assembly. The older Q10 statement dispute (native derived equivariant sheaves versus Frobenius pairs after deriving) remains documented in the preserved prior report below; it is not a new statement change in this delivery. In particular no native forgetful equivalence, faithfulness on derived morphisms, Frobenius-stable integral lattice, smoothness assumption, or ambient unbounded exceptional adjoint is introduced.

The ancestor helper still prints None for this maintainer-created item because created.item is null. I follow that computed provenance for new from.node = null and keep the textual lem-a1-local-boundary-duality/thm-coef-qbar-verdier provenance explicit in from.place, with via = [lem-sf-weil-verdier-biduality], as the prior accepted new nodes did. Their blueprint same_as lists are empty after the whole-blueprint searches.

Nothing in the authorized one-level split remains unfinished; the two new statements deliberately remain unsplit for other workers. No agents were started, no repository or launcher files were changed, and no Lean/compiler/build commands were run.

## Review by Q64

I read the worker brief, stage-1 document, GOAL, the three-level rule in SETUP, the chapter and unit, and delivery-errors B-E in full. For both new nodes and the parent I read the current thm-coef-qbar-verdier.proof.md coefficient-descent/evaluation paragraphs and cor-coef-verdier-weil-equivariance.proof.md transposition/exceptional-adjunction paragraphs under main-20261015/sk-thm-sf-package. I read the current statements of lem-sf-weil-native-closed-forgetful, lem-sf-adic-qbar-constructible-realization, lem-sf-weil-native-exceptional-forgetful and thm-coef-qbar-verdier, and the candidate duplicates listed above. The native comparison obligations are explicit agent refinements already present in the old reviewed proof, not stronger claims falsely ascribed to the pair-level equivariance source.

In parent step 1 the first new node supplies exactly h, c_K, common-stage membership and bounded constructibility of the underlying Hom. Its finite-field, separated finite-type and chosen-right-adjoint hypotheses are exactly the parent's. In step 2 the cited closed-forgetful statement explicitly says U commutes with cohomology and is conservative. For an object A, if UA=0 then U(0 -> A) is invertible, hence 0 -> A is invertible; this justifies zero detection without an extra lemma. The range of vanishing and constructibility then give the native category's defining property. Restriction of a functor to a full subcategory preserves composition and identities directly, so no hidden restriction lemma is required.

In step 3 the second new node supplies precisely the natural native evaluation transpose and the actual-arrow equality, assuming only the preservation just proved and the comparison data from step 1. I checked the b_K direction: c_K goes from U D_X K to rho D_Y M_K, so rho D_Y must be applied contravariantly to the INVERSE of rho^{-1}c_K to take the double dual to rho D_Y D_Y M_K. The counit j_K goes rho M_K -> UK, and the equation therefore has domain rho M_K on both sides. This direction matters; an arbitrary isomorphism of the source and target would not compare the biduality maps. The source transpose equation is retained explicitly in the new statement.

In step 4 thm-coef-qbar-verdier explicitly states that evaluation and biduality descend to a natural isomorphism on common-stage constructibles. The first node guarantees the arguments of both common-stage Homs are in that domain; the second node compares the same transpose. The closed-forgetful statement supplies conservativity for the actual native derived category, not faithfulness on derived Hom sets. Step 5 is the original explicit inverse-naturality calculation: multiplying the naturality square by the two inverses proves that the componentwise inverse is natural, and the two componentwise identity equations yield a natural isomorphism. All cited information is copied verbatim from statements into citations.json; no construction hidden inside another node's proof is used.

I tested the new claims on K=0, shifted coefficient lines, the geometric point with trivial Frobenius, a unipotent Jordan-block Frobenius extension, and the empty scheme. On the point, forgetting can erase an extension morphism but still detects isomorphisms, so only conservativity is used. The shift symmetry stays the derived symmetry in the transpose equation and is not replaced by an unsigned evaluation. A rescaling of h is kept in BOTH Hom comparisons, which is why their iterated comparison b_K is specified rather than arbitrary. There is no use of the banned SGA route. The two new nodes neither assume native biduality nor depend on the parent, and the parent first proves the conditional hypothesis needed by the second. I checked the complete old proof allocation below against the new statements so no argument disappears during the re-split.

## Original seven arguments and their allocation (verbatim)

### Old step 1 -> lem-sf-weil-dual-realization-comparison (with cohomology reflection retained in parent step 2)

Put $Y=\bar X$ and let $\mathcal C_Y$ be the common-stage category. By [lem-sf-adic-qbar-constructible-realization] the ordinary bounded constructible module category is equivalent to $\mathcal C_Y$ via $\rho_Y$. By [lem-sf-weil-native-closed-forgetful], termwise forgetting induces the exact conservative functor $U:\mathrm{WC}(X)\to D^b_{\mathrm{cons}}(\mathcal A_Y)$. For a native $K$ write $M=\rho_Y^{-1}UK$. The separated finite-type hypothesis here is the same hypothesis in both comparison lemmas; $Y$ is the geometric fiber of the given separated finite-type $X/k_0$.

Citations: lem-sf-adic-qbar-constructible-realization, lem-sf-weil-native-closed-forgetful

### Old step 2 -> lem-sf-weil-dual-realization-comparison (with cohomology reflection retained in parent step 2)

Apply [lem-sf-weil-native-exceptional-forgetful] to the structure morphism $a_0$. Its right-adjoint hypothesis is exactly the assumed HasUpperShriek, and its point-unit comparison identifies the specified constant Weil sheaf with the coefficient unit. Thus obtain $h:U\omega_X\xrightarrow{\sim}\rho_Y\omega_Y$, where $\omega_Y=Ra_Y^!\Omega$ is the common-stage dualizing object. This comparison is for the chosen right adjoint and is normalized by its counit; it is not an inference that forgetting must preserve every right adjoint.

Citations: lem-sf-weil-native-exceptional-forgetful

### Old step 3 -> lem-sf-weil-dual-realization-comparison (with cohomology reflection retained in parent step 2)

For native $K$, write $H=R\mathcal Hom_{\mathcal B_Y}(K,\omega_X)$ in the ambient native derived category. The Hom comparison of [lem-sf-weil-native-closed-forgetful], $h$ from step 2, and the evaluation-normalized realization of [lem-sf-adic-qbar-constructible-realization] identify $UH$ with $\rho_YR\mathcal Hom(M,\omega_Y)=\rho_YD_YM$. By [thm-coef-qbar-verdier] this common-stage Hom is bounded constructible. Since $U$ commutes with cohomology and detects zero, its boundedness implies boundedness of $H$; constructibility of its underlying cohomology sheaves is precisely constructibility of the cohomology of $UH$, by the definition of the native category. Thus $H$ is a native Weil complex, which is clause 1. These natural Hom comparisons restrict the ambient contravariant functor to $D_X$ on native Weil complexes and apply again to $D_XK$.

Citations: lem-sf-weil-native-closed-forgetful, lem-sf-adic-qbar-constructible-realization, thm-coef-qbar-verdier

### Old step 4 -> lem-sf-weil-bidual-evaluation-realization

In the ambient native derived category [lem-sf-weil-native-closed-forgetful] defines the natural transpose of symmetric evaluation $\delta_K:K\to R\mathcal Hom_{\mathcal B_Y}(R\mathcal Hom_{\mathcal B_Y}(K,\omega_X),\omega_X)$. Step 3 puts both successive Homs in the native full constructible subcategory, so this is a morphism $K\to D_XD_XK$ there. Fullness of the inclusion retains its naturality on every native derived morphism, including extension morphisms.

Citations: lem-sf-weil-native-closed-forgetful

### Old step 5 -> lem-sf-weil-bidual-evaluation-realization

Using the evaluation and internal-Hom comparisons in [lem-sf-weil-native-closed-forgetful] and [lem-sf-adic-qbar-constructible-realization], and $h$ from step 2, identify $UD_XK$ with $\rho_YD_YM$ and $UD_XD_XK$ with $\rho_YD_YD_YM$. Here [thm-coef-qbar-verdier] gives $D_Y=R\mathcal Hom(-,\omega_Y)$ on $\mathcal C_Y$ and guarantees both common-stage Homs are in its domain. These comparisons identify $U\delta_K$ with $\rho_Y\delta_M$. Indeed $\delta_K$ is characterized by $\operatorname{ev}_{D_XK,\omega_X}\circ(\delta_K\otimes1_{D_XK})=\operatorname{ev}_{K,\omega_X}\circ\sigma_{K,D_XK}$. Each of $U$ and $\rho_Y$ carries the tensor product, the symmetry and the evaluation in this equation to the corresponding maps. After identifying $U\omega_X$ by $h$, the resulting equation is the defining equation of $\delta_M$; uniqueness of the tensor--Hom transpose gives the claimed equality. This compares the actual morphism, not just its source and target.

Citations: lem-sf-weil-native-closed-forgetful, lem-sf-adic-qbar-constructible-realization, thm-coef-qbar-verdier

### Old step 6 -> parent step 4

By [thm-coef-qbar-verdier], $\delta_M$ is an isomorphism. Hence its image $\rho_Y\delta_M$, and therefore $U\delta_K$, is invertible. The conservativity in [lem-sf-weil-native-closed-forgetful] makes $\delta_K$ invertible. This applies to every $K$ in the native category, including zero and shifted objects.

Citations: thm-coef-qbar-verdier, lem-sf-weil-native-closed-forgetful

### Old step 7 -> parent step 5

The natural maps of step 4 assemble to $\delta:\mathrm{id}\to D_XD_X$. Their componentwise inverses are natural: from $D_XD_X(u)\circ\delta_K=\delta_L\circ u$, multiply on the left by $\delta_L^{-1}$ and on the right by $\delta_K^{-1}$ to obtain $u\circ\delta_K^{-1}=\delta_L^{-1}\circ D_XD_X(u)$. These are the inverse natural transformation and its two inverse identities. Thus $\delta$ is the natural isomorphism of clause 2, or in Lean notation $\mathord{\mathbf1}_{\mathrm{WC}(X)}\cong (\mathrm{verdierDual}).\mathrm{rightOp}\mathbin{\ggg}\mathrm{verdierDual}$.

Citations: 

## Preserved prior report (Q10; historical, before the current repair)

# Stage-1 delivery: lem-sf-weil-verdier-biduality

Group Q10, 2026-10-22. Direct delivery; author's review below.

## Files written

- dag/nodes/sec-six-functors/lem-sf-weil-verdier-biduality.json: split into seven steps; intended native Lean biduality statement retained, with the category corrected and made explicit.
- dag/nodes/sec-six-functors/lem-sf-weil-native-closed-forgetful.json: statement, unsplit; native derived tensor/internal Hom and evaluation under forgetting Frobenius. No Mathlib match.
- dag/nodes/sec-six-functors/lem-sf-adic-qbar-constructible-realization.json: statement, unsplit; evaluation-compatible realization of common-stage coefficients in native ordinary adic modules. No Mathlib match.
- dag/nodes/sec-six-functors/lem-sf-weil-native-exceptional-forgetful.json: statement, unsplit; native Weil compact-support/exceptional adjunction comparison with ordinary geometric-fiber operations. No Mathlib match.
- citations.json: one verbatim statement excerpt for every cited node in each proof step.
- searches.jsonl: actual msearch.py searches, retained as generated. No searches from this run were fabricated or substituted for a failed service.

## Attachments

None. The item's exact declaration AlgebraicGeometry.WeilComplex.nonempty_iso_verdierDual_rightOp_comp_verdierDual is at lean/WeilConjectures/WeilSheaf/VerdierDual.lean:141 and its proof is sorry at line 143. Searches of the whole project WeilConjectures tree for the id and declaration, and of WeilSheaf for biduality and the comparisons, found no finished replacement. The generic and ordinary sheaf declarations inspected do not state the new native comparisons with all their clauses.

## WANTED

None. The current blueprint, Bhatt--Scholze, Hemo--Richarz--Scholbach, and the native Lean source used for the type audit are present. The native derived upgrades of the blueprint's equivariance assertion are formulated by the agent and remain explicitly unsplit obligations; they are not represented as quotations of a theorem in those PDFs.

## STATEMENT-DISPUTED: fixed pairs and a derived category are different

The seeded statement says WC(X) is the category of def-weil-weil-sheaf-complex and simultaneously says it is Lean's WeilComplex. These are different categories. That definition explicitly makes pairs (K, theta) in an ordinary derived category and warns that their morphisms are not derived Ext groups. In contrast, Category.lean:134-180 constructs IsoAlgebra on the abelian category of native adic sheaves and then takes the full bounded constructible subcategory of its derived category.

Explicit small-case witness: take X=Spec(k0) and the constant coefficient line with Frobenius 1. A two-dimensional Jordan block gives a nonsplit extension of the trivial Weil line by itself. It is a nonzero Ext^1 class, hence a nonzero map from that line to its shift in the native derived category. The corresponding Hom in the fixed-pair category is zero, since the underlying Hom from the coefficient line to its shift over the geometric point is zero. Thus the two categories cannot be silently identified by their objects or the proposed forgetful functor.

The correction keeps the intended native Lean conclusion and the same field, separatedness, finite-type and HasUpperShriek assumptions. It explicitly defines native Weil complexes as bounded complexes with constructible cohomology in the derived category of equivariant sheaves. No hypothesis is added. The native coefficient sheaf is locally finite-extension-valued continuous functions, as in ConstantSheaf.lean, not discrete Qbar and not the unrestricted continuous-function sheaf. No claim about the category of fixed pairs is weakened to obtain the result. The separate seeded preservation node has the same model ambiguity; this split proves native preservation through its comparisons instead of taking that ambiguous sentence as a black box.

The unit and chapter remain unchanged. The unit requires geometric biduality followed by coefficient passage; the split uses precisely the common-stage theorem thm-coef-qbar-verdier, with the comparisons needed to apply it to the native category. It does not use the forbidden trace route or any SGA source.

## Not duplicates

- lem-sf-weil-native-closed-forgetful vs def-weil-weil-sheaf-complex: the latter defines fixed pairs after deriving; the new lemma concerns deriving equivariant sheaves before forgetting and compares actual tensor/Hom evaluations on that derived category.
- lem-sf-weil-native-closed-forgetful vs lem-fix-weil-operations: the latter supplies Weil structures on coefficient-passage operations and their algebraic maps, not conservativity or the native K-injective internal-Hom comparison.
- lem-sf-weil-native-closed-forgetful vs cor-coef-verdier-weil-equivariance: the corollary proves equivariance for fixed pairs; it neither constructs the native derived tensor--Hom adjunction nor accounts for native extension morphisms.
- lem-sf-weil-native-closed-forgetful vs lem-weil-native-internal-hom-contravariant-exact: the latter proves exactness and shifts of a native Hom functor in a general abelian category, expressly excluding evaluation or a biduality map; the new lemma compares forgetting, tensor, Hom and evaluation, without proving geometric biduality.
- lem-sf-adic-qbar-constructible-realization vs prop-weil-pbc-qbar-condensed-two-colimit: that proposition compares finite condensed stages with the condensed closed stage; its statement expressly distinguishes these stages from raw rationalizations. The new lemma also identifies the sf raw rationalized/common-stage category and the actual native module presentation, with evaluation-normalized tensor and internal-Hom maps.
- lem-sf-adic-qbar-constructible-realization vs lem-fd-rational-coefficient-category-comparison: that lemma compares the two raw integral/rational/common-stage presentations and Frobenius pullbacks, not their ordinary native adic internal Homs and evaluations.
- lem-sf-adic-qbar-constructible-realization vs lem-per-continuous-rational-derived-realization: that lemma treats a finite coefficient field and pullbacks; it does not assert the closed-stage Hom/evaluation comparison.
- lem-sf-adic-qbar-constructible-realization vs lem-zl-rational-realization-tensor-comparison: that lemma is the finite-field tensor compatibility, not the algebraic-closure internal-Hom comparison on all constructible pairs.
- lem-sf-adic-qbar-constructible-realization vs lem-sfb-qlbar-internal-hom-coefficient-comparison: that lemma assumes an internal-sheaf continuity property for a fixed first variable. The new lemma supplies the constructible realization and its actual evaluation compatibility, rather than adding that continuity assumption to the item.
- lem-sf-weil-native-exceptional-forgetful vs cor-coef-verdier-weil-equivariance: the corollary lifts adjunctions to pairs in the ordinary derived category. The new lemma compares the actual right adjoint on the native derived category of equivariant sheaves, retaining the derived extension morphisms.
- lem-sf-weil-native-exceptional-forgetful vs lem-pur-compact-support-condensed-realization: that lemma expressly makes no assertion about right adjoints and does not derive the Weil category; the new lemma compares the chosen native Weil right adjoint and its counit as well as the left functor.
- lem-sf-weil-native-exceptional-forgetful vs lem-pur-condensed-exceptional-reconstruction: that lemma concerns reconstruction from a normalized integral tower with specified system comparisons; the new lemma concerns forgetting the Frobenius action on a native derived exceptional adjunction for arbitrary native constructible inputs.

The blueprint searches were run for biduality, Verdier biduality, derived Weil, coefficient realization, forgetful, closed forgetful, constructible realization, exceptional forgetful, native, finite coefficient-field, and exceptional adjunction. Whole-DAG searches also examined statements and source places (especially Bhatt--Scholze 6.8.14 and the Hemo--Richarz--Scholbach coefficient comparisons), and full project searches checked the native names. None is an exact existing statement of the new comparisons. The new nodes assert no invertibility of a geometric double-dual map and do not restate a clause of the item.

## What could not be finished

Nothing in the one-level split is left unfinished. The three new comparison lemmas deliberately remain statement-only stage-1 obligations. No Lean was written or compiled. The provenance helper reports no computed ancestor because the maintainer-created item's created.item is null; the original blueprint.from already names lem-a1-local-boundary-duality. The first dry run rejected the three new nodes when they inherited that supplied textual ancestor. Following the helper output and the preflight diagnostic, their from.node is now null (the computed ancestor), with from.place retaining the exact textual provenance and via retaining the parent item. The original item metadata is unchanged. This is a correction of the new-node provenance to the required computation; no tool or maintainer-owned metadata was altered.

## Review by Q10

I read delivery-errors B--E in full, the stage-1 brief, GOAL, the unit and chapter, and the three-level rule. For the item I read the current thm-coef-qbar-verdier statement and proof and cor-coef-verdier-weil-equivariance statement and proof. I compared them with VerdierDual.lean:62-143, Category.lean:134-180, DerivedHom.lean:107-113, Localization.lean's objectProperty_iff and forgetBoundedConstructibleAdic, and the coefficient construction in ConstantSheaf.lean and Module.lean. This exposed the category error above. I corrected that error instead of assuming the corollary on pairs gives native derived biduality.

For the new ordinary realization lemma I read Bhatt--Scholze Definition 6.8.8, Proposition 6.8.14 and Remark 6.8.15, and Hemo--Richarz--Scholbach Proposition 5.2 and Theorem 7.7, including the hypotheses qcqs/topologically Noetherian and the distinction between raw localization and completion. I also opened every comparison candidate listed above. The statement requires separated finite type over the algebraically closed finite field, so these finiteness hypotheses hold. Its Hom comparison is in the derived category and only claims the coefficient-passage Hom when that Hom is constructible. It retains evaluation, which is essential in step 5 and is not supplied merely by an abstract category equivalence.

For the new native forgetting lemma I used the internal-Hom/transposition paragraph of the current equivariance proof and checked the precise native K-injective Hom-complex implementation. Its scope is the formal equivariant module derived category; it chooses no dualizing object and claims no geometric reflexivity. The underlying reason a future split must implement is exact induction along the Frobenius automorphism (a sum of its integer iterates): it permits forgetting K-injective resolutions, and forgetting creates the products used in the Hom complex. This is a genuine derived comparison obligation, not a consequence of the definition of fixed pairs.

For the new exceptional comparison I checked the same source's exceptional-adjunction assertion against the actual native HasUpperShriek and chosen right-adjoint definition. The source only gives the pair-level assertion; I explicitly marked the native extension as an agent-formulated comparison obligation, rather than asserting it follows by forgetting an arbitrary adjunction. Its statement is about native equivariant derived operations, without an unbounded ambient exceptional adjoint hypothesis. A future proof must construct/compare the derived equivariant lift and its adjunction, retaining the counit. This is independent of biduality, so the split is not circular.

Step 1 uses the two new realization/forgetting statements exactly for the equivalence and the conservative functor. Step 2 uses the new exceptional comparison's explicit structure-map and point-unit clause for the same chosen adjoint as the item. Step 3 uses the stated Hom comparisons and thm-coef-qbar-verdier's internal-Hom identification and constructible anti-equivalence. Exactness, cohomology commutation and conservativity then reflect bounded constructibility by the native definition; this avoids assuming the separately seeded preservation lemma's ambiguous model identification. Step 4 uses the new native closed statement's actual evaluation transpose, already natural on derived extension morphisms. Step 5 uses the evaluation/symmetry clauses of both comparison nodes and the common-stage internal-Hom/biduality statement. I wrote the transpose equation explicitly; there is no unsupported claim that equal source and target objects imply equal comparison morphisms. Step 6 uses only the common-stage natural biduality isomorphism and conservativity. Step 7 is elementary: naturality of the componentwise inverse follows by multiplying the naturality equation by the two inverses. For every citation I extracted an actual contiguous statement excerpt into citations.json; no proof-only construction is used as if it were a statement.

I checked the point, zero object, arbitrary shifts, and the Jordan-block extension. The native functor may kill a nonzero extension morphism, so the proof uses conservativity, not faithfulness on derived morphisms. Identity structure maps give the expected coefficient-line case. Empty schemes give the zero category. None of the new comparisons assumes a Frobenius-stable integral lattice, smoothness, or perfection of a constructible sheaf on the entire site. The distinctions in the Not duplicates section are substantive: the new statements retain morphism/evaluation and native derived information absent from the existing statements. Each new node has an empty proof and proof_deps; every search recorded in it was actually run with msearch.py and its hits were read. No proof step exceeds 2000 characters. All statement and proof objects have their hypotheses introduced explicitly, and all comparison maps are derived isomorphisms rather than per-cohomology claims.
