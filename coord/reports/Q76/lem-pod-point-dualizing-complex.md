# Stage-1 worker report: lem-pod-point-dualizing-complex

## Files written

- dag/nodes/sec-six-functors/lem-pod-point-dualizing-complex.json: existing statement node split in six steps; Mathlib no match. Explicitly types the point-fibre comparison.
- citations.json: 32 verbatim statement quotes, one for each proof citation.
- report.md: source review and statement-dispute record.

No new nodes; no Mathlib leaves. Searches are preserved in searches.jsonl.

## Attachments

None. The candidate AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual in WeilConjectures/SixFunctors/Etale/Derived/Point.lean:157 has sorry, and states only the finite evaluated comparison.

## WANTED

None needed for the present split; all prerequisites are existing DAG statements.

## What was wrong or incomplete

The imported one-paragraph proof suppressed the identity compact-support normalization and the actual point internal-Hom comparison. The earlier expanded sandbox had left the canonical integral reconstruction-unit inference and integral internal-Hom constructibility too implicit. Both arguments are now explicit. The source also suppressed a fibre functor between sheaf and module categories; its typing correction is recorded below. The unused geometric-hypotheses statement dependency is removed. All imported blueprint provenance fields remain.

## What could not be finished

Nothing mathematical remains in this one-level split. It is left for the fresh second reader to review and deliver; no push is performed here.

## Statement corrected (STATEMENT-DISPUTED)

The source writes a sheaf complex `R mathcal Hom_s(C,omega_s)` and a module complex `R Hom_Lambda(C,Lambda)` in one isomorphism. Read literally with the current DAG definitions, their types differ: already for C=Lambda_s, the left side lies in D(s_proet,Lambda), while the right side requires a Lambda-module complex as input and lies in D(Lambda). Moreover s_proet is not a one-object ringed site. The source's intended identification is explicitly via the point fibre functor, as also confirmed by slopmaster2 Point.lean's docstring. The repaired statement writes c=Fib_s(C) and Fib_s(D_sC)=RHom_Lambda(c,Lambda), retains the identity exceptional inverse image and all four coefficient stages, and specifies ambient evaluation for the internal-Hom value. This is a typing clarification, with no perfectness hypothesis added and no conclusion removed.

The only direct DAG citer is `thm-pod-global-verdier-duality`. Its current Step 2 already applies Fib_s and takes precisely this evaluated derived-dual formula, so the repaired statement supplies that premise unchanged. No citer was edited.

Original statement (verbatim):

In the Poincare duality conventions of this chapter (the fixed setting),
the exceptional inverse image of the identity is the identity functor,

$$
\omega_{s,\Lambda}=Ra_s^!\Lambda\cong\Lambda_s,
$$

and, for every object $C$ of the
category at the point,

$$
D_sC:=R\mathcal Hom_s\bigl(C,\omega_{s,\Lambda}\bigr)\cong C^\vee.
$$



## Review by Q76

The sandbox contains one modified existing node, citations.json, and this report; there are zero new nodes and zero Mathlib leaves. No attachment was found: slopmaster2 SixFunctors/Etale/Derived/Point.lean:145-165 has the finite-coefficient evaluated duality theorem, but its body is sorry. Its scope also omits the exceptional identity and the other three coefficient stages. The item remains a genuine split. WANTED: none for this split; the existing DVR node records its own unavailable Serre reference and supplies that result as a cited statement.

I reopened the master item statement, the main-20261015 proof, the chapter and package unit, and the current statements of all cited nodes. I read Stacks sites-modules Tags 03EI and 093M at their labels, sites-cohomology Tags 0A94 and 08JA, Algebra 00LP, More on Algebra 0AUW and 066U, and Bhatt–Scholze pp. 58–61 (Definition 6.8.1, Lemma 6.8.2, and the coefficient-category descriptions). Those sources justify the ringed-site Hom calculation and coefficient models; no forbidden SGA route is used.

For step 1 I checked the compactification formula in def-compact-support-direct-image-detailed and the strict integral limit/rational/common-stage formulas in def-weil-integral-rational-qbar-compact-support. With both arrows the identity their finite functors are identity. The exceptional definition supplies the actual constructible adjunction, for bounded constructible inputs, without an ambient adjoint hypothesis. The derived-completeness definition deliberately does not choose a natural isomorphism. Consequently I strengthened the inherited argument: lem-coef-derived-system-evaluation-calculus supplies a natural adjunction unit; lem-coef-normalized-dvr-effectivity supplies the invertible counit on normalized systems. The triangle identity proves the unit invertible on the limit-image objects, and naturality transfers this to a complete C through any completeness isomorphism C ≅ LRC. This is an argument about the canonical unit, not a choice of a cone map. The final Yoneda comparison is the two natural representing Hom bijections, so it gives the identity exceptional functor and its value on the unit.

For step 2, the cited exact-sheafification statement explicitly says sheafification preserves exact sequences; applying it to constant presheaves gives exact constant modules. The completed-coefficient statement explicitly says flat over the constant ring and gives all finite quotients. The point-sections lemma supplies exact sections even for ambient sheaves. The continuous coefficient statement gives B(s)=O_E; exactness and its finite-quotient sequence give A_n(s)=A_n. The DVR statement supplies Noetherianity before the flat-completion theorem is applied. The extension/sections adjunction is proved by the two inverse section formulas in the step. No claim that the entire pro-etale site is a one-object site is used.

For step 3 I checked the finite-presentation node for a finite module over a Noetherian ring, the stalk node and finite-constructibility definition for constant finite cohomology, and the free-resolution node for a finite free cover with finitely generated kernel. The DVR torsion-free theorem applies to that kernel, which embeds in a finite free module; perfect-cohomology assembly then gives the bounded integral projective model. The integral stratified-perfect test applies since s is Noetherian, dimension zero, and ell is invertible. The fibre definition gives bounded finitely generated sections, and the fibre equivalence gives conservativity on precisely the two constructible objects in the counit. The triangle equation shows the sections of the actual counit are invertible. These are the statements quoted in citations.json, not results taken from their proofs.

For steps 4 and 5, def-pur-kinjective-complex supplies the null-homotopy definition; exactness of L_R and its explicit adjunction prove that sections of I are K-injective. Exact sections identify its resolution target with R. The internal-Hom definition and Hom-complex definition give each product and its signed differential; the termwise adjunction identifies those complexes. I added an omitted domain check at the end of step 5: for integral P bounded finite projective, sheaf Hom from each L_R P^i is exact, and a finite filtration shows Hom from L_R P preserves quasi-isomorphisms of its second input. Thus the integral internal Hom is represented by L_R Hom(P,R), and the cited integral stratified-perfect criterion makes it constructible. Its rationalization in step 6 is therefore defined. This uses no perfectness of a finite A_n complex. Step 4 is elementary with its complete null-homotopy calculation; step 5 is marked non-elementary because it now also invokes the integral constructibility criterion.

For step 6 I checked the exact rational/common-stage definitions, lem-pc-base-change-rhom-perfect with its first input perfect over O_E, the specified point-sections scalar comparisons, and the internal-Hom scalar comparisons including their identity and tower equations. The finite-projective formula identifies the resulting arrow after every scalar extension. The explicit formula on a three-field chain checks its composition equation. Naturality in localized arrows follows from precomposition and scalar multiplication on both sides. An integral torsion representative becomes zero after rationalization on both sides, as required.

B1–B7: there are no new nodes to be self-contained or to contain hidden proofs. Searches were rerun with the required msearch command and recorded exactly; the earlier entries are present in the inherited searches.jsonl as well. The generic rightAdjointUniq result at Mathlib/CategoryTheory/Adjunction/Unique.lean:102 does not make this item a Mathlib leaf: it supplies only a general categorical tool, not the concrete compact-support normalization or coefficient dual comparison. I read the actual search hits, including the ordinary module dual and condensed/sheaf Hom descriptions, none of which states the item. A second semantic phrasing also produced only ordinary sheaf pullback tools. Searches across the DAG/whole blueprint found lem-sf-point, a broader axiomatized package under def-sf-datum, not an interchangeable concrete proof prerequisite. No duplicate or clause-restatement helper node was created.

C1–C4: every non-elementary external input is a cited existing statement. The two previously suppressed arguments (canonical integral unit and integral Hom constructibility) are now written out, with their existing prerequisites. The 32 citation entries were checked as literal substrings of the current node statements, one for every step/use pair. The off-unit generic tools are declared in split_report.tool_uses with their purposes; none replaces the identity-adjoint/coefficient-dual route of this item. D1–D5: no part of the conclusion was renamed as a fresh premise; the argument is in the six proof steps. E1–E6: finite coefficients use K-injectives even at n>1; only the integral DVR step uses length-one free resolutions. Tested C=0, C=the unit, C=O_E/(varpi), and the residue module over A_{E,2}; no perfectness or properness assumption is silently added. The explicit typing correction is documented under STATEMENT-DISPUTED above and is compatible with the sole direct citer, thm-pod-global-verdier-duality.

The earlier sandbox passed a fresh server dry run at 1c0c8edf48. After these two mathematical clarifications and refreshing searches/citations, the final sandbox is submitted to the required dry run again. No Lean, compiler, Lake, live-project edit, push, or sub-agent was used.

## Second reading by Q76

- Step 1: checked the first sentence of the main-20261015 proof against the compactification definition, the integral/rational/common-stage compact-support definition, the actual reduction/limit adjunction unit and normalized-effectivity statements, and the constructible exceptional-adjoint statement; PASS after spelling out scalar compatibility of the canonical completion map on its product and shifted-product components. The Yoneda calculation uses both natural variables and gives inverse maps.
- Step 2: checked every hypothesis of the five cited statements and Stacks 03EI (`lemma-sheafification-exact`) and 093M (`lemma-completion-flat`) in sites-modules.tex; PASS. The DVR supplies Noetherianity, flatness preserves the injective uniformizer map, and exact sections identify the finite quotient with its coefficient ring. The two displayed section formulas prove the adjunction used later.
- Step 3: checked all nine cited statements, Stacks 00LP (`lemma-resolution-by-finite-free`), 0AUW (`lemma-dedekind-torsion-free-flat`, clause 3), 066U (`lemma-cohomology-perfect`), and Bhatt–Scholze Proposition 6.8.11; PASS. The finite case uses constant finite cohomology, while only the integral DVR case uses finite projective resolutions. Both objects of the counit lie in the domain of the cited conservative equivalence.
- Step 4: checked the two definition statements and the K-injective calculation against the construction around Stacks 0A94 (`lemma-RHom-into-K-injective`); PASS as elementary. Exact extension carries an acyclic module complex to an acyclic sheaf complex, and the explicit adjunction carries its null homotopy back termwise; exact sections preserve the resolution map.
- Step 5: checked all four cited statements and the sheaf-Hom complex construction surrounding Stacks 0A94; PASS. Products are sectionwise, the termwise adjunction preserves the signed differential, and the finite filtration of the integral model establishes constructibility before rationalization. There is no perfectness assumption on a finite-coefficient input.
- Step 6: checked all six cited statements, including the canonical completed-scalar comparison and the definition of the fibre scalar map; PASS after identifying the actual scalar-Hom arrow by transposing evaluation on finite free terms and restricting to projective summands. The two maps on a three-field chain have the same pure-tensor formula, so the common-stage naturality square is justified.
- New nodes: none; checked the sandbox inventory against the shared DAG. B1–B7 and removal of elementary, duplicate, clause-restatement or Mathlib helper nodes introduce no further work; the additional input is the existing `lem-weil-finite-free-completed-scalar-comparison`.

The statement was checked against both the current blueprint statement and its two-sentence proof, with the chapter and package unit open. The existing STATEMENT-DISPUTED typing repair is necessary: a sheaf complex and a module complex occupy different derived categories, already on the unit. Explicit ambient evaluation retains the original universal quantifier over the point category and every coefficient stage. The direct citer `thm-pod-global-verdier-duality`, step 2, uses exactly that evaluated formula. No target or other existing statement was changed.

Small cases checked: the zero input gives zero dual at every stage; the unit gives the coefficient ring in degree zero; at n=1 the field case is ordinary finite-dimensional duality; at n=2 the residue module need not be perfect over A_{E,2}, but steps 4–5 still compute its derived dual using a K-injective target. For the integral residue module the two-term resolution has dual cohomology in degree 1, rather than degree 0; rationalizing this torsion model gives zero on both sides. The empty scheme is not an instance of s=Spec(k), and n=0 is excluded by the fixed n≥1 convention. No properness hypothesis is used for an arbitrary X in this point calculation.

Independent Mathlib searches were run through msearch.py with the new semantic query “global sections derived sheaf Hom exact constant sheaf left adjoint coefficient ring geometric point” and a grep for `rightAdjointUniq|sheafHom.*[sS]ection|[sS]ection.*sheafHom`. The actual results are appended to searches.jsonl and mathlib_searches. I read Mathlib/CategoryTheory/Sites/GlobalSections.lean:69–76 and Sites/SheafHom.lean:250–254: these give ordinary adjunction/sections facts, not the derived coefficient comparison at four stages. The existing generic right-adjoint uniqueness hit likewise does not state this item. Point.lean:157–165 in slopmaster2 still ends in `sorry`; no finished declaration can be attached. `lem-sf-point` in the DAG uses an axiomatized six-functor datum and cannot replace this concrete argument.

Changes made: (1) refreshed the stale `def-pod-conventions` citation, whose current statement includes the corrected lecture-notes orientation; (2) expanded step 1's common-stage descent into the explicit completion-map square, instead of asserting that a stage representative remains itself; (3) expanded step 6's identification of the internal-Hom scalar comparison, so it does not rely merely on existence and coherence of abstract isomorphisms; (4) cited the existing completed-scalar comparison in both steps and recorded its generic tool purpose for the maintainer; (5) refreshed the complete citation list and added the independent search records. There are now 34 citation pairs, with one verbatim current statement per pair, zero new nodes and zero Mathlib leaves. Earlier report counts describe the inherited version. All other correct statements and proof steps were retained. No forbidden SGA source, Lean edit, compiler, Lake, local preflight, shared-repository write, direct git command or sub-agent was used.
