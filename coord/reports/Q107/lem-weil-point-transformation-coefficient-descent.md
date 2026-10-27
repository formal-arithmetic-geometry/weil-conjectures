# Worker report: Q107 repair of lem-weil-point-transformation-coefficient-descent

## Files written

- `dag/nodes/sec-six-functors/lem-weil-point-transformation-coefficient-descent.json`: existing statement, unchanged; replace its seven-step 6150-character proof by a three-step 1452-character assembly.
- `dag/nodes/sec-six-functors/lem-weil-point-transformation-rational-normalization.json`: new statement, unsplit; no Mathlib match. Obligation: old steps 1-3.
- `dag/nodes/sec-six-functors/lem-weil-point-composite-comparison-tower.json`: new statement, unsplit; no Mathlib match. Obligation: old steps 4-5.
- `dag/nodes/sec-six-functors/lem-weil-point-rational-family-common-stage-naturality.json`: new statement, unsplit; no Mathlib match. Obligation: old steps 6-7.
- `citations.json`: one verbatim statement quotation for each of the three cited nodes.

The sandbox initially held only dispatcher marker files, no node files, report or search log. I copied the live node as `repair-baseline.json` before editing; it is the returned seven-step proof, with the stage-2 Lean record now present. Thus there was no previous sandbox split to dry-run or earlier search result to discard. I kept all existing metadata, the statement, source, citations in the retained argument, blueprint provenance, and Lean records. No repository, launcher, Lean or unit/chapter file was written. No compiler or Lake command ran.

## Attachments

None. The blueprint tag and concept searches in `lean/WeilConjectures/` found no exact completed declaration. The current declaration `WeilConjectures.PointTransformationDescent.coefficient_descent`, in `lean/Sheaf/Paper/PointTransformationCoefficientDescent.lean:433`, still ends in `sorry`. It therefore cannot close this item. The source-library `AlgebraicGeometry.Etale.DerivedCategory.rationalization_transport` is a generic transport theorem for integral derived functors; it does not assert this normalized sections/pullback coefficient equation or its common-stage representatives.

## WANTED

None. I read the available Deligne PDF with `pdftotext`, printed pages 150-151 (PDF pages 15-16), especially (1.1.3) and (1.1.7). The source supplies rational Hom tensors and the coefficient-field colimit, and the point-transport context. It does not assert the completed pro-etale comparison formulas. Those remain explicitly attributed to the agent-written argument, as in the returned node.

## Return repaired

The return asked to spread all of the 6150-character proof across at least two comparable new statement-only nodes and keep the parent's assembly below 3000 characters. There are three new nodes, with self-contained statements of 3239, 3206 and 3197 characters; all have status `unsplit`, no proof steps, empty proof dependencies and null proof origin. The first handles integral-to-rational normalization, the second comparison coherence without any transformation family, and the third descent of a supplied rational family without requiring an integral lift. None restates the full item, and none depends on the parent or a sibling: all three can be worked on independently. The old arguments are retained verbatim below, assigned to the appropriate new obligation. They are not replaced by shorter sketches.

No STATEMENT-DISPUTED issue was found. The parent statement is byte-for-byte the same JSON string as the baseline. The inherited unit is `sk-prop-sf-rf-shriek-preservation`; the actual blueprint ancestry is the first cohomology-transport arrow in `def-weil-global-geometric-frobenius`, through the recorded point-transport chain. I read its main-20261015 blueprint file and the chapter/unit records and preserved this route rather than editing the inherited chapter/unit assignment.

## Searches

I searched the whole DAG by concept and title, the whole blueprint using `tools/blueprint_refs.py search` with `rational natural`, `common stage`, `scalar comparison`, `morphism tensors`, `natural transformations` and `tower cocycle`, and obtained the ancestor with `blueprint_refs.py ancestor`. Each new node has `is: null`, the inherited ancestor, a precise `from.place`, and the parent prepended to the `via` list. No exact blueprint duplicate was found.

Every new node has the exact queries actually run through the required `msearch.py` command: LeanFinder twice with different phrasing, Loogle, grep, and LeanSearch. The generated `searches.jsonl` is retained. LeanSearch returned its explicit HTTP rate-limit message and is recorded as `unavailable`, not as absence. Loogle's two rejected identifiers are recorded with the actual unknown-identifier diagnostic. Successful LeanFinder and grep searches supply the search evidence independently of that diagnostic.

I inspected the strongest candidates: `CategoryTheory.Localization.Construction.natTransExtension` at `Mathlib/CategoryTheory/Localization/Construction.lean:269` concerns the constructed ordinary localization, and does not state the normalized raw tensor/point-comparison equation; `PresheafOfModules.pullback_assoc` at `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean:142` is an underived presheaf pullback associativity theorem; `Module.DirectLimit.map_comp` at `Mathlib/Algebra/Colimit/Module.lean:196` concerns maps between module direct limits. They can be tools below the new nodes but are not one-line specializations proving these statements. Other semantic hits were scheme normalization, ordinary free-module pullbacks, residue-field evaluation, tensor congruence and directed-system map composition, none with the required objects or conclusions.

## Not duplicates

lem-weil-point-transformation-rational-normalization vs lem-weil-point-transformation-coefficient-descent: only rationalizes a supplied integral family and its scalar equation; it asserts no common-stage action, tower formula for the composite, or descended transformation.
lem-weil-point-composite-comparison-tower vs lem-weil-point-transformation-coefficient-descent: comparison coherence and the identification of the two actual common-stage functors; it takes no transformation family and asserts no rationalization or descended transformation.
lem-weil-point-rational-family-common-stage-naturality vs lem-weil-point-transformation-coefficient-descent: takes already natural rational maps and coherent comparison actions as inputs, with no integral transformation or integral lift; it proves the same-field equation and descent only.
lem-weil-point-transformation-rational-normalization vs lem-sf-completed-tensor-rational-naturality: that node treats an invertible binary tensor comparison under a reflective completion and an equivalence; ours treats arbitrary, possibly zero, point-section transformation components with the specified coefficient square.
lem-weil-point-transformation-rational-normalization vs lem-weil-pbc-realization-pull-rational-descent: that node concerns normalized pullback realization arrows, units and compositors; ours concerns arbitrary point-section transformations and their sections-comparison square.
lem-weil-point-transformation-rational-normalization vs lem-weil-point-rational-sections-hom: that node is a Hom isomorphism assuming a fibre equivalence; ours assumes no fibre equivalence and establishes naturality plus the normalized scalar equation.
lem-weil-point-transformation-rational-normalization vs lem-weil-point-automorphism-transport-scalar-extension: that node constructs the scalar equation for canonical restriction transport and explicitly asserts no naturality; ours assumes an arbitrary natural integral family and obtains all rational morphism naturality.
lem-weil-point-composite-comparison-tower vs lem-weil-point-sections-scalar-extension: that node supplies phi, not the composite b built using inverse alpha or the pullback-composite common-stage action.
lem-weil-point-composite-comparison-tower vs lem-pur-integral-operations-scalar-extension: that node supplies alpha, not the sections-composite b or its actual common-stage realization.
lem-weil-point-composite-comparison-tower vs lem-fd-local-frobenius-coefficient-extension: that node involves a geometric point of a finite-type scheme, iterated Weil structures and a fixed finite extension; ours has no Weil structures and proves the three-field tower and common-stage realization.
lem-weil-point-composite-comparison-tower vs lem-fd-common-stage-comparison-descent: that node compares two different coefficient frameworks by equivalences J; ours compares sections before/after one pullback inside the prescribed single framework, without an equivalence input.
lem-weil-point-rational-family-common-stage-naturality vs prop-weil-pbc-descent-functors: that node is stated for exact functors between PBC coefficient categories of schemes and their PBC common-stage categories; ours has target the literal pair category of ordinary point complexes and asserts the equation in D(L) at the original representative field with the specified b and phi, not just a descended equality.
lem-weil-point-rational-family-common-stage-naturality vs lem-pur-common-stage-smooth-operation-identification: that node concerns smooth f, f-star(d)[2d], f-shriek and the PBC source and target; ours concerns arbitrary automorphisms of the geometric point and point-complex-valued transformations, including noninvertible ones.
lem-weil-point-rational-family-common-stage-naturality vs lem-fd-common-stage-comparison-descent: that node descends equivalences between frameworks and pullback comparison isomorphisms; ours requires neither framework equivalences nor invertible transformation components and pins the same-field equality in D(L).
All three new nodes vs lem-sf-point-field-tensor-descent: that conditional result constructs point tensor/unit comparison packages, not arbitrary sections-to-pullback transformations or the displayed b composite and same-field naturality.

No new node cites a Stacks tag: these are explicit formal coefficient-comparison arguments, and I have not attached an unrelated tag merely to provide a source. The nearby Deligne references describe the context, not a theorem asserted to prove the new obligations.

## Review by Q107

I read the returned item, every original proof dependency's statement, the live Lean theorem and its predicates, the ancestor blueprint text, the inherited chapter/unit records, and Deligne (1.1.3), (1.1.7). For each new node I used the same source pages and the exact original steps assigned below, keeping the explicit warning that the normalized completed-coefficient argument is agent-written. The two scalar-comparison lemmas were opened: the sections lemma really supplies natural phi with the identity, three-field associator equation and its rationalization; the operations lemma really supplies alpha in the direction scalar-extension of pullback to pullback of scalar-extension, naturally, with units and successive-extension compatibility. The point-fibre and pullback definitions supply the actual rational morphism maps and actual common-stage conjugations. The two common-stage definitions supply equality after some further common finite extension, without requiring injective transition maps. I did not take a claim from any cited proof instead of its statement.

Assembly step 1 cites lem-weil-point-transformation-rational-normalization. Its statement explicitly concludes t equals eta tensor E, naturality for every finite tensor sum and balanced class, and the normalized b t = (t tensor L) phi equation. All of its integral-family hypotheses occur in the unchanged parent. The fields are finite inside the one fixed closure; the geometric point has characteristic p, so ell is invertible, and the automorphism preserves the constructible integral domain. The original domain argument and the precise pure-tensor formulas are assigned to this node, not silently dropped.

Assembly step 2 cites lem-weil-point-composite-comparison-tower. Its statement supplies exactly the b defined in the parent, naturality, identity and the full associator-corrected tower equality, then A and B as the actions of the already specified two common-stage functors. It also states the comparison with the prescribed pullback representative and invariance under extension and equivalent representatives. It requires no eta and therefore cannot be a renamed copy of the parent. The original naturality interchange at alpha-inverse, identity/composition cancellation and transition argument are all retained as its assigned argument below.

Assembly step 3 cites lem-weil-point-rational-family-common-stage-naturality. Its finite-stage naturality and normalized square are the outputs of step 1; its coherence and actual representative-action assumptions are the outputs of step 2. Its conclusion is explicitly in D(L) for the original L, then persists at N and agrees for equivalent representatives, and its component is the finite-stage class t. This is exactly what step 3 takes from it. The verbatim quotes in citations.json were checked against these three statement strings. I also checked the longer output statements directly, rather than treating the short citation quotations as substitutes for the required clauses.

For edge cases I substituted E=L and repeated fields in towers, g=id, eta=0, zero objects, torsion integral objects whose rational images vanish, zero and summed rational arrows, and source/target coefficient fields that differ. The first node uses linearity, not injectivity of integral-to-rational Hom maps. The second uses inverse alpha and then phi in the type-correct order. The third requires neither inverse t nor injective coefficient transitions; for equivalent representatives the equations agree only after passing to a common N, exactly as the source and target definitions permit. All three new statements explicitly accommodate these cases. No statement was weakened, and no canonical formula was imposed on the arbitrary supplied components.

I checked B1-B9: new nodes are self-contained statements only, with named definitions, TeX, correct source attribution, actual logged searches and complete blueprint ancestry; none is a spurious Mathlib leaf. I checked C1-C8: every assembly's non-elementary input is a cited new statement, all quotes occur verbatim, dependencies are acyclic and proof_deps is exactly the union of uses. The two old off-unit scalar tools are now statement dependencies of the unsplit obligations; no new off-unit proof citation or route change was introduced. I checked D1-D5 by separating the rationalization, coherence and rational-family descent inputs: no single new node can prove the whole item, and each carries a distinct original argument. I checked E1-E7 by the types, the field hypotheses, and the edge cases above. All assembly steps are under 2000 characters; the total assembly is 1452 characters. The larger old argument is preserved here, not hidden inside a long assembly step.

## Preserved argument for the independent downstream workers

The following are the exact seven text strings of the returned parent proof, grouped by new obligation. They are working material for the agents who will split the new nodes, not proof steps in those unsplit node files.

### lem-weil-point-transformation-rational-normalization

Original step 1:

Use [lem-weil-isomorphism-derived-pullback] with the automorphism $g$ of $s$; $\ell$ is invertible since $\ell\ne p$. Thus $P_E$ preserves the integral category. By [def-weil-rationalization-karoubi] the rational category has exactly the integral objects and Hom groups tensored with $E$. The formulas in [def-weil-finite-coefficient-point] and [def-weil-derived-pullback-tensor-hom] give, for an integral $v:K\to K'$ and $a\in E$, $F_E(v\otimes a)=a(F_E^{\mathrm{int}}(v)\otimes E)$ and $H_E(v\otimes a)=a(F_E^{\mathrm{int}}(P_Ev)\otimes E)$. In particular the proposed component $t_{E,K}:=\eta^E_K\otimes E$ has source $F_EK$ and target $H_EK$, both in $D^b_{\mathrm{fd}}(E)$.

Original cited statements: lem-weil-isomorphism-derived-pullback, def-weil-rationalization-karoubi, def-weil-finite-coefficient-point, def-weil-derived-pullback-tensor-hom.

Original step 2:

For integral $v:K\to K'$, the assumed naturality is $F_E^{\mathrm{int}}(P_Ev)\eta^E_K=\eta^E_{K'}F_E^{\mathrm{int}}(v)$. Apply the module-complex scalar-extension functor $-\otimes_{\mathcal O_E}E$ and multiply the resulting equality by $a\in E$. The formulas of [def-weil-finite-coefficient-point] and [def-weil-derived-pullback-tensor-hom] give $H_E(v\otimes a)t_{E,K}=t_{E,K'}F_E(v\otimes a)$. Every tensor is a finite sum of pure tensors by [def-weil-rationalization-karoubi]. Bilinearity of composition therefore gives, for $u=\sum_jv_j\otimes a_j$, $H_E(u)t_{E,K}=\sum_j a_j(H_E(v_j\otimes1)t_{E,K})=\sum_j a_j(t_{E,K'}F_E(v_j\otimes1))=t_{E,K'}F_E(u)$. This includes zero, sums and every balanced tensor representative, since both functor maps already factor through the tensor product.

Original cited statements: def-weil-finite-coefficient-point, def-weil-derived-pullback-tensor-hom, def-weil-rationalization-karoubi.

Original step 3:

For $E\subset L$, tensor the assumed integral compatibility equation with $L$ over $\mathcal O_L$. The last display of [lem-weil-point-sections-scalar-extension] identifies its sections comparisons with precisely $\bar\varphi_{E,L}$, and rationalizing the pullback comparison of [lem-pur-integral-operations-scalar-extension] gives precisely $\bar\alpha_{E,L}$. Consequently the equation becomes
$$b_{E,L,K}\,t_{L,K\otimes_E L}=(t_{E,K}\otimes_E L)\,\bar\varphi_{E,L,K}. \tag{*}$$
No comparison is replaced by an arbitrary isomorphism: tensoring is a functor, so it preserves the composite and the inverse occurring in the supplied equation. Tensoring the unit and tower equations in the two cited statements preserves those equations too. This proves the specified rational scalar compatibility, including equality of fields.

Original cited statements: lem-weil-point-sections-scalar-extension, lem-pur-integral-operations-scalar-extension.

### lem-weil-point-composite-comparison-tower

Original step 4:

Write $S_{L/E}K=K\otimes_E L$, $T_{L/E}A=A\otimes_E L$, and write $a^C:S_{N/L}S_{L/E}\xrightarrow{\sim}S_{N/E}$ and $a^D:T_{N/L}T_{L/E}\xrightarrow{\sim}T_{N/E}$ for the specified associators. For $E\subset L\subset N$, suppress these associators momentarily. The two cited tower equations read
$$\bar\alpha_{E,N}=\bar\alpha_{L,N,S_{L/E}K}\,S_{N/L}(\bar\alpha_{E,L}),\qquad \bar\varphi_{E,N}=(\bar\varphi_{E,L}\otimes_LN)\bar\varphi_{L,N,S_{L/E}K}.$$
Insert these expressions into $b_{E,N}=\bar\varphi_{E,N,P_EK}F_N(\bar\alpha_{E,N})^{-1}$ and use naturality of $\bar\varphi_{L,N}$ for $\bar\alpha_{E,L}^{-1}$. The result, with associators restored, is
$$b_{E,N,K}H_N(a^C_K)=a^D_{H_EK}(b_{E,L,K}\otimes_LN)b_{L,N,S_{L/E}K}. \tag{**}$$
Explicitly the middle interchange is $\bar\varphi_{L,N,S_{L/E}P_EK}F_N(S_{N/L}\bar\alpha_{E,L}^{-1})=(F_L(\bar\alpha_{E,L}^{-1})\otimes_LN)\bar\varphi_{L,N,P_LS_{L/E}K}$. This gives (**), and the unit equations give $b_{E,E}=1$ under unit identifications. Naturality follows by composing the two natural isomorphisms defining $b$. All the inputs here are the naturality, identity and tower assertions of [lem-weil-point-sections-scalar-extension] and [lem-pur-integral-operations-scalar-extension].

Original cited statements: lem-weil-point-sections-scalar-extension, lem-pur-integral-operations-scalar-extension.

Original step 5:

Let $u:S_{L/E}K\to S_{L/E'}K'$ represent a common-stage arrow as in [def-weil-algebraically-closed-coefficients]. The point-fiber action in [def-weil-finite-coefficient-point] is $A_L(u)=\bar\varphi_{E',L,K'}F_L(u)\bar\varphi_{E,L,K}^{-1}$. The pullback action of [def-weil-derived-pullback-tensor-hom] first gives $\bar\alpha_{E',L,K'}^{-1}P_L(u)\bar\alpha_{E,L,K}$. Apply the point-fiber action to this arrow, now between $P_EK$ and $P_{E'}K'$. Expanding $F_L$ of the composite gives exactly $B_L(u)=b_{E',L,K'}H_L(u)b_{E,L,K}^{-1}$. Thus these are the two specified functors, rather than alternative realizations. At a common stage they preserve identities and composition: the intermediate $\bar\varphi^{-1}\bar\varphi$ or $b^{-1}b$ cancels, and $F_L,H_L$ are functors. The two tower equations (the sections equation and (**)) show that scalar extension of $A_L(u),B_L(u)$ is respectively $A_N(u_N),B_N(u_N)$ after the source and target associators. Hence their classes are unchanged by further extension, and by changing to any equivalent representative, using the equality criterion of [def-weil-point-fd-qlbar-category].

Original cited statements: def-weil-algebraically-closed-coefficients, def-weil-finite-coefficient-point, def-weil-derived-pullback-tensor-hom, def-weil-point-fd-qlbar-category.

### lem-weil-point-rational-family-common-stage-naturality

Original step 6:

The proposed component at $(E,K)$ is the finite-stage class of $t_{E,K}$. Put $t^L_{E,K}=t_{E,K}\otimes_E L$ with the target-category unit identifications of [def-weil-point-fd-qlbar-category]. Equation (*) says $b_{E,L,K}^{-1}t^L_{E,K}=t_{L,S_{L/E}K}\bar\varphi_{E,L,K}^{-1}$. Apply Step 2 at field $L$ to the arbitrary rational morphism $u:S_{L/E}K\to S_{L/E'}K'$ and calculate in $D(L)$:
$$\begin{aligned} B_L(u)t^L_{E,K}&=b_{E',L,K'}H_L(u)t_{L,S_{L/E}K}\bar\varphi_{E,L,K}^{-1}\\ &=b_{E',L,K'}t_{L,S_{L/E'}K'}F_L(u)\bar\varphi_{E,L,K}^{-1}\\ &=t^L_{E',K'}\bar\varphi_{E',L,K'}F_L(u)\bar\varphi_{E,L,K}^{-1}=t^L_{E',K'}A_L(u).\end{aligned}$$
This is naturality over the very same field $L$, before passing to any colimit.

Original cited statements: def-weil-point-fd-qlbar-category.

Original step 7:

For a further finite field $N\supset L$, apply $-\otimes_LN$ to the equality of Step 6 and conjugate by the source and target tower associators. Functoriality preserves the equality and the expansions of Step 5 identify it with the equation for $u_N$. If $[L,u]=[L',v]$, [def-weil-algebraically-closed-coefficients] gives $N\supset L,L'$ with $u_N=v_N$. The two equations then have identical sides in $D(N)$; by [def-weil-point-fd-qlbar-category] they yield the same equality of morphism classes. Therefore all supplied integral components give the claimed natural transformation on the common-stage category. This proves independence of representative without assuming injectivity of transition maps, invertibility of $\eta$, or any special formula for its components.

Original cited statements: def-weil-algebraically-closed-coefficients, def-weil-point-fd-qlbar-category.

## Unfinished work

The three new obligations intentionally remain unsplit for independent stage-1 workers, as required by the return. There is no unassigned part of the old argument. The existing Lean sorry is untouched because only stage 1 is authorized.

## Validation

The required server dry run completed successfully: `OK (not pushed)` at `9dd99b7856a`, server preflight passed. The final report update is followed by another dry run and then the direct push. The commands run no local check_dag/review_split/preflight or compiler. The live parent statement was compared against the saved baseline and is unchanged; all four node files parse, all statement dependencies exist, and the three new nodes have no proof steps.
