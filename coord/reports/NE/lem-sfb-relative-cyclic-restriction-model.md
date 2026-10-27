# Repair report: lem-sfb-relative-cyclic-restriction-model

## Files written

The sandbox initially contained only dispatcher .brief files: no node, prior report, citations or search log. I copied the current read-only repository item as the returned baseline and retained it verbatim in returned-proof.json. No git command, compiler or build was run in the repository. The repository statement, statement dependencies, existing Lean/audit/review records and the existing search history are retained unchanged. The only parent changes are proof, proof_deps and split_report. The parent now has six assembly steps (2187 characters), rather than the 14732-character argument returned by the human. Six new statement-only nodes are delivered unsplit; none is a Mathlib leaf. Their proof, proof_deps are empty, proof_origin is null, and each has its own self-contained hypotheses and formulas.

- `lem-sfb-product-action-exact-forgetting`: statement, unsplit, no Mathlib match; carries returned steps 1, 2, 3, 4: Exact free induction for forgetting a commuting profinite action.
- `lem-sfb-relative-restriction-mate-forgetting`: statement, unsplit, no Mathlib match; carries returned steps 5, 6: Normalized relative restriction mate on injective models.
- `lem-sfb-cyclic-total-triangulated`: statement, unsplit, no Mathlib match; carries returned steps 7, 8: Signed cyclic totalization on the bounded-below derived category.
- `lem-sfb-cyclic-row-derived-comparison`: statement, unsplit, no Mathlib match; carries returned steps 9, 10, 11, 12: Invariant-normalized cyclic row comparison with residual action.
- `lem-sfb-relative-cyclic-coefficient-square`: statement, unsplit, no Mathlib match; carries returned steps 13, 14: Coefficient square for normalized relative cyclic rows.
- `lem-sfb-bar-cyclic-evaluation-roof`: statement, unsplit, no Mathlib match; carries returned steps 15, 16, 17: Evaluation map from the injective bar total to the cyclic total.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag and the relative/cyclic/forgetting notions. The specific implementation is lean/Sheaf/CategoryTheory/RelativeCyclicRestrictionModel.lean; relative_cyclic_restriction_model at line 157 has sorry at line 159, so cannot close this item. Related Sheaf definitions are not finished proofs and do not discharge the extracted tasks.

## WANTED

WANTED: a literature reference for the combined internal condensed relative cyclic comparison, exact induction for residual-action forgetting, nonflat coefficient square, and injective-bar evaluation normalization, for this item and its six new tasks. The inherited source explicitly requests this combined reference. I did not invent a Stacks tag for the combined theorem. The main-20261015 direct-images proof paragraph (3) supplies the open-direct-image context only. All six extracted statements and the retained argument are agent-formulated. Stacks sites-modules.tex, Tag 03EV, lemma-j-shriek-flat (2), supplies the free sheaf flatness ingredient, not the whole of any extracted task.

## Return repaired

The human requested at least four comparable tasks and a parent proof of at most 3000 characters, retaining every argument. There are six tasks: foundations/exact induction (old 1–4); restriction mate/forgetting (5–6); totalization signs (7–8); row-derived comparison/forgetting (9–12); arbitrary coefficient square (13–14); bar-evaluation roof (15–17). These are separate mathematical arguments, none restates the whole item. The statements retain the concrete intermediate formulas, not just headings or the item's conclusion clauses. The complete prior argument is copied below, allocated to its task, so future workers have the full derivation as well as a self-contained statement. The new JSON files themselves carry statements only, as requested.

No statement dispute was found; the parent's statement is unchanged. The strengthened normalization on every bounded-below complex is kept, because degree-zero normalization alone would not identify a chosen rank-one witness. No SGA source is used, and the chapter/unit route is unchanged.

## Sources and searches

I read coord/brief-stage1.md, stages/1-dag.md, roles/worker.md, GOAL.md, SETUP.md's three levels, and both B–E copies in coord/delivery-errors.md. I read the chapter and unit records, the main-20261015 direct-images proof paragraph (3), the 17-step returned item, its relative-definition statements, and the nearby scalar lattice, action-site/topos, derived-restriction and bar-roof statements. For the exact-induction task I read Stacks sites-modules.tex at lemma-j-shriek-flat, including the free presheaf formula and its sheafification proof. The other five tasks retain the agent expansion of paragraph (3), with the existing categorical ingredients explicitly named in the preserved argument; the blueprint is not represented as proving these auxiliaries.

Whole-DAG statement/title searches used cyclic total/restriction/comparison, forgetting/injectives/condensed, scalar/coefficient/cyclic and bar/roof/evaluation. I checked the tag 03EV and lemma-j-shriek-flat across the DAG. Whole-blueprint searches were: cyclic, residual, action.*injective, bar.*evaluation, cyclic total, derived restriction, free induction, cyclic coefficient, bar evaluation. The first broad cyclic search also matches acyclic, so a word-boundary DAG search was used to disambiguate it. No imported blueprint node states any of these full extracted tasks. blueprint_refs.py ancestor confirms the inherited null ancestor; the from.via chain is extended by this item, and from.place records paragraph (3) and the exact returned step allocation. No invented ancestor is substituted.

For each of the six new ids I ran two different LeanFinder phrasings, a Loogle name pattern, a Mathlib grep and a LeanSearch query through the mandatory msearch.py command. All 30 outputs are retained under <id>.search-results.json and the command's searches.jsonl. Every mathlib_searches entry has the exact command query and actual output. Three LeanSearch calls were rate-limited; their verdict is unavailable. Other searches succeeded. The results do not provide a one-line specialization for any whole task. Condensed.freeForgetAdjunction and profiniteFree use ordinary-ring condensed modules, not the residual-action adjunction for arbitrary internal condensed R. The finite cyclic resolutions have norm differentials and ordinary Rep coefficients. ContAction.resComp is about continuous actions on topological objects. The mappingCone.mapTriangleIso/mapTrianglehIso hits are for termwise additive functors; they do not state the adjacent-degree cyclic total's signed cone comparison. The general derived-unit and CommShift declarations assume their input functors/models and do not supply these comparisons. Source text in the corresponding Mathlib files was read to check these scope differences. No positive match is claimed.

## Not duplicates

lem-sfb-product-action-exact-forgetting vs lem-sfb-condensed-product-action-inflation: the existing theorem handles profinite product invariant adjunctions; the new task includes discrete J and the exact free-induction adjunction for forgetting G, preservation of injectives and conservativity on the full derived categories.

lem-sfb-product-action-exact-forgetting vs lem-pc-sites-modules-j-shriek-flat: the existing 03EV theorem is only flatness on a ringed site; the new task identifies the profinite free sheaf and constructs the commuting-action induction adjunction, with module and derived forgetting consequences.

lem-sfb-product-action-exact-forgetting vs lem-sfb-internal-action-site-presentation: a presentation and kernel/cokernel description do not state the exact free-induction adjunction or injective preservation.

lem-sfb-product-action-exact-forgetting vs lem-sfb-condensed-derived-restriction-calculus: scalar action forgetting exactness and Grothendieckness are existing ingredients; this task adds residual-group free induction and injective-preserving derived conservativity. These are required to compute the partial invariant forgetting comparison.

lem-sfb-relative-restriction-mate-forgetting vs lem-sfb-condensed-derived-restriction-calculus: the existing statement is scalar; this task constructs the mate retaining G and the normalized partial-to-scalar derived invariant comparison, on actual arrows.

lem-sfb-cyclic-total-triangulated vs def-sfb-relative-cyclic-total: the definition specifies a model and comparison predicate; it does not prove a realization exists. This task is the explicit total, homotopy, signed cone/shift and localization argument.

lem-sfb-cyclic-row-derived-comparison vs lem-sfb-discrete-lattice-koszul-resolution: the scalar statement gives an existential comparison on modules. The new task concerns complexes with residual G action and fixes the comparison on every complex by theta alpha = Qb, including the injective row and natural resolution formula. It chooses a permitted scalar witness; it does not identify arbitrary normalized witnesses from H0.

lem-sfb-relative-cyclic-coefficient-square vs def-sfb-relative-coefficient-comparisons: the definition specifies the desired datum; the new task supplies the nonflat common-acyclic-model compatibility. A definition is not being cited as a theorem.

lem-sfb-relative-cyclic-coefficient-square vs lem-sfb-ringed-derived-monoidal-comparisons: the existing generic ringed-topos comparison is an ingredient, not the comparison of this normalized cyclic row model or the exact beta/lambda/c coefficient squares.

lem-sfb-bar-cyclic-evaluation-roof vs lem-sfb-internal-bar-roof-adjunction: the existing result normalizes a bar resolution and cocycle roofs/adjunction signs; it does not construct the evaluation map to the two-term cyclic total or prove its relation to the restriction mate. The new task is that concrete cochain-map and derived-roof calculation.

lem-sfb-bar-cyclic-evaluation-roof vs lem-sfb-condensed-derived-invariant-bar: the existing derived bar equivalence does not state evaluation at a chosen generator, the cochain identity E j = k epsilon, or the cyclic restriction roof.

lem-sfb-product-action-exact-forgetting vs lem-sfb-condensed-product-bar-comparison: the product-bar theorem identifies successive derived invariants with bar totalizations for profinite groups; its proof contains an induction ingredient, but its statement does not supply the new task, in particular for discrete J. I do not use a proof as if it were a statement.

## Review by NE

I checked the new parent proof against the full statement of each cited new node, with the files open. Step 1 uses the exact-forgetting task's Grothendieck/enough-injectives and normalized adjunction assertions for exactly J=H,Z; G remains profinite, which is necessary for the representable free-flat sheaf argument. Step 2 uses the restriction-mate task's displayed all-complex computation-unit equation and its delta_J comparison of actual derived arrows, which gives more than H0. Step 3 uses the totalization task's explicit differential, signed shifts, cone arrows and lower-bound identification, so its triangulated conclusion has the same signs as the parent. Step 4 uses the row task's invertible theta and full normalization, including its resolution formula and the chosen scalar rank-one witness; defining c is then composition. Step 5 uses the coefficient task's d_J, its non-injective common acyclic model and its three squares. It assumes neither scalar extension flatness nor injectivity after scalar restriction. Step 6 uses exactly the evaluation-roof task's c eta^{-1}j identity for trivial regular coefficients, not an underived cochain comparison asserted without acyclicity. citations.json contains a verbatim statement excerpt for each of these six citations. All proof_deps are the union of these uses.

I also checked the content assigned to each future worker. For old 1–4, small action-site presentation applies to the discrete group sheaf as well as the profinite ones; inverse equivariant isomorphisms remain equivariant, and exact forgetting commutes with cohomology, so the cone argument detects derived isomorphisms without boundedness. The free-induction formula uses only the profinite first factor G, never induction along the image of u. For old 5–6, the mate equation is meaningful on a restricted injective even when that restriction is not injective. For old 7–8, d^2=0 follows by the cancellation of the two (T-1)d terms, and the second-column signs in homotopies, shifts and the source-cone summand are retained explicitly. For old 9–12, the injective module row normalization lifts by conservative forgetting; the row-total map and unit characterize theta on all bounded-below complexes, so naturality/cone compatibility does not rest on an unsupported uniqueness claim on H0. For old 13–14, the ringed-topos square supplies the normalized mate d; sI' need not be injective, but exact scalar restriction preserves its augmented rows, which suffices for the formula. For old 15–17, E is internal evaluation, its horizontal identity is (d_h m)(tau)=(T-1)m, its vertical column-one sign is negative in both totals, E b_H is inclusion and E j_rep=k epsilon. Cancellation uses only k and the bar augmentation, not invertibility of beta. Each original argument is present below with its original citations and source.

Small cases were tested in words: R=0 gives zero objects and maps throughout; G=1 makes the forgetting comparison identity; J=1 makes invariants identity and free induction still has its stated adjunction. For tau=1, K has zero horizontal differential, but beta is not asserted invertible (for H=1 the target has the additional degree-one R). For complexes with a negative lower bound, the explicit column sign after shifting to first quadrant is retained; no convergence assumption for an unbounded double complex is used. Bar totals use nonnegative resolution and bar degrees, hence finite diagonals. A nonflat coefficient map such as constant Z to Z/2 is allowed precisely because scalar restriction, rather than scalar extension, preserves the rows. The preserved old proof has no step above 2000 characters; the new parent steps are each below 500 characters. No new statement is an elementary two-line fact: each packages a distinct multi-step construction required by the explicit re-split instruction. No new node has proof steps hidden in its statement; the formulas there specify conclusions/data to be constructed, and the derivations are only in this report.

The final notation audit made the coefficient-map domain explicitly derived and bounded below for either J, and introduced Q, Gamma_H, T, alpha and b in the standalone bar task. The corrected defect is the size/allocation of proof work, not a weakened statement or an altered route. I have not changed the source, launcher scripts, live repository, definitions, Lean files, or maintainer review fields. The independent maintainer will review the new split.

## Preserved argument allocated to the six new tasks

The following is the complete returned proof verbatim, in original step order within each task. It is retained as worker material, not as proof steps in the unsplit JSON nodes.

### lem-sfb-product-action-exact-forgetting

Original step 1:

Write $\mathcal M_R$ for internal modules. Identify them with section-ring module sheaves by [def-weil-pbc-internal-abelian-sheaf-module-equivalence]. Apply [lem-sfb-internal-action-site-presentation] to the group sheaves $\underline G$, $\underline J$ and $\underline G\times\underline J$, for $J=H,\mathbf Z_{\mathrm{disc}}$. They are sheaves: continuous maps glue along finite profinite quotient covers (for the discrete target their finite-image clopen fibers glue). The action sites are small in the fixed coefficient universe. The presentation and [lem-pur-ringed-site-grothendieck-abelian] make all the action categories Grothendieck abelian. In particular [lem-sp-grothendieck-enough-injectives] applies, including to $G\times\mathbf Z$, which is not profinite.

Uses: def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-sfb-internal-action-site-presentation, lem-pur-ringed-site-grothendieck-abelian, lem-sp-grothendieck-enough-injectives.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 2:

For projection inflation $L_J^G:\mathcal A_G(R)\to\mathcal A_{G\times J}(R)$, the underlying module and map do not change, so it is exact by the kernel/cokernel assertion of [lem-sfb-internal-action-site-presentation]. The sections fixed by $J$ after every base change form a submodule sheaf, stable under $G$ because the two actions commute. A map $L_J^G M\to N$ is equivariant exactly when its image lies in that submodule; restriction of its codomain and composition with its inclusion are inverse transposes. This proves $L_J^G\dashv\Gamma_J^G$ with the required normalization, also for discrete $J$. For profinite $J$ this is precisely the datum of [lem-sfb-condensed-product-action-inflation].

Uses: lem-sfb-internal-action-site-presentation, def-sfb-condensed-action-module, lem-sfb-condensed-product-action-inflation.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 3:

Let $U_J:\mathcal A_{G\times J}(R)\to\mathcal A_J(R)$ forget $G$, and $U_0:\mathcal A_G(R)\to\mathcal M_R$. They create kernels and cokernels by the action-site presentation, and reflect zero objects and isomorphisms: the inverse of an equivariant isomorphism is equivariant. They are exact, so descend to triangulated functors on the ordinary derived categories. Exactness gives $H^n(UK)=U H^n(K)$. Thus $UK=0$ implies all $H^n(K)=0$ and $K\to0$ is a quasi-isomorphism, so $K=0$. Applying this to the cone triangle of a morphism shows that derived $U$ is conservative as well. This argument has no boundedness restriction.

Uses: lem-sfb-internal-action-site-presentation, lem-weil-pbc-exact-functor-complex-cohomology, lem-weil-pbc-exact-functor-derived-factorization, def-weil-abstract-derived-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 4:

There is an exact left adjoint to $U_J$, namely $F_G(M)=R[\underline G]\otimes_R M$, with $G$ translating the free generators and $J$ acting on $M$. Indeed $[g]\otimes m\mapsto g f(m)$ and evaluation at $[1]\otimes m$ are inverse adjunction formulas, valid after every profinite base change. Here $R[\underline G]=j_{G!}R_G$: both are the sheafification of the free module on maps into the profinite test object $G$. It is flat by [lem-pc-sites-modules-j-shriek-flat], so $F_G$ is exact. The same construction with $J=1$ gives an exact left adjoint to $U_0$. Therefore both $U_J$ and $U_0$ preserve injectives by [lem-sp-right-adjoint-preserves-injectives]. This does not use induction along a non-profinite subgroup.

Uses: lem-pc-sites-modules-j-shriek-flat, lem-pc-sheaf-modules-tensor-closed, lem-sfb-internal-action-site-presentation, lem-sp-right-adjoint-preserves-injectives.

Source: literature/stacks-project/sites-modules.tex — Tag 03EV, lemma-j-shriek-flat; elementary free-module adjunction with commuting action.

### lem-sfb-relative-restriction-mate-forgetting

Original step 5:

Use bounded-below termwise injective resolutions on the small action sites [lem-sc-bounded-below-injective-resolution], and the normalized derived functors and units $\alpha_J^G$ of [lem-weil-pbc-right-derived-plus-injective]. The exact adjunctions of step 2 induce canonical derived adjunctions [lem-trf-bounded-below-derived-adjunction]. Put $V=\operatorname{Res}_{1_G\times u}$. Restriction is exact and $V L_H^G=L_{\mathbf Z}^G$. Take the derived mate of this identity square. This defines $\beta^G$. Its model equation, by [lem-trf-bounded-below-derived-mate-model], is
$$\beta^G_{QP}\alpha^G_{H,P}=\alpha^G_{\mathbf Z,VP}\,Q(\iota_P),$$
where $\iota_P:\Gamma_H^G P\to\Gamma_{\mathbf Z}^G VP$ is the invariant inclusion, termwise. In particular its degree-zero map is the claimed inclusion. The canonical derived adjunctions commute with canonical shifts [lem-sp-canonical-right-derived-adjunction-shift]; the mate, expressed as unit, identity and counit, consequently commutes with shifts and image-triangle boundaries.

Uses: lem-sc-bounded-below-injective-resolution, lem-weil-pbc-right-derived-plus-injective, lem-trf-bounded-below-derived-adjunction, lem-trf-bounded-below-derived-mate-model, lem-sp-canonical-right-derived-adjunction-shift.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 6:

For every bounded-below injective complex $I$ in $\mathcal A_{G\times J}(R)$, step 4 makes $U_J I$ a bounded-below injective complex. The equality $U_0\Gamma_J^G I=\Gamma_{R,J}U_J I$ is equality of fixed-section submodules, with identical inclusion maps. The derived resolution comparisons [lem-sp-derived-injective-resolution-naturality] therefore give a natural isomorphism
$$D(U_0)R\Gamma_J^G\cong R\Gamma_{R,J}D(U_J).$$
For $\beta$, apply its model equation in step 5 to $I$. Under these identifications it is the invariant-inclusion model equation for the canonical scalar restriction of [lem-sfb-condensed-derived-restriction-calculus]; uniqueness in [lem-weil-pbc-right-derived-plus-injective] identifies the transformations. This establishes equality of the actual derived arrows, not just of their degree-zero cohomology.

Uses: lem-sp-derived-injective-resolution-naturality, lem-sfb-condensed-derived-restriction-calculus, lem-weil-pbc-right-derived-plus-injective.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

### lem-sfb-cyclic-total-triangulated

Original step 7:

The two-column total is explicitly
$$K^G(N)^n=N^n\oplus N^{n-1},\qquad d(x,y)=(d_Nx,(T-1)x-d_Ny).$$
The actions commute, hence $T-1$ and this differential are $G$-equivariant. Squaring $d$ gives zero because $d_NT=Td_N$. A chain map acts on both summands; a chain homotopy $h$ gives the total homotopy $(h,-h)$, since the horizontal cross terms cancel. Each column functor is the underlying-module functor and is exact. Consequently a quasi-isomorphism of bounded-below inputs gives a columnwise quasi-isomorphism and hence a total quasi-isomorphism by [lem-sc-first-quadrant-total-column-comparison]. To apply the first-quadrant statement, shift the common vertical lower bound to zero and multiply column $a$ by the resulting constant sign $(-1)^{a b}$. Thus $QK^G$ descends to $D^+$.

Uses: def-sp-double-complex-total, lem-sfb-internal-action-site-presentation, lem-sc-first-quadrant-total-column-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 8:

The shift comparison $K^G(N[s])\to K^G(N)[s]$ is $(x,y)\mapsto(x,(-1)^s y)$. For a chain map $f:A\to B$, reorder the summands of $K^G C(f)$ to those of $C(K^G f)$ and multiply each source-cone summand in cyclic degree $a$ by $(-1)^a$. Direct substitution in $d(x,y)$ gives a chain isomorphism. It is the identity on the target inclusion and agrees on the negative cone projection with the displayed shift comparison. Thus it identifies all three arrows of the cone triangles, in the convention $C(f)\xrightarrow{-p}A[1]$ of [def-weil-abstract-derived-category]. Since distinguished triangles are images of cone triangles up to isomorphism, this makes $QK^G$ triangulated.

Uses: def-weil-abstract-derived-category, def-sp-double-complex-total.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

### lem-sfb-cyclic-row-derived-comparison

Original step 9:

If $I$ is injective in $\mathcal A_{G\times\mathbf Z}(R)$, then $U_{\mathbf Z}I$ is injective by step 4. Apply [lem-sfb-discrete-lattice-koszul-resolution] with $r=1$ to $U_{\mathbf Z}I$. Its invariant normalization says that the composite
$$(U_{\mathbf Z}I)^{\mathbf Z}[0]\longrightarrow[U_{\mathbf Z}I\xrightarrow{T-1}U_{\mathbf Z}I]\xrightarrow{\lambda_R}R\Gamma_{\mathbf Z}(U_{\mathbf Z}I)$$
is the canonical derived-unit map. That last map is invertible on injectives by [lem-weil-pbc-right-derived-plus-injective]. Hence the first arrow is a quasi-isomorphism. It is the forgotten form of $\Gamma_{\mathbf Z}^G I[0]\to K^G(I)$, which is therefore a quasi-isomorphism by step 3. Only the stated existence and invariant-normalization clause of the scalar lattice node is used here.

Uses: lem-sfb-discrete-lattice-koszul-resolution, lem-weil-pbc-right-derived-plus-injective.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 10:

For a bounded-below injective complex $I$, apply step 9 in every vertical degree. The row augmentations assemble to
$$b_I:\Gamma_{\mathbf Z}^G I\longrightarrow K^G(I).$$
It is a quasi-isomorphism by total comparison [lem-sc-first-quadrant-total-column-comparison]. For the row version interchange indices and conjugate the total differential by $(-1)^{a b}$; this is $1$ on each augmentation axis. A lower vertical bound is removed as in step 7. The inclusion in cyclic degree zero defines a natural map $Q\Gamma_{\mathbf Z}^G\to QK^G$ on bounded-below complexes. By the universal property in [lem-weil-pbc-right-derived-plus-injective] it uniquely induces
$$\theta^G:R\Gamma_{\mathbf Z}^G\longrightarrow QK^G,\qquad \theta^G_{QP}\alpha^G_{\mathbf Z,P}=Q(b_P).$$
On $I$, both $\alpha_I$ and $Q(b_I)$ are invertible, so $\theta_I$ is invertible. Every derived object has such a resolution; naturality proves $\theta^G$ is an isomorphism everywhere. Define $\lambda^G=(\theta^G)^{-1}$.

Uses: lem-sc-first-quadrant-total-column-comparison, lem-weil-pbc-right-derived-plus-injective, lem-sc-bounded-below-injective-resolution.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 11:

Here is the full normalization, which also controls naturality: for any resolution $a:N\to I$,
$$\lambda^G_N=\alpha^G_{\mathbf Z,I}\,Q(b_I)^{-1}\,Q(K^G a),$$
followed by the inverse of $R\Gamma_{\mathbf Z}^G(Qa)$ on its target. The equation defining $\theta$ makes this independent of all choices by the derived-unit universal property. For a cone diagram, use the cone of a map of specified injective resolutions: it is again bounded below and termwise injective, and its augmentation is a quasi-isomorphism by [lem-sp-derived-injective-resolution-naturality]. The row inclusions $b$ commute with the cone and shift identifications of step 8. On these injective models the derived units are the normalized comparisons and their shifts are canonical [lem-sp-canonical-right-derived-adjunction-shift]. The displayed formula therefore makes $\lambda^G$ a shift-compatible natural isomorphism of triangulated functors, retaining the negative cone boundary convention. On a module its map from invariants is exactly the invariant inclusion. Set $c_N^G=(\lambda_N^G)^{-1}\beta_N^G$.

Uses: lem-weil-pbc-right-derived-plus-injective, lem-sp-derived-injective-resolution-naturality, lem-sp-canonical-right-derived-adjunction-shift.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 12:

Forgetting $G$ leaves $K$, $b$ and every differential unchanged and takes a chosen injective resolution to an injective resolution. Thus the formula of step 11 becomes the scalar rank-one comparison, and step 6 takes $c^G$ to its scalar composite with restriction. More precisely, the rank-one existence theorem [lem-sfb-discrete-lattice-koszul-resolution] may and here does use the witness obtained by this same row-augmentation construction with $G=1$; it satisfies its stated naturality and normalization. We do not infer uniqueness of a derived isomorphism from its degree-zero map alone. The strengthened equation $\theta\alpha=Qb$ fixes the comparison on all bounded-below complexes. All forgetting comparisons commute with shifts and boundaries because they identify the actual resolution and cone diagrams.

Uses: lem-sfb-discrete-lattice-koszul-resolution, lem-sp-derived-injective-resolution-naturality, lem-weil-pbc-right-derived-plus-injective.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

### lem-sfb-relative-cyclic-coefficient-square

Original step 13:

Let $\varphi:R\to R'$ and $f:N\to s_{G\times J}N'$ be an equivariant coefficient map. The action topoi of [lem-sfb-action-topos-geometric-restriction] apply to the group-sheaf projection $G\times J\to G$: its module pullback is $L_J^G$ and its direct image is $\Gamma_J^G$. On these topoi scalar restriction is direct image along the identity geometric morphism with ring map $\varphi$. The commuting scalar/projection square gives, by [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] and its adjunction normalization [lem-sfb-ringed-derived-monoidal-comparisons], a canonical isomorphism
$$d_J:R\Gamma_J^{G,R}s_{G\times J}\xrightarrow{\sim}s_G R\Gamma_J^{G,R'}.$$
Define the coefficient map as $d_J R\Gamma_J^{G,R}(f)$. This uses derived scalar-extension adjunctions, not exactness of ordinary scalar extension. For restriction along $1_G\times u$, both paths around the coefficient square transpose to the same map $V L_H^G R\Gamma_H^G N\xrightarrow{V\varepsilon_H}VN\xrightarrow{Vf}VsN'$. Mate pasting [lem-weil-pbc-mate-pasting] proves equality. The same pasting with forgetting gives the coefficient compatibility of step 6.

Uses: lem-sfb-action-topos-geometric-restriction, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-mate-pasting.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 14:

For the cyclic coefficient square, let $N'\to I'$ be a bounded-below injective resolution over $R'$. Every augmented cyclic row for $I'$ is a quasi-isomorphism by step 9; scalar restriction is exact and leaves that row and $T-1$ unchanged, so the same is true for $sI'$, without claiming its terms are injective over $R$. Therefore $Q(b_{sI'})$ is invertible by step 10's row-total argument. The identity $K_R(sI')=s_GK_{R'}(I')$ identifies these row maps. By adjunction normalization in step 13, $d_{\mathbf Z}^{-1}$ is the derived mate of the identity $L_{\mathbf Z}^{G,R}s_G=s_{G\times\mathbf Z}L_{\mathbf Z}^{G,R'}$. Apply [lem-trf-bounded-below-derived-mate-model], whose two horizontal functors here are exact scalar restrictions. Its model equation gives $d_{\mathbf Z}\alpha_R(sI')=s_G\alpha_{R'}(I')$. Since $\theta_R\alpha_R(sI')=Q(b_{sI'})$ is invertible, $\alpha_R(sI')$ is invertible as well. Thus the defining equations $\theta\alpha=Qb$ on this common acyclic model give $s_G\lambda_{R'}=d_{\mathbf Z}\lambda_R$ under the termwise coefficient identification. Compose with $f$ and naturality to obtain the general coefficient square. Scalar comparisons commute with canonical shifts by [lem-weil-pbc-derived-adjunction-shift]; hence the squares for $\beta,\lambda,c$ also preserve triangle boundaries.

Uses: lem-sc-first-quadrant-total-column-comparison, lem-weil-pbc-right-derived-plus-injective, lem-trf-bounded-below-derived-mate-model, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-derived-adjunction-shift.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

### lem-sfb-bar-cyclic-evaluation-roof

Original step 15:

It remains to prove the bar identity, now with $G=1$ and $N=R$ having trivial $H$-action. Choose a nonnegative equivariant injective resolution $a:R[0]\to I$. Use the explicit compatible bar model in [lem-sfb-internal-bar-roof-adjunction], which spells out the normalization of [lem-sfb-condensed-derived-invariant-bar]:
$$D^{p,q}=\underline{\operatorname{Hom}}_R(R[\underline H^p],UI^q),\quad d_{\mathrm{Tot}}=d_h+(-1)^p d_I.$$
Its invariant-inclusion map $b_H:\Gamma_H I\to\operatorname{Tot}D$ represents $\eta$; the map $V^\bullet\to\operatorname{Tot}D$ induced by $a$ in resolution degree zero represents $j$. These are exactly statements of the cited model node, not an assumption that $V$ computes derived invariants. All diagonals here are finite because both indices are nonnegative.

Uses: lem-sfb-internal-bar-roof-adjunction, lem-sfb-condensed-derived-invariant-bar, def-sp-double-complex-total.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 16:

Define $E:\operatorname{Tot}D\to K^1(VI)$, where $V$ now denotes restriction along $u$, by the identity on $D^{0,q}=UI^q$, evaluation at $\tau$ from $D^{1,q}$ to cyclic degree $1$ and vertical degree $q$, and zero for $p\geq2$. Evaluation is an internal module morphism: it is precomposition with $R\to R[\underline H]$, $1\mapsto[\tau]$, and so is natural after every profinite base change. The only horizontal chain equation needing a check is
$$(d_h m)(\tau)=\tau m-m=(T-1)m.$$
There is no target in cyclic degree two. Vertical differentials commute with evaluation and both totals use $(-1)^p$ in column $p=0,1$, so $E$ is a cochain map. Moreover $Eb_H$ is the invariant inclusion $\Gamma_H I\to K^1(VI)$, in cyclic degree zero. This calculation uses the action-dependent bar differential even though the original coefficient module $R$ was trivial: the resolution terms need not have trivial action.

Uses: lem-sfb-internal-bar-roof-adjunction, lem-pc-sheaf-modules-tensor-closed, def-sp-double-complex-total.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

Original step 17:

Put $k=K^1(Va):[R\xrightarrow0R]\to K^1(VI)$; it is a quasi-isomorphism by step 7 and exactness of restriction. Steps 5 and 10 give, on the resolution $I$,
$$c_R^1=Q(k)^{-1}Q(Eb_H).$$
Indeed the derived-mate equation for $\beta$ followed by $\theta\alpha=Qb$ gives precisely the invariant inclusion into $K^1(VI)$; no injectivity of $VI$ is needed. With $\eta=Q(b_H)$ in the chosen model, cancellation yields $c_R^1\eta^{-1}j=Q(k)^{-1}Q(E)j$. On complexes, $E$ applied to the representative of $j$ is $k\epsilon$: in degree zero it is $a$, in degree one it is $a$ after evaluation at $\tau$, and in all higher degrees it is zero. Hence the last expression is $Q(\epsilon)$. The map $\epsilon$ is a cochain map since $R$ has trivial action and $d_h^0=0$. No invertibility of $\beta$ was used or obtained.

Uses: lem-trf-bounded-below-derived-mate-model, lem-weil-pbc-right-derived-plus-injective, lem-sfb-internal-bar-roof-adjunction, lem-sfb-condensed-derived-invariant-bar.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), open direct image: relative cyclic calculation below the tame-boundary input; agent expansion, not a claim that the blueprint states this auxiliary result.

## Unfinished work

The six extracted nodes intentionally remain unsplit for parallel future stage-1 work. No portion of the requested repair is deferred: delivery checks and push are run after this report is written. Their final results are recorded below.

## Validation

First required server dry run exited successfully: OK (not pushed), preflight passed at d76255af6ae. A final notation audit then explicitly introduced the derived coefficient morphism and bar-model Q, T, invariants and computation-unit symbols; the mathematical statements and search questions are unchanged. A second required dry run is run on these final files before pushing.
