# Q99: stage-1 re-split of lem-weil-isomorphism-comparison-scalar-extension

## Files written

- `dag/nodes/sec-six-functors/lem-weil-isomorphism-comparison-scalar-extension.json`: existing statement, unchanged; five-step assembly of the specified compatibility, replacing the returned eight-step monolith.
- `dag/nodes/sec-six-functors/lem-weil-isomorphism-scalar-tensor-kflat-model.json`: statement, unsplit; Mathlib no match. Exact inverse image preserves the flat-term K-flat model; ordinary coefficient tensor commutes with this inverse image, on complexes, finite quotient squares, and derived categories.
- `dag/nodes/sec-six-functors/lem-weil-isomorphism-scalar-augmentation-cone.json`: statement, unsplit; Mathlib no match. The two actual chain augmentations agree in both coordinates of the specified scalar-extension Roos cone.
- `report.md`, `citations.json`, and `searches.jsonl`: review, verbatim citation evidence, and actual search log. `returned-node.json` retains the starting node, and the two local Python scripts only prepare sandbox data; none is a Lean file or launcher modification.

## Attachments

None. Searching `lean/WeilConjectures/` for the blueprint tag and the exact declaration gave no attachment. The existing declaration `WeilConjectures.isomorphismComparison_scalarExtension` in `lean/Sheaf/Paper/IsomorphismComparisonScalarExtension.lean:224` has `sorry` at line 236. Its tensor-model existence helpers at lines 55, 82 and 104 also have sorry proofs, at 62, 92 and 118. The derived tensor definition at 134 depends on that tensor existence helper. These are source material, not finished proofs. No Lean was written or compiled.

## WANTED

None: all sources used here were available locally.

## What was wrong and how it was repaired

The human deliberately returned the already reviewed node because its proof text was 5442 characters, too much work for one stage-3 item. This repair does not dispute or change its statement, its definition of alpha or beta, its coefficient categories, or its Lean record. The tensor model and the strict cone calculation now have separate self-contained statements, empty proof and proof_deps, null proof_origin, and status unsplit. They are strictly below the parent: neither states alpha T(kappa) = kappa beta. In particular the cone lemma ends at equality of chain maps, before completion comparison conjugation, normalization and localization. The original cone argument was not replaced by equality of projections.

There were no retained node files or report in this sandbox at startup (only dispatcher markers). I therefore copied the current live node, which contains the previously accepted returned argument. Its eight steps appear verbatim below so that no argument is lost. The final delivery tool rebases the split-owned fields onto current server main and retains maintainer-owned records; no git command was run in the read-only clone.

## Allocation of the old proof

Old Steps 1–2 become the tensor-model node: the completed coefficient projection equations, exact inverse image, pure-tensor comparison, strict quotient compatibility, and derived representative descent. The K-flat change of rings at the start of old Step 4 is included in that model's statement. This leaves a substantive module/coefficient-equivalence argument for its next worker, independent of the cone calculation.

Old Step 7 becomes the augmentation-cone node: the precise domain Z, the two composites, their common finite component, transported coefficient balancing, all quotient transitions, and the zero shifted coordinate. The new statement fixes every object and every coordinate; the full argument is reproduced verbatim below for the future worker.

Old Steps 3–5 are assembly from the existing finite-free-completion and specified-alpha statements, retained in new Step 2. These existing nodes already state the natural chi, its independence and zero shifted coordinate, Q's K-flatness, chi_Y(P):Q to B(P), both coordinates of delta, and the displayed formula for alpha. Thus they do not need duplicate new nodes. The inverse-image tensor factors of beta now come from the tensor-model node. Old Step 6's entire theta-inverse/G(unit) naturality calculation remains explicitly in new Step 3; it is a few lines of naturality, so it is a step rather than a redundant new lemma. Old Step 8's conjugation and cancellation remain in new Step 5. New Step 4 is the localization of the new chain identity, using precisely the specified comparison definition and Step 3's resolution independence.

## Sources read

For the parent and both new statements I read Bhatt–Scholze, *The pro-etale topology for schemes*, Section 6.5, Lemma 6.5.9(4)–(5), printed pp. 50–51, in `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`. This supplies the completed-pullback context, not a verbatim proof of coefficient compatibility. The added assertions and the retained parent argument are agent calculations from the specified quotient maps. I read the entire statements of `def-weil-inverse-image-pullback-comparison` (especially the completed structure isomorphism and part (b)), `def-weil-integral-scalar-extension`, `def-pur-integral-derived-operations`, `lem-weil-specified-pullback-comparison-alpha`, `lem-weil-finite-free-completed-scalar-comparison`, and `lem-weil-isomorphism-derived-pullback-comparison-normalization`.

For the tensor model I additionally read `lem-pur-isomorphism-inverse-image-tensor-hom`, `lem-weil-proetale-isomorphism-inverse-image`, `lem-pur-kflat-change-of-rings`, `def-pc-kflat-complex`, `lem-pc-kflat-resolution`, and Stacks `sites-modules.tex`, Tag 03EL, label `lemma-tensor-product-pullback` (the tensor comparison input, not a citation for the full new statement). The new nodes cite the comparison and K-flat/tensor definition nodes for their precise meanings. They do not use an unspecified condensed-module category.

I read the chapter and unit records, the main-20261015 blueprint `sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-weil-global-geometric-frobenius.md`, and `sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md` clauses (2)–(3). The first cohomology-transport arrows are the inherited blueprint ancestor. No chapter or unit route is changed. The blueprint ancestor tool returned def-weil-global-geometric-frobenius. New nodes have the parent's ancestor and its full via chain preceded by this item. No SGA source is used.

## Not duplicates

lem-weil-isomorphism-scalar-tensor-kflat-model vs lem-sfb-kflat-scalar-comparison-normalization: the existing node identifies a derived scalar-adjunction mate for a general inverse image; it does not assert that the transported completed-ring inverse image of every flat-term K-flat P is itself flat-term K-flat, nor the specified same-index completed-to-finite quotient square. Its generic derived comparison can be reused in the new node's future proof.

lem-weil-isomorphism-scalar-tensor-kflat-model vs lem-weil-isomorphism-derived-pullback-reduction-tower: that node is at a single coefficient field and assumes K-flatness of both pulled representatives in its comparison clause; it does not prove this preservation or the E-to-L tensor model.

lem-weil-isomorphism-scalar-tensor-kflat-model vs lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution: that node chooses a specially adapted resolution; the new node concerns every given flat-term K-flat representative under an isomorphism, with explicit finite-extension tensor and quotient compatibility.

lem-weil-isomorphism-scalar-tensor-kflat-model vs lem-pur-isomorphism-inverse-image-tensor-hom: the existing node is a sheaf-level tensor/Hom/inverse-limit statement, with no K-flat or derived representative assertion. The new work includes preservation of K-flatness and descent of the specified quotient-compatible chain comparison.

lem-weil-isomorphism-scalar-augmentation-cone vs lem-weil-specified-pullback-comparison-alpha: that node defines d and delta, specifies their two coordinates and identifies alpha. It does not assert delta(a_E tensor S) = a_L b. That is the additional strict augmentation square to prove here.

lem-weil-isomorphism-scalar-augmentation-cone vs lem-weil-isomorphism-comparison-scalar-extension: the parent asserts an equality in a derived category involving two completion comparisons and alpha/beta. The new lemma is the strictly smaller chain-map identity before completion conjugation and localization. Neither the parent's full conclusion nor one of its stated isomorphism clauses is restated.

lem-weil-isomorphism-scalar-augmentation-cone vs lem-pod-canonical-coefficient-pullback-reduction: that node normalizes pullback for the single coefficient object and its reduction projections; it has no coefficient extension E to L or arbitrary K-flat coefficient complex tensor square.

lem-weil-isomorphism-scalar-augmentation-cone vs lem-tw-ordinary-completed-integral-pullback: that node specifies the completion map for ordinary pullback at one coefficient field, with no scalar-change square between two completion cones.

Whole-DAG statement searches for isomorphism/inverse image/K-flat/coefficient and for delta_P were inspected, in addition to source searches for the proposed notions. Whole-blueprint searches were run for scalar extension, inverse image, K-flat, augmentation, quotient cone, cone augmentation, coefficient comparison, scalar tensor and K-flat model. No imported statement states either new result. The search log is actual msearch output, not reconstructed queries.

## Mathlib searches read

Both new nodes have LeanFinder, LeanSearch, Loogle and grep searches; the two semantic phrasings were different. All services answered successfully. For the tensor model the hits were generic adic completion finite-module comparisons, exact flat extension for ModuleCat, a sheaf equivalence, and presheaf tensor constructions. I read the presheaf Monoidal definitions, including tensorObj at line 63, and checked the returned signatures. They do not identify completed-coefficient sheaf complexes or preserve their K-flat models with these quotient squares.

For the cone lemma I read `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`, ext_to/ext_to_iff at lines 171–185, and `.../Pretriangulated.lean`, map/map_eq_mapOfHomotopy at lines 160–168. These establish general component extensionality or construct a cone map from a square already known to commute. They do not prove the balanced coefficient-generator equality that is the new lemma's content. They can be tools in its later proof, but a one-line specialization does not supply the missing square. Both new nodes remain unsplit, with no Mathlib match falsely claimed.

## Review by Q99

I checked every proof-step citation against the statement it uses and copied literal statement spans into citations.json. Step 1 uses the K-flat resolution existence statement, the new tensor-model statement for Q, Z and b, and the comparison definition for the exact completed-ring module functor. Exactness is supplied in the latter's structure-isomorphism paragraph, not inferred from an assertion about constant module coefficients alone. Step 2 uses finite-free comparison for the actual chi map and its naturality/invertibility; the specified-alpha statement explicitly supplies Q, B(P), chi_Y(P), delta with both coordinates and its alpha formula; the tensor-model statement supplies the other invertible factor of beta. Step 3 uses the normalization equation theta kappa = G(u) and naturality/independence of theta, and explicitly derives naturality of kappa rather than attributing it verbatim to that statement. The finite-free statement certifies that C_Y K and T_Y K are linked by that actual chi isomorphism. Step 4 cites the new entire chain identity and the comparison definition to identify a_P and a_Q with the specified kappa after localization; the derived-category definition supplies this localization. Step 5 only substitutes earlier equations, uses naturality of chi and cancels an isomorphism; it contains no new comparison lemma.

For the tensor-model statement I verified the site equivalence and completed coefficient projection equations, and checked the K-flat hypothesis term by term: the inverse equivalence carries an acyclic X-complex to an acyclic Y-complex; inverse-image tensor compatibility identifies its tensor with G_E P with inverse image of the tensor with P. Thus the K-flat test transports, and the same exact tensor equivalence transports flatness of each term. Change of rings then gives Q and Z. The map b and its inverse are the displayed balanced tensor maps; their coefficient actions use c_E and c_L. Exactness and the canonical K-flat identifications descend b to the derived category. The finite quotient square is a separate coherence assertion with explicit coefficient arrows, not just the existence of a tensor isomorphism. No assumption that an arbitrary pullback preserves K-flatness was used.

For the augmentation-cone statement I checked the same-index maps exist also for ramified extensions, since varpi_E^m O_L is contained in varpi_L^m O_L. The common component has p tensor 1 in Q reduced at L-level, not P reduced only at E-level. The two sides both start at the genuine tensor complex Z and end at A_L(Q). Coefficient balancing uses the projection equation for c_L and the naturality of the finite structure maps for iota_m. Delta acts on both cone coordinates; both shifted coordinates are zero, so the argument proves equality of actual chain maps. No cone B(P) representing T_Y K is assumed K-flat. The full old generator calculation is preserved below, rather than blurred into a statement about projections.

Hypotheses for the parent assembly: K, G_E K and Lg_E^* K are derived complete as in the unchanged statement (isomorphism pullback constructibility is already a statement dependency). The finite-free comparison applies on both schemes. Normalization is an ambient derived-category assertion, so Step 3 can use the derived morphism chi_Y even when its target is a Roos cone that needs re-resolution. The new tensor lemma requires no completeness; the cone lemma assumes the parent's constructible K so that the existing specified-alpha model is in exactly its declared range. Universes and sites are inherited, not enlarged implicitly. The only off-unit proof input retained directly in the parent is normalization, declared as an existing generic tool use in split_report.

I tested g = identity, E = L, K = 0, the empty scheme, a free coefficient object in degree zero, and a two-term complex. The b formula becomes the usual tensor-unit formula; the shifted coordinate stays zero for both chain maps in every degree. For a ramified extension (e.g. uniformizers with varpi_E = unit times varpi_L^e, e > 1), the residue d_m need not be invertible and the statements do not require it. The whole-cone comparison is the existing specified-alpha assertion, not a spurious termwise-isomorphism claim. These tests expose no missing flatness or completeness assumption.

Against delivery-errors B–E: both new nodes introduce all objects, have definition dependencies and one-layer empty proofs, sources distinguish contextual literature from agent assertions, and searches were run and their results inspected. Every parent's non-elementary fact is a cited statement, not an external tag in prose; each citation's exact needed assertion was checked. No new node restates the derived square, no cyclic dependency on the parent was introduced, and the original route/statement were retained. I corrected the mechanically collected statement dependencies to exclude bracket notation [b_P] and [-1], which are mathematical notation rather than node references. There is no non-elementary parent step longer than 2000 characters, and the total parent proof text is below 3000. All eight returned arguments remain accounted for above and verbatim below.

## Unfinished work

The new nodes are intentionally statement-only: their independent proofs are work for subsequent workers. No stage-2/3 work or compiler checks were authorized or run. The requested repair itself consists of this split and its successful dry-run and push.

## Preserved returned proof, verbatim

### Old Step 1

The inverse-image equivalence for the scheme isomorphism is exact and commutes with all limits and colimits. The completed coefficient map used by the integral comparison is the map whose finite components satisfy π_m ∘ c_{O_E} = c^g_{A_{E,m}} ∘ g^{-1}(π_m), so it is compatible with every quotient transition. Hence the transported module functors G_E and G_L are exact on complexes and descend to the derived categories, while κ^{g,E} and κ^{g,L} are the specified maps of the comparison definition.

Cited nodes: lem-weil-proetale-isomorphism-inverse-image, def-weil-inverse-image-pullback-comparison.

### Old Step 2

Choose the K-flat representative P → K used to define the integral pullbacks. The inverse-image tensor comparison gives a chain-level map C_XG_EP → G_LC_YP by the pure-tensor rule y ⊗ a ↦ g^{-1}(y_0 ⊗ a_0), with the coefficient actions transported by c_E and c_L. The finite quotient maps commute with this rule, so it is a map of strict towers. Exactness of g^{-1} carries it through the localization and gives the derived isomorphism b_K : C_XG_EK → G_LC_YK.

Cited nodes: lem-pur-isomorphism-inverse-image-tensor-hom, lem-weil-proetale-isomorphism-inverse-image, def-weil-abstract-derived-category, lem-pc-kflat-resolution.

### Old Step 3

For every derived-complete $H$, the specified $\chi_{W,H}:C_WH\to T_WH$ is natural, independent of the K-flat resolution, and invertible. On a chosen resolution it is the quotient augmentation with zero shifted-product coordinate. Finite freeness of $S_W$ over $R_W$ means ordinary $C_W$ is termwise tensor on ANY complex; no K-flatness of a Roos cone is required to apply $C_W$. We will use naturality of this precise $\chi$ to replace $T_X(\kappa^{g,E}_K)$ by $C_X(\kappa^{g,E}_K)$ after conjugating by the two $\chi$ maps.

Cited nodes: lem-weil-finite-free-completed-scalar-comparison, def-weil-integral-scalar-extension.

### Old Step 4

Use $P\to K$ from Step 2 and the concrete flat-term K-flat $S_Y$-complex $Q=P\otimes_{R_{E,Y}}R_{L,Y}$; change of rings preserves K-flatness and flat terms. It represents $C_YK$, not the cone representing $T_YK$. The specified-map node defines $A_E(P)$, $A_L(Q)$, the same-index tower maps $d_m$ and their whole-cone map $\delta_P$. It gives $\alpha_K=Lg_L^*(\chi_{Y,K})[\delta_P]\chi_{X,Lg_E^*K}^{-1}$. The chain map $\chi_Y(P):Q\to B(P)$ has the correct direction and represents $\chi_{Y,K}$; application of $Lg_L^*$ is in the derived category. Thus we have an explicit representative of the canonical tensor-and-completion comparison, refining the existence assertion in the scalar-operation lemma.

Cited nodes: lem-weil-specified-pullback-comparison-alpha, lem-pur-integral-operations-scalar-extension, lem-pur-kflat-change-of-rings.

### Old Step 5

The definition β_K = G_L(χ_{Y,K}) ∘ b_K ∘ χ_{X,G_EK}^{-1} is a composite of the three displayed isomorphisms. Therefore β_K is an isomorphism in D(X_proet,O_L), and its source and target are exactly T_XG_EK and G_LT_YK by the definitions of C and T.

Cited nodes: lem-weil-finite-free-completed-scalar-comparison, lem-pur-isomorphism-inverse-image-tensor-hom, lem-weil-proetale-isomorphism-inverse-image.

### Old Step 6

We may compute the specified $\kappa^{g,L}_{C_YK}$ using $Q$ and move it along $\chi_{Y,K}$ to the specified $\kappa^{g,L}_{T_YK}$. The normalization lemma (applied with coefficient field $L$) gives $\theta_{g,N}\kappa^{g,L}_N=G_L(u_N)$ with $\theta_{g,N}$ an isomorphism, independent of the K-flat representative and natural for derived morphisms, and $u$ the natural completion unit. Hence $\kappa^{g,L}_N=\theta_{g,N}^{-1}G_L(u_N)$ is itself independent of the representative, and for a derived morphism $v:N\to N'$, $Lg_L^*(v)\kappa_N=\theta_{N'}^{-1}G_L(\widehat v)G_L(u_N)=\theta_{N'}^{-1}G_L(u_{N'})G_L(v)=\kappa_{N'}G_L(v)$. With $v=\chi_{Y,K}$ this gives the equality of actual derived maps
$$Lg_L^*(\chi_{Y,K})\,\kappa^{g,L}_{C_YK}=\kappa^{g,L}_{T_YK}\,G_L(\chi_{Y,K}).$$
Here $C_YK$ is derived complete by the finite-free comparison. Naturality is applied on the ambient completed-module derived category, so it also applies to the cone model $B(P)$ and to any fixed K-flat re-resolution used in the definition of $\kappa_{T_YK}$.

Cited nodes: lem-weil-isomorphism-derived-pullback-comparison-normalization, lem-weil-finite-free-completed-scalar-comparison.

### Old Step 7

Compute on the genuine tensor complex $Z=G_EP\otimes_{R_{E,X}}R_{L,X}$, representing $C_XG_EK$. The left chain map is $\delta_P\circ(C_X\tilde\theta^E_P)$ and the right is $\tilde\theta^L_Q\circ b_P$, both landing in $A_L(Q)$. Take a local tensor generator $y\otimes s$, with $y=g^{-1}p$ and $s=c_L(g^{-1}s_0)$. The $m$-component of the left augmentation first sends $y$ to $(g^{-1}(p\otimes1))\otimes1$ at E-level. The formula for $d_m$ sends its tensor with $s$ to
$$(g^{-1}(p\otimes1))\otimes\pi^L_m(s)\ \in g_{L,m}^*(Q_{L,m}).$$
The right route sends $y\otimes s$ by $b_P$ to $g^{-1}(p\otimes s_0)$, then reduces $Q$ and tensors with $1$. Balancing the sheaf tensor product moves $s_0$ to the last coefficient, giving exactly the same displayed element. Compatibility $\pi^L_m c_L=c^g_{A_{L,m}}g^{-1}(\pi^L_m)$ and functoriality of $c^g_A$ for $A_{E,m}\to A_{L,m}$ justify this balancing with the transported actions. The quotient maps commute with all transitions by their same-index definition. Both augmentations have shifted coordinate zero; $\delta_P$ applies $\prod d_m$ to BOTH coordinates and therefore sends that zero to zero. Thus the two chain maps to the entire cone coincide. After localization this is
$$[\delta_P]\,C_X(\kappa^{g,E}_K)=\kappa^{g,L}_{C_YK}\,b_K.$$
The identification of the last $\kappa$ with the $Q$-representative uses Step 6; it does not assert that the cone $B(P)$ is K-flat.

Cited nodes: lem-weil-specified-pullback-comparison-alpha, def-weil-inverse-image-pullback-comparison, lem-pur-isomorphism-inverse-image-tensor-hom, lem-weil-proetale-isomorphism-inverse-image, def-weil-integral-scalar-extension, def-weil-abstract-derived-category, lem-weil-isomorphism-derived-pullback-comparison-normalization.

### Old Step 8

Precompose the required square with the isomorphism $\chi_{X,G_EK}$. Naturality of $\chi$ and the formula of Step 4 give
$$\alpha_K T_X(\kappa^{g,E}_K)\chi_{X,G_EK}
= Lg_L^*(\chi_{Y,K})[\delta_P]C_X(\kappa^{g,E}_K).$$
By Steps 7 and 6 this equals
$$Lg_L^*(\chi_{Y,K})\kappa^{g,L}_{C_YK}b_K
=\kappa^{g,L}_{T_YK}G_L(\chi_{Y,K})b_K
=\kappa^{g,L}_{T_YK}\beta_K\chi_{X,G_EK}.$$
Cancel $\chi_{X,G_EK}$. These equalities take place in the localization of complexes; the only comparison inside a limit was already an equality of the entire cone maps in Step 7.

Cited nodes: lem-weil-finite-free-completed-scalar-comparison, lem-weil-specified-pullback-comparison-alpha, lem-weil-isomorphism-derived-pullback-comparison-normalization, def-weil-abstract-derived-category.
