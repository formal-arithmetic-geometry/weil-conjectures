# Worker report: Q19 repair of lem-trf-site-derived-tensor-restriction

## Files written

- `dag/nodes/sec-six-functors/lem-trf-site-derived-tensor-restriction.json`: existing statement unchanged byte for byte; four assembly steps, 2670 characters in their text.
- `dag/nodes/sec-six-functors/lem-trf-site-balanced-tensor-chain.json`: statement, unsplit; no Mathlib match. Explicit sheaf maps, balanced inverse formulas, chain naturality and compatibility with homotopies, for arbitrary unbounded P.
- `dag/nodes/sec-six-functors/lem-trf-site-one-sided-tensor-normalization.json`: statement, unsplit; no Mathlib match. Existence and uniqueness of the one-sided computation family normalized to the specified two-sided comparison, and its two naturality equations.
- `citations.json`: exact statement quotes for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log. Auxiliary `returned-proof.json` preserves the complete returned proof; neither auxiliary files nor scripts are repository changes.

## Attachments

None. The live `lean/Sheaf/Paper/SiteDerivedTensorRestriction.lean` has the exact target theorem `CategoryTheory.siteDerivedTensorRestriction` at line 306, ending in `sorry` at line 397. Searching the blueprint tag under `lean/WeilConjectures/` found no completed declaration of this item. The live statement and docstring were read, including `OneSidedTensorComparison` and `CanonicalOneSidedTensorComparison`: the normalization extracted here is exactly the equation that Lean currently demands. The ordinary relative-tensor-pullback declarations under WeilConjectures concern scheme ring maps and do not supply this arbitrary-site result with its normalized comparison family.

## WANTED

None. All mathematical sources used are present in literature/.

## What was wrong and what this repair changes

The human's 2026-10-21 return concerns workload, not the statement: the returned proof has seven steps and 6610 characters. The sandbox initially contained only dispatcher markers, with no node, report or prior search log. I therefore copied the current repository's returned split and read its review and Lean statement. No prior proof was invalidated by a missing delivery response. The item still states exactly the same proposition; all imported, provenance, Lean, reviewer and other maintainer-owned metadata are retained. This delivery deliberately re-splits the reviewed node as requested.

Two independent arguments become queue items of comparable size (1623 and 1954 statement characters). Both new nodes have `status: unsplit`, empty proof and proof_deps, and null proof_origin. Neither assumes the other or the item. The balanced chain node is underived and does not require K-flatness. The normalized computation node is over one arbitrary coefficient ring B and has no change-of-rings map or projection formula. The old item combines them with existing K-flat scalar extension and localization. This is not moving the entire theorem or a projection-formula clause to a new node.

## Argument allocation, with the returned arguments retained

Old step 1 is retained verbatim as assembly step 1. Old step 4 is assembly step 2, using the same three existing results: resolution, K-flat change of rings, derived scalar extension. Old step 7 remains assembly step 4, with the same localization proof (including the functor-category target, extension of the inverse, the identity composites and independence via Qp). No new node is created for these short applications of existing general interfaces.

Old steps 2 and 3 are assigned in full to `lem-trf-site-balanced-tensor-chain`. Its self-contained statement requires both explicit inverse maps as sheaf maps, their compatibility with differential, naturality, and homotopy naturality. The precise argument handed to its future worker is the returned argument below; it is not placed in the new node's statement or proof fields.

### Returned step 2, assigned to balanced chains

For an $\mathcal R$-module sheaf $M$ and an $\mathcal S$-module sheaf $N$, construct inverse maps $a_{M,N}:M\otimes_{\mathcal R}\operatorname{Res}_\varphi N\to\operatorname{Res}_\varphi((M\otimes_{\mathcal R}\mathcal S)\otimes_{\mathcal S}N)$ and $b_{M,N}$ by $x\otimes n\mapsto(x\otimes1)\otimes n$ and $(x\otimes s)\otimes n\mapsto x\otimes sn$. These formulas are first applied to local tensor generators, not to an identification of sheaf-tensor sections with tensor products of sections. Additivity is immediate. The first formula is $\mathcal R$-balanced since $(rx\otimes1)\otimes n=(x\otimes\varphi(r))\otimes n=(x\otimes1)\otimes\varphi(r)n$. The second respects the inner relation $(rx\otimes s)=(x\otimes\varphi(r)s)$ and the outer relation $(x\otimes st)\otimes n=(x\otimes s)\otimes tn$. For $b$, the target $M\otimes_{\mathcal R}\operatorname{Res}_\varphi N$ is a sheaf of $\mathcal S$-modules through $N$: the presheaf tensor $U\mapsto M(U)\otimes_{\mathcal R(U)}N(U)$ is a presheaf of $\mathcal S$-modules, and by [lem-pc-sites-module-sheafification-interface] its $\mathcal S$-module sheafification and its $\mathcal R$-module sheafification have the same underlying abelian sheaf; so the second formula is $\mathcal S$-bilinear into an $\mathcal S$-module sheaf, as bilinear extension over $\mathcal S$ requires. The module sheafification universal property [lem-pc-sites-module-sheafification-interface] and bilinear extension [lem-pc-sites-module-sheafification-bilinear-extension], together with the tensor definition [def-pur-sheaf-tensor-product], therefore give sheaf maps. Their composites are identities on local tensor generators, hence on the sheaves by uniqueness in those universal properties. Both formulas commute with restriction and with module maps; this proves simultaneous naturality.

Original citations: def-pur-sheaf-tensor-product, lem-pc-sites-module-sheafification-interface, lem-pc-sites-module-sheafification-bilinear-extension.

### Returned step 3, assigned to balanced chains

Apply step 2 with $M=P^i$ in every degree and $N$ in degree zero. Naturality with respect to $d_P^i$ gives a chain isomorphism $a_{P,N}$ with exactly the forward and inverse formulas in the statement. The differential is $d_P\otimes1$ on both sides, since $N$ has only degree zero [def-pc-tensor-complex-sheaves]. For a chain map $u:P\to P'$ and an $\mathcal S$-linear map $v:N\to N'$, the two composites in the naturality square both send $x\otimes n$ to $(u(x)\otimes1)\otimes v(n)$. A chain homotopy in $u$ is carried to the corresponding tensor homotopy by the same degreewise formula, so this naturality also holds in the homotopy category.

Original citations: def-pc-tensor-complex-sheaves.

Old steps 5 and 6 are assigned to `lem-trf-site-one-sided-tensor-normalization`. Its statement includes preservation of quasi-isomorphisms in both orders, the one-sided comparison with arbitrary unresolved M, its prescribed normalization to the existing two-sided descent, and naturality in the K-flat argument. In particular it retains the sign check and the uniqueness argument, rather than replacing either with an unspecified isomorphism. This argument is retained verbatim below. Assembly step 3 instantiates this one-ring result separately over R and over S, and then inserts the balanced chain map.

### Returned step 5, assigned to normalized one-sided computation

For a K-flat complex $T$ on either coefficient site, tensoring with $T$ preserves quasi-isomorphisms: if $s$ is a quasi-isomorphism, its cone is acyclic by [lem-pur-quasi-iso-cone-acyclic]; K-flatness [def-pc-kflat-complex] makes its tensor with $T$ acyclic; the cone identification [lem-pc-tensor-mapping-cone-iso] then shows that $1_T\otimes s$ is a quasi-isomorphism. Interchanging the factors uses the symmetry from [lem-pc-sheaf-modules-tensor-closed], with graded sign $(-1)^{ij}$ in total degree $(i,j)$; this sign identifies the two differentials $d_T\otimes1+(-1)^i1\otimes d$ and $d\otimes1+(-1)^j1\otimes d_T$. This gives either tensor order without a flatness assumption on the other complex.

Original citations: lem-pur-quasi-iso-cone-acyclic, def-pc-kflat-complex, lem-pc-tensor-mapping-cone-iso, lem-pc-sheaf-modules-tensor-closed.

### Returned step 6, assigned to normalized one-sided computation

For K-flat flat-term $T$ over a coefficient ring sheaf $B$ and an arbitrary complex $M$, $Q_B\operatorname{Tot}(T\otimes_B M)$ canonically computes $Q_BT\otimes_B^{\mathbf L}Q_BM$. To see this precisely, tensor with $T$ descends in $M$ by step 5 and [lem-weil-pbc-localization-universal-property]. On the K-flat flat-term subcategory its comparison with derived tensor is the canonical natural comparison in [lem-weil-pbc-site-derived-tensor-descent]. That subcategory localized at its quasi-isomorphisms is $D(B)$ by the same node; hence the comparison extends uniquely to all $M$ by the localization universal property. For a map $T\to T'$, the naturality square agrees on K-flat flat-term $M$, so uniqueness gives the square for every $M$. In particular, using $T=P$, $M=\operatorname{Res}_\varphi N$, and then $T=P_{\mathcal S}$, $M=N$, proves that the two complexes in step 3 compute respectively the left and right derived objects in the statement, after the exact restriction of step 1. The identification of $Q_{\mathcal S}P_{\mathcal S}$ with the inner scalar extension is step 4.

Original citations: lem-weil-pbc-localization-universal-property, lem-weil-pbc-site-derived-tensor-descent.

For completeness, the original assembly argument of step 7 is also retained here, so its resolution-independence reasoning is available verbatim beside the shorter assembly:

Let $\mathcal P_{\mathcal R}$ be the homotopy subcategory of K-flat flat-term complexes. Regard both sides of the desired identity as functors of $H$ with values in the category of functors from $\operatorname{Mod}(\mathcal S)$ to $D(\mathcal R)$. Steps 3 and 6 give a natural isomorphism between their restrictions along $Q_{\mathcal R}|_{\mathcal P_{\mathcal R}}$. By [lem-weil-pbc-site-derived-tensor-descent], this restriction is a localization at the quasi-isomorphisms. Apply clause (2) of [lem-weil-pbc-localization-universal-property], with that functor category as target: the isomorphism and its inverse extend uniquely, their composites extending the identities. The result is therefore natural simultaneously in $H$ and the degree-zero sheaf $N$. For a specified resolution $p:P\to C$, naturality along $Qp$ expresses its component as the chain map $a_{P,N}$ under the canonical computation isomorphisms of steps 4 and 6. Uniqueness shows that any other resolution gives the same component; no direct chain map between the two resolutions is needed. Only the existence of unbounded K-flat resolutions and their preservation under change of rings were used, so no boundedness, finite Tor amplitude, or flatness of the coefficient map is required.

## Review by Q19

I read the current blueprint `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-lem-sf-kunneth-star/lem-trf-ordinary-kunneth.proof.md`, specifically Step 2's P tensor_A Q = (P tensor_A kappa) tensor_kappa Q, together with the chapter and unit records. This is the same coefficient-transport route as before. The new statements supply its underived balanced chain calculation and its canonical unbounded derived interpretation. They do not substitute a geometric base-change or projection-formula theorem.

For the balanced-chain node I read Stacks `sites-modules.tex`, Tag 03EK (`section-tensor-product`), its presheaf/sheaf tensor definitions and bilinear characterization, and Tag 03CY (`lemma-sheafification-presheaf-modules`). The tensor is sheafified, so one cannot silently equate sections with tensor products of sections. The old proof's extra S-action sentence is preserved: the inverse first has its S-bilinear target through N, and the two coefficient sheafifications have the same underlying abelian sheaf. The two balancing relations and both inverse identities are explicitly in the argument allocation above. Applying them to each degree commutes with d_P; since N is in degree zero there is no extra differential, and the tensor of a homotopy has degree minus one as required. This is a construction and normalization task, not simply the existential ordinary cancellation theorem already in the DAG.

For the one-sided-normalization node I read Stacks `sites-cohomology.tex`, Tag 06YP (`lemma-K-flat-quasi-isomorphism`), Tag 06YS (`lemma-K-flat-resolution`), Tag 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`), and the construction preceding Tag 06YU (`definition-derived-tor`). The retained cone proof uses the acyclic-cone and tensor-cone nodes, not merely the definition of K-flatness; the order switch is the Koszul symmetry with (-1)^(ij). The resolving-subcategory equivalence and its canonical two-sided comparison are exactly what `lem-weil-pbc-site-derived-tensor-descent` states. Extending that specified comparison in the arbitrary second factor by localization proves existence and uniqueness of c. To get naturality in T, compare the two transformations on resolving second arguments and use full faithfulness of localization; the report retains that argument verbatim. For uniqueness one may also choose a flat-term K-flat resolution V to M and cancel the invertible Q(1_T tensor (V to M)); normalization and naturality then determine c(T,M). Thus the new node asks for a specified coherent family, not an arbitrary computation isomorphism.

I checked all four assembly steps against every cited statement, not their proofs. Step 1 cites `def-pc-sheaf-restrict-scalars`, which leaves the underlying abelian sheaf unchanged, and `lem-weil-pbc-module-sheaves-colimits-forgetful`, whose clauses (1) and (3) give exact faithful forgetful functors and common kernels, cokernels and sums for each of R and S. These give exact restriction; faithfulness detects zero cohomology. `def-weil-abstract-derived-category` then supplies localization at quasi-isomorphisms, hence derived restriction. The site is small in the module universe, so all these module sheafifications and small sums exist. This step is elementary relative to those statements, not an uncited claim that scalar restriction is exact.

Step 2 uses the actual full statements of `lem-pc-kflat-resolution`, `lem-pur-kflat-change-of-rings`, and `lem-pur-derived-change-of-rings`. The first gives unbounded K-flat resolutions with flat terms; the second needs exactly K-flatness and termwise flatness of P, which we have, and does not require S to be R-flat; the third computes the S-valued derived extension on that P, including its canonical independence and compatibility. I also read Stacks 0G7E (`lemma-pullback-K-flat`) and 06YY (`lemma-derived-base-change`) for this identity-topos application. No restriction of K-flat S-complexes to R is claimed.

Step 3 uses both new statements exactly. The first gives the chain map and its inverse with the generator formulas the item asks for. The second applies first with B=R,T=P,M=UN[0], then with B=S,T=P_S,M=N[0]. Step 2 supplies the K-flat/flat-term hypothesis on P_S; N and UN need no such hypothesis. Its comparison orientation is derived tensor to localized total tensor; conjugating the chain isomorphism therefore uses c_R first and the inverse of c_S on the right. Step 1 permits restriction of that second comparison to D(R). These are the comparisons appearing in the existing Lean statement, including its normalization to the existing descent, so an arbitrary isomorphism cannot be substituted.

Step 4 uses the localization clause of `lem-weil-pbc-site-derived-tensor-descent` and clause (2) of `lem-weil-pbc-localization-universal-property`, whose statement explicitly permits any target category and extends natural transformations as well as inverses, preserving composition. The target is the functor category from S-module sheaves to D(R), in the chosen larger universe. Thus extending the inverse and identity composites is licensed by the cited statements, and naturality is simultaneous in H and N. Naturality along Qp gives the prescribed representative and uniqueness gives resolution independence. None of these facts is taken from a cited node's proof. `citations.json` copies the actual statements for every occurrence.

I tested identity coefficient maps, S=0, N=0 and P=0: all formulas become the usual unit/cancellation maps or zero maps. The empty site has the same unique maps and causes no generator or final-object assumption. On the one-point site with Z to F_p, no flatness of the ring map is available but a K-flat free resolution computes the formula. On Z/4 to F_2, the unbounded resolution and its infinitely many possible Tor groups are allowed; the one-sided computation leaves the arbitrary factor unresolved, so there is no hidden finite-Tor or boundedness assumption. In the normalization lemma T=B[0] reduces to the unit comparison; arbitrary acyclic M tensors acyclically with T, and quasi-isomorphic resolutions give the same component by the stated naturality. No small-case counterexample or source error was found.

The B-to-E return checklist was checked in substance: both new claims introduce their own sites, rings, module categories and complexes and cite their definitions; neither has proof text masquerading as a statement. Sources are local Stacks tags with labels. Mathlib searches are exact msearch-command queries, with real returned declarations recorded; no unavailable service was recorded as absence. All non-elementary assembly steps cite theorem nodes giving the required claim. New statements contain no circular reference to the item, and their statement dependencies do not depend on the item. The four assembly steps have lengths below 2000 individually, and the total is 2670, below 3000. No SGA source is used. No Lean or compiler/Lake/build command was run. Only the authorized sandbox was written.

## Searches and reuse

The whole DAG was searched by balanced tensor, scalar restriction, one-sided/K-flat computation, source tags and relevant declaration concepts, and blueprint_refs.py was run for ancestor and the searches `balanced tensor`, `K-flat computation`, `restriction of scalars`, `one-sided tensor`, `K-flat representative`, `balanced chain`, `tensor cancellation`, `one-sided`, and `canonical computation`. The nearest blueprint ancestor is lem-trf-ordinary-kunneth. The new blueprint.from.via contains the item; same_as is empty because none of the blueprint statements gives either normalized interface.

Mathlib search results were read as returned. Loogle's tensor/restrictScalars hits are scalar-tower identities on ordinary modules, and its KFlat query returns only Lean.mkFlatCtorOfStructCtorName, which is unrelated. LeanSearch's ordinary extension associators and TensorProduct.AlgebraTensorModule.assoc/cancelBaseChange give algebraic section-level identities, not the sheafified normalized chain family. The grep hits in ModuleCat.ChangeOfRings and Descent are ordinary scalar extension and flat descent. LeanFinder returns presheaf tensor, free pullback and total-tensor existence declarations; these do not assert the new statements. Mathlib/CategoryTheory/Monoidal/Tor.lean was read: it defines nth projective left-derived Tor of objects, not unbounded K-flat sheaf-derived tensor or the normalized comparison. The Homology grep for KFlat/kflat gives no hits. Two semantic phrasings were tried for each proposed node. All queries are retained literally in the new nodes and searches.jsonl.

Existing ordinary cancellation is reused conceptually rather than reintroduced as a new existential module lemma: `lem-pur-change-of-rings-tensor-cancellation` and its independent-universe version supply an unnormalized ordinary natural isomorphism. The new chain node additionally pins both inverse maps to the specified local generator formulas and supplies compatibility with homotopies for arbitrary complexes. `lem-weil-pbc-kflat-fixed-tensor-triangulated` already supplies preservation and exact derived fixed-tensor functors; it does not state uniqueness of the joint c(T,M) family normalized to the specified two-sided comparison or the displayed equations with that same comparison. That normalization argument is the independent work assigned to the second new node. The derived-descent node is retained as a statement dependency and in the assembly; it gives the comparison only when both arguments are resolving objects, so does not on its own provide c for arbitrary M.

## Not duplicates

lem-trf-site-balanced-tensor-chain vs lem-pe-internal-section-tensor-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Relative tensor and K-flatness under the internal-to-sectionwise module equivalence, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sf-completed-tensor-finite-shift: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Signed right shifts of the strict finite tensor tower, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-zl-pbc-finite-raw-scalar-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Canonical comparison of normalized and embedding finite-field scalar extension, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-trf-singleton-site-operations: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Punctual ringed-site operations and normalized comparison predicates, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sc-hom-tensor-comparison-natural: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Naturality of the sheaf tensor comparison isomorphism, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sc-hom-tensor-summand-restriction-ext: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Internal Hom maps determined by total tensor summand restrictions, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sc-internal-hom-coproduct-fan: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Internal Hom of a coproduct is a product, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pc-sheaf-modules-tensor-closed: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Sheaves of modules on a site form a symmetric monoidal closed category, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sc-hom-tensor-section-natural: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Naturality of the canonical presheaf-to-sheaf tensor map, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sc-hom-tensor-summand-localized-ext: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Localized pure-tensor extensionality for a sheaf tensor, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pc-sites-sheaf-tensor-bilinear-universal: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Universal property of sheaf tensor product, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sc-internal-hom-product-fan: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Internal Hom preserves integer-indexed product fans, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sc-hom-tensor-reverse-pair: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Reverse currying for one pair of module sheaves, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sfb-scalar-inverse-image-tower-diagram: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Ordinary inverse-image and balanced scalar-tower square, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sfb-proetale-intrinsic-tensor-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Right-tensor comparison for intrinsic constant-ring realization, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sfb-internal-section-scalar-adjunction: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Scalar adjunction transport between internal and sectionwise module sheaves, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sfb-internal-scalar-extension-section-test: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Internal scalar-extension flatness tested on sectionwise module sheaves, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-sfb-internal-section-total-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Canonical internal-to-sectionwise total-complex comparison, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-weil-pbc-continuous-module-encoding-scalar-extension: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Scalar extension under the continuous integral and rational module encodings, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-weil-pbc-scalar-localization-complex-colimit: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Ordinary scalar-sequence colimit of complexes, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs adic-unit-exists-data: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Existence of the identity scalar-extension unit map, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-weil-pbc-ringed-tensor-section-calculus: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Section calculus for the actual sheaf tensor and scalar extension, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-weil-pbc-scalar-localization-module-colimit: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Scalar localization as an ordinary module-sheaf colimit, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-weil-pbc-tensor-local-bijection-universes: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Tensoring a local module bijection commutes with sheafification in independent universes, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-w2-inverse-image-change-of-rings-unit-smul: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Scalar compatibility of the inverse-image change-of-rings unit, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-weil-pbc-extension-tensor-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Restricted scalar extension as a sheaf tensor product, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-weil-pbc-continuous-module-encoding-lattices: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Local freeness and lattice compatibility of the explicit continuous encodings, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-weil-pbc-flat-scalar-restriction-kflat: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Flat scalar restriction preserves K-flat complexes, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-weil-pbc-common-quotient-tower-presentation: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Common-quotient tower presentations and local ideal-product membership, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-weil-pbc-scalar-tensor-comparison-universes: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Scalar-extension tensor associativity on underlying abelian sheaves in independent universes, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-pur-kummer-module-coefficients: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Kummer sheaves with module coefficients and their scalar actions, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-pur-sheaf-tensor-product: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Tensor product of sheaves of modules on a site, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-system-ordinary-tensor-reduction: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Ordinary scalar-adjoint tensor formula for strict systems, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-kun-prime-coefficient-functors: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Punctual tensor source and target functors, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-constant-finite-free-section-basis: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Compatible sectionwise bases of constant coefficient extensions, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-sp-semilinear-constant-ring-operations: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Constant-ring semilinear system operations and normalized evaluation mates, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sp-scalar-extension-dual-local-iso: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Local rank-one scalar extension and dual invertibility, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-kummer-finite-biproducts: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Integral finite-basis cohomology and Kummer exactness, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-kun-prime-coefficient-complexes: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Degree zero complexes and localization, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-proetale-inverse-image-tensor-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Pure-tensor description and coherence of the pro-etale inverse-image tensor comparison, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-pur-finite-tate-site-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Finite Tate tensor generators and root-normalized site comparison predicates, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sp-scalar-extension-binary-coherence: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Normalized binary scalar-extension comparisons, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-module-tensor-monoidal-equations: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Associativity and symmetry of the canonical ordinary module tensor comparison, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-kun-prime-coefficient-complexes-input-output: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Ordinary source and target tensor complexes, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-weil-sheaf-scalar-extension-ring-iso: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Scalar extension along an isomorphism of ring sheaves, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-kun-prime-coefficient-constructions: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Canonical quotient coefficient tensor arrow, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-twist-coefficient-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states The canonical coefficient pushout comparison is invertible, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-change-of-rings-tensor-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Natural comparison of restricted scalar extension and sheaf tensor, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-constant-finite-free-power-iso: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Finite-basis coordinates for constant scalar extension, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-etale-constant-module-tensor: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Constant-coefficient realization commutes naturally with right tensor, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sp-finite-free-scalar-models: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Existence of normalized actual-restriction scalar models, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-kun-prime-coefficient-normalization: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Derived normalization by the quotient tensor map, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-kun-prime-coefficient-iso: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Derived coefficient tensor isomorphism type, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-twist-coefficient-tensor: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Finite integral coefficient extension commutes with sheafwise completion, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-kun-prime-coefficient-term-map: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Degree zero coefficient term map, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-change-of-rings-tensor-cancellation-independent: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Natural tensor cancellation in independent coefficient universes, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-twist-integral-local-models: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Scalar-extension local models of the integral root line, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-kun-prime-coefficient-localization-compatibility: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Localized termwise coefficient compatibility, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-pur-twist-coefficient-rings: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states The canonical discrete and completed scalar square of the Tate twist, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-tensor-pushout-action: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states A sectionwise scalar pushout acts uniquely on a balanced tensor sheaf, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-sp-scalar-tensor-comparison-data: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Normalized tensor and scalar-extension comparison data, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-inverse-image-tensor-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states The unit-normalized tensor comparison for an isomorphic base change, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-kummer-integral-root-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Integral basis reduction for the Kummer root sheaf, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-module-tensor-generator-calculus: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Pure tensors and normalized insertion naturality for sheaf modules, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-inverse-image-scalar-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Inverse image commutes with extension of scalars, with its unit formula, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sp-scalar-extension-dual-evaluation: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Explicit scalar-extension evaluation on internal duals, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-pur-presheaf-tensor-product: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Presheaf tensor product of modules, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-kun-prime-coefficient-termwise-normalization: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Termwise normalization of the quotient tensor arrow, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-compatible-coefficient-tower: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Compatible coefficient maps give a linear strict tensor tower, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-system-cochain-tensor-reduction: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Cochain scalar-adjoint tensor formula for strict systems, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-kun-prime-coefficient-pullbacks: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Canonical coefficient pullback maps, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-weil-point-sections-tensor-shift: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Sections-tensor comparison commutes with shifts, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-sp-scalar-extension-dual-tower-core: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Dual comparisons and binary scalar-extension tower squares, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-change-of-rings-tensor-cancellation: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Natural cancellation of scalar extension in sheaf tensors, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-kummer-finite-free-comparison: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Normalized finite free Kummer cohomology comparison, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-pur-inverse-image-tensor-hom-sections: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Tensor, scalar and unit-section conventions for module inverse image, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-etale-constant-module-flat: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Flatness under constant-scalar realization, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-pur-operation-scalar-transport: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Pure-tensor and derived-counit normalized operation scalar transport, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-constant-finite-free-products: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Countable products and finite-free constant scalar extension, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-pd-proetale-section-module-functors: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Normalized tensor structures on existing pro-etale section-module functors, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pd-ringed-direct-image-pairing-lax: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Normalized lax tensor pairing for ringed direct image, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs def-pd-section-module-operations-data: new node specifies the normalized balanced chain isomorphism and both local-generator inverse formulas, compatible with homotopies; existing node states Existing section-module operations and pure-tensor data, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-weil-pbc-ringed-tensor-cohomological-bounds: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Cohomological bounds for derived extension of ring-sheaf scalars, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-exc-intrinsic-resolution-tensor-homology: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Tensor cohomology in the intrinsic coefficient presentation, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sf-finite-comparisons-existence: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Section preserving finite comparisons exist, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sf-finite-compatibility-transport: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Pinned finite comparisons preserve canonical open arrows, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sf-open-tensor-support: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived tensor preserves open support in either factor, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-exc-intrinsic-tor-amplitude-transport: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Transport of intrinsic Tor intervals, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sf-finite-operation-comparisons: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Prescribed finite realizations admit pinned operation comparisons, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sf-open-tensor-support-aux: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states The open tensor projection transpose is invertible, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-weil-proetale-derived-restriction-closed-monoidal: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Normalized native pro-etale restriction is braided closed monoidal, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-sf-open-normalization-data: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Geometric and operation data for open tensor normalization, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-trf-ringed-complex-derived-tensor-vanishing: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived tensor cohomology vanishing for a complex on a ringed site, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-pc-derived-tensor-cohomology-vanishes: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Vanishing of derived tensor cohomology with an O_X-module, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sc-source-kflat-tensor-left-triangulated: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived tensor by a K-flat homotopy model is triangulated, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-sc-derived-tensor-augmentation: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived tensor augmentation on a scheme, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-pc-derived-tensor-complex-cohomology-vanishes: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Vanishing of derived tensor cohomology of two derived objects, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-geo-cartier-coeff-extension: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived scalar extension of a closed supported constant sheaf, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-sfb-ringed-projection-coherence-data: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Recorded data for tensor projection coherence, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sfb-divisible-extension-derived-reduction: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived reduction of an extension by a divisible sheaf, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sfb-flat-scalar-cyclic-resolution: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Two-term scalar quotient resolutions after flat sheaf extension, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-geo-cartier-exponent-independence: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Modulus change of the derived quotient and torsion identifications, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sfb-ringed-projection-tensor-structure: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Canonical tensor structure in arbitrary recorded presentations, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sfb-ringed-projection-pullback-comparisons: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Normalized identity, composition and section pullback comparisons, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-sfb-ringed-projection-tensor-compatibility: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Tensor constraints and compatibility of normalized comparisons, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-weil-pbc-ringed-projection-mate-exact: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Exactness data for the ringed-topos projection mate, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-weil-pbc-completed-constant-resolution-tensor-calculation: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Tensor quotient diagrams on finite-free completion resolutions, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-weil-pbc-completed-constant-realization-data: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Completed constant realization interfaces, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-weil-pbc-site-derived-tensor-descent: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived tensor and K-flat representative descent on a ringed site, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-weil-pbc-completed-constant-derived-tensor-tower: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Universal derived tensor tower from K-flat resolutions, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-weil-pbc-kflat-fixed-tensor-triangulated: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Exact descent of tensoring with a fixed K-flat complex, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-pur-etale-single-functor-monoidal-compatibility: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Canonical flat degree-zero tensor pairings and exact inverse image, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-kun-prime-coefficient-functors: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Punctual tensor source and target functors, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-kun-prime-coefficient-complexes: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Degree zero complexes and localization, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-pur-line-unbounded-derived-tensor: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived tensor by a locally free line is the exact termwise equivalence, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-kun-prime-coefficient-complexes-input-output: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Ordinary source and target tensor complexes, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-kun-prime-coefficient-constructions: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Canonical quotient coefficient tensor arrow, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-pur-derived-change-of-rings: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived change of rings along a morphism of sheaves of rings, computed by K-flat resolutions, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-pur-integral-operation-shift-data: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Representative-normalized operation and independent-slot shifts, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-kun-prime-coefficient-normalization: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived normalization by the quotient tensor map, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-amb-derived-tensor-symmetry-involutive: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Opposite canonical derived tensor symmetries cancel, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-kun-prime-coefficient-iso: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived coefficient tensor isomorphism type, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-kun-prime-coefficient-term-map: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Degree zero coefficient term map, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-kun-prime-coefficient-localization-compatibility: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Localized termwise coefficient compatibility, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-kun-prime-coefficient-termwise-normalization: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Termwise normalization of the quotient tensor arrow, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-kun-derived-tensor-well-defined: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Independence of the K-flat model, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-kun-prime-coefficient-pullbacks: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Canonical coefficient pullback maps, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-asd-derived-pullback-symmetry: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Derived pullback preserves canonical tensor symmetry, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-pur-kflat-cone-comparison: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Two K-flat resolutions: augmentation square computing the derived-to-ordinary tensor comparison, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-pur-synchronized-canonical-maps: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states The same canonical map at two independent input families, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs lem-pur-varying-ring-tensor-support: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Tensor support for canonical varying-ring extension, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-pd-section-derived-realization: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Canonical derived section-module realization, rather than that normalized family.

lem-trf-site-one-sided-tensor-normalization vs def-pd-section-derived-tensor-data: new node specifies the unique joint one-sided family c(T,M), natural in arbitrary M and normalized to the fixed two-sided delta; existing node states Canonical derived section-module tensor data, rather than that normalized family.

lem-trf-site-balanced-tensor-chain vs lem-pur-change-of-rings-tensor-cancellation: ordinary natural sheaf isomorphism only; new node pins both local-generator maps, extends to arbitrary cochains and requires homotopy compatibility.

lem-trf-site-balanced-tensor-chain vs lem-pur-change-of-rings-tensor-cancellation-independent: ordinary cancellation for independent universes; no specified chain or homotopy family.

lem-trf-site-balanced-tensor-chain vs lem-weil-pbc-scalar-tensor-comparison-universes: natural functors on modules, after forgetting to abelian sheaves, with no normalized chain/homotopy family.

lem-trf-site-balanced-tensor-chain vs lem-pc-relative-tensor-pullback-balanced-naturality: scheme pullback with R=f-inverse O_S and O_X rather than arbitrary ring sheaves on any site.

lem-trf-site-balanced-tensor-chain vs lem-pc-relative-tensor-pullback-complex-comparison: scheme ringed-space pullback, after forgetting to abelian sheaves; no arbitrary coefficient site or both local generator formulas.

lem-trf-site-one-sided-tensor-normalization vs lem-weil-pbc-kflat-fixed-tensor-triangulated: exact fixed-factor derived functors and shift/cone compatibility; new result specifies the unique c-family with normalization to the already fixed two-sided comparison and two displayed naturality equations.

lem-trf-site-one-sided-tensor-normalization vs lem-pur-kflat-total-tensor-model: both factors K-flat with flat terms, plus closure under total tensor; new node allows arbitrary unresolved M and pins normalization.

lem-trf-site-one-sided-tensor-normalization vs lem-pur-kflat-tensor-quasiiso-independent: quasi-isomorphism preservation only; no normalized comparison family with derived tensor.

lem-trf-site-one-sided-tensor-normalization vs lem-pc-tensor-counit-one-kflat-coordinates: scheme pullback counit equation for chosen tensor coordinates, not arbitrary-site uniqueness relative to a fixed two-sided descent comparison.

lem-trf-site-one-sided-tensor-normalization vs lem-pur-kflat-cone-comparison: two bounded-above augmented resolutions of degree-zero sheaves and their comparison square, not arbitrary unresolved unbounded M.

lem-trf-site-one-sided-tensor-normalization vs lem-pc-balanced-derived-tensor-model: one-point site and scalar-extension model, rather than the normalized family for every small site.

## Unfinished work

The proofs of the two new nodes are intentionally left to separate future stage-1 workers, as the human explicitly requested. Their complete inherited arguments are retained above for those workers. No part of this item's assembly is left unresolved. Independent maintainer review remains required after delivery.

## Validation

The required server-side `deliver.py Q19 lem-trf-site-derived-tensor-restriction --no-push` exited 0 and printed `OK (not pushed)` at `1f9dbdd591e`: preflight passed. The delivered report records that actual successful check. A final dry run is made after this report update, followed by the authorized direct delivery. No Lean compilation was requested or run.
