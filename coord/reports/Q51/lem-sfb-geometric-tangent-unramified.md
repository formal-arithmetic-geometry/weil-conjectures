# Worker report: Q51, lem-sfb-geometric-tangent-unramified

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-geometric-tangent-unramified.json: repaired parent split, original statement kept exactly; 1592 characters of proof text.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-point-tangent-unramified.json: statement, unsplit, no Mathlib match; local rational-section and tangent/cotangent argument.
- dag/nodes/sec-six-functors-basics/lem-sfb-unramified-geometric-point-test.json: statement, unsplit, no Mathlib match; source-point lifting and geometric-fibre unramifiedness test.
- citations.json: whole statements copied verbatim for each citation of each parent step.
- searches.jsonl: actual msearch records; returned-proof.json: read-only input proof preserved as a sandbox handoff artifact.

## Attachments

None. I searched lean/WeilConjectures for the blueprint id and the notions of tangent/unramified and rational/geometric unramifiedness. There is no project declaration giving this criterion. The landed Sheaf.AlgebraicGeometry.GeometricTangentUnramified theorem unramified_iff_geometricFiber_tangentSpace_zero ends in sorry and is not an attachment. Its statement matches the retained parent statement, including relative Omega-scheme lifts. No Lean file was written and no compiler was run.

## Wanted literature

None. All sources used are available in literature/stacks-project/.

## Faults and repair of the return

The only numbered issue in this return is the batch5 human re-split request: 4204 characters spread over six steps were too much work for one node. I did not replace that argument by a shorter unexplained argument. Old Steps 1--2 now belong to lem-sfb-rational-point-tangent-unramified and old Steps 3--5 to lem-sfb-unramified-geometric-point-test. Both new nodes are statement-only, status unsplit, with empty proof/proof_deps and null proof_origin. Their mathematical workloads are respectively the rational section and local linear-dual calculation (1392 old characters), and the base-change/source-point lifting argument (2134 old characters); neither restates the whole parent. The old Step 6 remains explicitly in the parent, together with its residue-field citation. The assembly is 1592 characters, below 3000. The preserved paragraphs below are the proof handoffs for future workers, rather than proofs inserted into the new nodes.

The sandbox initially contained only dispatcher .brief files, no node, report, or search log. Thus I copied the current read-only repository node, which contains the returned six-step split. There was no prior sandbox proof/report/log to overwrite or discard. The inherited parent search records and all its metadata are retained. Delivery rebases the owned stage-1 fields on the current server state. No git command was run in the shared repository.

No new statement dispute was found. In particular the already-corrected parent formulation says morphisms of Omega-schemes; it must stay relative. The inherited review records the older unrestricted-reading counterexample: for Omega an algebraic closure of Q(t), a derivation extending d/dt gives a nonconstant ordinary dual-number morphism even for the identity scheme. Requiring Omega-linearity removes it. This repair changes no statement or Lean signature.

The inherited chapter is sec-six-functors-basics while unit sk-thm-sf-ctf-stability is recorded under sec-six-functors; both are retained. blueprint_refs.py ancestor returns None for this item. Its existing blueprint.from.node is null, so both new nodes preserve that reported ancestor and prepend this item to its full inherited via chain. The precise place is the inherited stable pointed Isom rigidity input under det-thm-sf-ctf-stability-direct-images, proof (3). I did not invent a new ancestor or alter the unit route.

## Search record and boundaries

Before creating nodes I searched all dag/nodes for tags 0B2G, 0B2E, 0B2F, 0475, 01J9 and for tangent/unramified and geometric-point test statements; I opened every same-source statement listed below. I ran tools/blueprint_refs.py search for unramified, tangent, cotangent, 0475 and 0B2G across the entire imported blueprint. None states either new result. same_as is [] for both and for the parent. Searching the two proposed ids in dag/nodes and both Lean source roots found no collision. I read the existing rational tangent duality, dual-map criterion, rational cotangent criterion, lft base-change and unramified-locus statements. They remain reusable inputs for the unsplit tasks; I did not create copies of those results.

Twelve msearch commands actually ran, six assigned to each new node: two differently phrased LeanFinder questions, one Loogle query, two source greps, and one LeanSearch question. Both LeanSearch calls reported HTTP rate limiting and are recorded as unavailable. Loogle executed successfully with zero hits. LeanFinder's returned declarations concern FormallyUnramified, its affine-local characterization, IsEtale implying formal unramifiedness, the affine unramified locus and its openness, and preservation under composition. I read their printed types and the source of Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean, especially the affine-local class and the base-change instance. They do not identify a scheme tangent space at a section with a dual cotangent space, or construct geometric-fibre sections over arbitrary source points and use them to detect the global unramified locus. Neither new node is an exact match or one-line specialization. The file-specific msearch grep returned malformed path/line columns because rg omits filenames for a single file; that actual output is recorded without alteration, and I read the file directly. The substantive first source grep for the geometric test gave the base-change instance at line 121, which supplies only stability, not reflection at every geometric test point. No Mathlib leaf is claimed. All query strings and digests in new nodes come directly from searches.jsonl; no searches were invented.

The specific re-split instruction requires spreading this existing argument. The local criterion is a reusable lemma about one field and one rational section, not a clause of the global geometric-fibre theorem. The geometric test contains no tangent space or dual number assertion. It requires the rational lifts covering all source points as well as locus base-change. A reader may work on either task independently. The elementary rational-point preliminaries are packaged with the substantive local calculation, not made a third elementary node. The two new nodes do not cite the parent, so there is no circular dependency.

## Review by Q51

I read varieties.tex definition-dual-numbers (0B29), lemma-tangent-space (0B2B), definition-tangent-space (0B2C), lemma-tangent-space-rational-point (0B2E), lemma-map-tangent-spaces (0B2F), and lemma-injective-tangent-spaces-unramified (0B2G). I read morphisms.tex definition-unramified (02G4) and lemma-set-points-where-fibres-unramified (0475), and schemes.tex lemma-characterize-points (01J9), checking these labels in tags/tags. These justify the parent's unchanged statement and both smaller tasks. In 0B2G the hypothesis is local finite type and equality of the two residue fields; for the structure map of the first new node the target is Spec k and the section forces that equality. Neither source calls for flatness or a Noetherian base. In 0475 the first clause explicitly commutes with arbitrary base change under only local finite type; local finite presentation is needed only for the separate G-unramified variant, which is not used here.

Parent Step 1 reads lem-weil-pbc-lft-base-change, whose statement gives exactly local finite type of the second projection after arbitrary base change. The new rational-point node supplies both the residue-field identification/closedness and the equivalence between tangent vanishing and unramifiedness at that point. The other new node explicitly quantifies exactly these sections of the geometric-fibre projection. Thus Step 1's substitution is valid for every Omega and s in the parent; no assumption that every point of a fixed geometric fibre is rational is made. All three cited statements are quoted verbatim in citations.json.

Parent Step 2 uses only lem-sfb-unramified-geometric-point-test. Its statement is the needed iff for the entire family of local conditions and explicitly includes lifts over an algebraic closure of kappa(z). I checked that an arbitrary geometric point Spec Omega to S is allowed in the parent, rather than only a chosen algebraic closure of kappa(s). This is essential because Omega chosen over kappa(z) need not be algebraic over kappa(f(z)). This step does not silently use a construction hidden inside that node's proof: the lift and its projection are in the new statement itself.

Parent Step 3 reads the first new node's residue-field identification and the actual definitions def-sc-scheme-tangent-space and def-sc-dual-numbers. The tangent definition explicitly supplies relative dual-number maps and defines scalar multiplication by precomposition with epsilon sent to lambda epsilon. Hence lambda=0 factors through Spec Omega and x, exactly the constant vector. The remaining assertion that a vector space is zero iff all its elements are its zero element is elementary. Empty geometric fibres admit no section. For an empty source, the affine-cover equivalent definition in def-weil-unramified-morphism is vacuously satisfied. These four cited statements are also quoted verbatim, so C4 is checked directly rather than inferred from titles.

For the local new task I checked every statement used by its handoff. lem-sc-rational-tangent-cotangent-duality gives the two Hom-space identifications AND identifies the actual tangent map with the dual cotangent map. lem-sc-dual-map-injective-iff-surjective states the iff without a finite-dimensionality assumption. lem-sc-rational-unramified-cotangent-criterion requires closed rational points and local finite type: old Step 1 proves closedness of the section by maximal kernels in affine neighbourhoods and identifies the residue field; the target point of Spec k is closed and rational. Specializing the cotangent map to 0 -> m/m^2 and dualizing is exactly the old Step 2, retained below. No theorem about cotangent spaces was replaced by a definition citation.

For the geometric new task I checked lem-trf-unramified-locus-base-change literally supplies W_{h'}=(g')^{-1}(W_h), for any base change, rather than merely preservation of unramifiedness. It also defines W_h as the union of unramified source opens. def-weil-algebraic-closure includes existence of a closure for every field, def-weil-geometric-point identifies field maps out of residue fields with geometric points, and def-pc-fibre-product gives the compatible-pair universal property. Thus the old Steps 3--5 below have exactly the inputs they claim. In their new proof handoff, references to the tangent calculation belong to the first task/parent assembly; the second task itself proves the test directly with local unramifiedness, so it has no dependency on the tangent task. All source-point lifting, pointwise reflection, and the final affine cover remain obligations of that task, not unstated assumptions in the parent.

Small cases: for Z=Spec k the cotangent and tangent spaces are zero and the identity is unramified. For A^1_k at 0 the tangent is k and the structure map is ramified; for Spec(k[e]/e^2) its nonzero tangent also prevents unramifiedness, in any characteristic. The first new statement works over non-algebraically-closed k because a section itself forces residue field k. A nonrational point is excluded by its section hypothesis. For the second, an empty X has no tests or source points and is unramified. For A^1_S, a source generic point can have residue field transcendental over the base residue field; an algebraic closure of that source field is deliberately allowed and gives the required section. I checked this is a scheme fibre product, not an identification of points without its universal property. No finiteness of the set of points, quasi-compactness, or flatness is used.

B1--B10: both new nodes are self-contained TeX statements with all schemes, fields, sections, projection maps and residue fields introduced; no proofs occur in their statement fields, and proof arrays remain empty. The ordinary notions use existing definition nodes in stmt_deps. Sources give exact Stacks tags AND labels. Searches are real and unavailable services are labelled. No leaf or attachment is falsely claimed; blueprint links preserve the inherited ancestry. C1--C8: the parent has a citation for each substantive fact, direct statement quotations, no cycle and no new off-unit proof dependency. Old off-unit tools have moved into the future task obligations described above, not been replaced by weaker claims. D1--D5: two separate strict subproblems replace the long proof, not a single new restatement, and all old arguments survive in the handoff. E1--E7: I checked local finite type after arbitrary base change, rational closedness, equality of residue fields, correct second projection, all source points, relative maps, and empty cases against the source. The return is repaired by redistributing work; the mathematical statement and source route stay fixed.

## Preserved arguments and task handoff

The following are verbatim paragraphs from the returned proof. They preserve all details, including the old step numbers for cross-reference. New task A owns the rational section preliminaries and local tangent criterion (old 1--2). New task B owns preservation/reflection of the unramified locus, construction of the lifted section, and the cover argument (old 3--5); when proving B, replace mentions of tangent vanishing/old Step 2 by its hypothesis that the fibre map is unramified at its test section. The tangent/unramified substitution is now performed by parent Step 1. Old Step 6 is retained in the parent Step 3. This is an allocation of the same arguments, not an additional proof hidden in a new-node statement.

### Old step 1 — task A

Fix an algebraically closed field $k$ and a $k$-point $w$ of a $k$-scheme $Z$. The maps $k\to\kappa(w)\to k$ have composite the identity. The second is an injective field map whose image contains $k$, so both maps are isomorphisms. The point $w$ is closed: in every affine open $\operatorname{Spec}B$ containing it, the $k$-algebra map $B\to k$ is surjective and its kernel is maximal. If $w$ specialized to $z$, an affine neighbourhood of $z$ would also contain $w$; maximality in that affine forces $z=w$. Thus $w$ and the point of $\operatorname{Spec}k$ satisfy the closed and rational hypotheses needed below.

Inputs: def-weil-geometric-point, def-pc-scheme.

### Old step 2 — task A

For a locally finite type $p:Z\to\operatorname{Spec}k$ and the point $w$ of Step 1, put $C_w=\mathfrak m_w/\mathfrak m_w^2$. The cotangent space of $\operatorname{Spec}k$ is zero, so its cotangent map is $u:0\to C_w$. By [lem-sc-rational-tangent-cotangent-duality], the tangent map is the dual of $u$, with source $T_{Z/k,w}$ and zero target. By [lem-sc-dual-map-injective-iff-surjective], this dual is injective exactly when $u$ is surjective. A map to the zero vector space is injective exactly when its source is zero. Finally [lem-sc-rational-unramified-cotangent-criterion] identifies surjectivity of $u$ with $p$ being unramified at $w$. Hence $T_{Z/k,w}=0$ exactly when $p$ is unramified at $w$. Only local finite type and the closed rational points from Step 1 were used.

Inputs: lem-sc-rational-tangent-cotangent-duality, lem-sc-dual-map-injective-iff-surjective, lem-sc-rational-unramified-cotangent-criterion.

### Old step 3 — task B

Assume $f$ is unramified. For an arbitrary geometric point $\bar s:\operatorname{Spec}\Omega\to S$, write $p:X_{\bar s}\to\operatorname{Spec}\Omega$ and $g:X_{\bar s}\to X$ for the projections. The morphism $p$ is locally of finite type by [lem-weil-pbc-lft-base-change]. Write $W_f,W_p$ for the loci of [lem-trf-unramified-locus-base-change]. Since $f$ is unramified, $W_f=X$; that node gives $W_p=g^{-1}(W_f)=X_{\bar s}$. In particular $p$ is unramified at every $\Omega$-point, so Step 2 gives the required tangent vanishing. The base-change statement permits every algebraically closed extension $\Omega$, not just an algebraic closure of a base residue field.

Inputs: lem-weil-pbc-lft-base-change, lem-trf-unramified-locus-base-change.

### Old step 4 — task B

Conversely assume the asserted tangent vanishing. Fix any $z\in X$. Choose an algebraic closure $\Omega$ of $\kappa(z)$, which exists by [def-weil-algebraic-closure]. Let $a:\operatorname{Spec}\Omega\to X$ be the geometric point over $z$ induced by $\kappa(z)\hookrightarrow\Omega$ [def-weil-geometric-point], and put $\bar s=f\circ a$. The compatible pair $(a,\mathrm{id})$ defines an $\Omega$-point $\widetilde z$ of $X\times_S\operatorname{Spec}\Omega$ by the fibre-product universal property [def-pc-fibre-product]. Its projection is $z$. The quantifier in the statement includes this $\bar s$ even when $\Omega/\kappa(f(z))$ is not algebraic. Thus the tangent space at $\widetilde z$ is zero.

Inputs: def-weil-algebraic-closure, def-weil-geometric-point, def-pc-fibre-product.

### Old step 5 — task B

The morphism $p:X_{\bar s}\to\operatorname{Spec}\Omega$ from Step 4 is locally of finite type by [lem-weil-pbc-lft-base-change]. Its point $\widetilde z$ is closed and rational by Step 1, so Step 2 makes $p$ unramified there, i.e. $\widetilde z\in W_p$. Applying [lem-trf-unramified-locus-base-change] gives $\widetilde z\in g^{-1}(W_f)$, hence $z\in W_f$. Since $z$ was arbitrary, every point has an unramified source neighbourhood. Such neighbourhoods give an affine cover by unramified ring maps, precisely the affine-cover formulation of [def-weil-unramified-morphism]; therefore $f$ is unramified. This argument neither asserts that every point of one fixed geometric fibre is rational nor assumes flatness, finite presentation, quasi-compactness or a Noetherian base.

Inputs: lem-weil-pbc-lft-base-change, lem-trf-unramified-locus-base-change, def-weil-unramified-morphism.

### Old step 6 — parent Step 3

By [def-sc-scheme-tangent-space] and [def-sc-dual-numbers], tangent vectors at an $\Omega$-point $x$ are exactly the morphisms of $\Omega$-schemes $\operatorname{Spec}(\Omega[\epsilon]/(\epsilon^2))\to X_{\bar s}$ reducing to $x$. The zero vector is the constant one: scalar multiplication by zero is precomposition with $\epsilon\mapsto0$, which factors through $\operatorname{Spec}\Omega$ and then $x$. A vector space is zero if and only if every vector equals its zero vector. This proves the stated equivalent formulation. If a fibre is empty it has no $\Omega$-points, so its condition is vacuous; if $X$ is empty, the affine-cover definition likewise makes $f$ unramified.

Inputs: def-sc-scheme-tangent-space, def-sc-dual-numbers, def-weil-unramified-morphism.

## Not duplicates

lem-sfb-rational-point-tangent-unramified vs lem-zl-bertini-finite-cover-irreducible-system: is a Bertini theorem for linear systems on affine smooth varieties, not a local tangent or geometric-fibre unramifiedness test.

lem-sfb-rational-point-tangent-unramified vs def-weil-geometric-fibre: defines a fibre over a chosen algebraic closure of a base residue field; the new statement is a criterion for unramifiedness, with arbitrary geometric points where needed.

lem-sfb-rational-point-tangent-unramified vs def-weil-geometric-point: defines field-valued geometric points and their residue-field maps; it neither detects unramifiedness at a section nor proves the tangent criterion.

lem-sfb-rational-point-tangent-unramified vs lem-weil-pbc-field-point-factors-through-immersion: factors a field-valued point through an immersion; the new statement is not a factorization through an immersion.

lem-sfb-rational-point-tangent-unramified vs lem-weil-pbc-morphism-from-spec-field: classifies maps from a field spectrum; it does not prove the local tangent criterion or global detection by fibre sections.

lem-sfb-rational-point-tangent-unramified vs lem-weil-pbc-residue-field-point-naturality: states naturality of canonical residue-field points under a morphism; it has no tangent or unramifiedness criterion.

lem-sfb-rational-point-tangent-unramified vs lem-weil-pbc-spec-field-point-residue-field: computes residue-field maps for affine field-valued points; it has no local tangent criterion or global geometric-point detection theorem.

lem-sfb-rational-point-tangent-unramified vs lem-trf-closed-point-residue-immersion: characterizes closed points by their residue-field closed immersion; it does not assert rational-section closedness or any unramifiedness test.

lem-sfb-rational-point-tangent-unramified vs lem-sfb-geometric-tangent-unramified: is the parent combining local tangent vanishing, all geometric fibres, global unramifiedness and relative dual-number uniqueness; this new task supplies only one independent intermediate argument.

lem-sfb-unramified-geometric-point-test vs def-weil-geometric-fibre: defines a fibre over a chosen algebraic closure of a base residue field; the new statement is a criterion for unramifiedness, with arbitrary geometric points where needed.

lem-sfb-unramified-geometric-point-test vs def-weil-geometric-point: defines field-valued geometric points and their residue-field maps; it neither detects unramifiedness at a section nor proves the tangent criterion.

lem-sfb-unramified-geometric-point-test vs lem-weil-pbc-field-point-factors-through-immersion: factors a field-valued point through an immersion; the new statement is not a factorization through an immersion.

lem-sfb-unramified-geometric-point-test vs lem-weil-pbc-morphism-from-spec-field: classifies maps from a field spectrum; it does not prove the local tangent criterion or global detection by fibre sections.

lem-sfb-unramified-geometric-point-test vs lem-weil-pbc-residue-field-point-naturality: states naturality of canonical residue-field points under a morphism; it has no tangent or unramifiedness criterion.

lem-sfb-unramified-geometric-point-test vs lem-weil-pbc-spec-field-point-residue-field: computes residue-field maps for affine field-valued points; it has no local tangent criterion or global geometric-point detection theorem.

lem-sfb-unramified-geometric-point-test vs lem-trf-closed-point-residue-immersion: characterizes closed points by their residue-field closed immersion; it does not assert rational-section closedness or any unramifiedness test.

lem-sfb-unramified-geometric-point-test vs lem-trf-unramified-locus-base-change: gives the base-change equality of loci, which is a reusable input; it does not supply sections above each source point using its residue-field closure or state the global test restricted to such sections.

lem-sfb-rational-point-tangent-unramified vs lem-sc-rational-unramified-cotangent-criterion: that node characterizes unramifiedness by surjectivity of a map between two cotangent spaces, requiring closed rational points; the new task obtains closedness from a section and proves tangent vanishing for its structure morphism using duality.

lem-sfb-rational-point-tangent-unramified vs lem-sc-rational-tangent-cotangent-duality: that node identifies tangent maps with dual cotangent maps, without an unramifiedness criterion; the new task combines it with the cotangent criterion.

lem-sfb-rational-point-tangent-unramified vs lem-sc-finite-flat-unramified-tangent-criterion: that node requires finite locally free and characterizes etaleness by injectivity of a tangent map between two schemes; the new task has no flatness assumption and concerns unramifiedness of a structure morphism.

## Unfinished work

Exactly the two newly created statement-only tasks remain to split, as the return explicitly requires; this delivery does not claim their proofs are finished. No Lean work was authorized or performed. The parent's proof assembly and all required validation/delivery work are handled here.
