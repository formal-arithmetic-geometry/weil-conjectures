# Worker report — Q102, 2026-10-22

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-fibre-degree-bound-field-points.json`: item, statement unchanged; three assembly steps, 1768 characters in their text, against 5362 in the returned six-step proof.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-field-base-point-fibre-isomorphism.json`: new statement, status unsplit, no proof steps or proof dependencies; no full Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-field-degree-isomorphism-transport.json`: new statement, status unsplit, no proof steps or proof dependencies; no full Mathlib match.
- `citations.json`: one verbatim statement quotation per cited node per assembly step. Auxiliary sandbox records retain the original node, full search responses, logged searches, and the scripts used for this repair.

## Attachments

None for the item or either complete new statement. The parent declaration `AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_iff_fieldPoints` is at `lean/Sheaf/AlgebraicGeometry/BoundsFiberDegreesFieldPoints.lean:55` and ends with `sorry` at line 59. The blueprint tag is not found under `lean/WeilConjectures/`. Concept searches there find only ingredients, not a sorry-free theorem for the equivalence.

The project already proves `AlgebraicGeometry.Scheme.Hom.finrankΓ_eq_of_iso` (`lean/WeilConjectures/AlgebraicGeometry/Morphisms/FiberDegree.lean:103`). I read its statement and body: it gives the numeric global-sections finrank equality over a compatible ring isomorphism. It does not assert the finite-morphism equivalence or the induced ring isomorphism's semilinearity and basis transport as conclusions, so it does not attach the complete second new statement. It is useful implementation material for its future worker. Likewise `AlgebraicGeometry.fiberDegree_eq_finrankΓ` at line 602 compares degrees assuming an affine morphism and does not assert the canonical fibre isomorphism for every scheme over a field.

## WANTED

None: all sources used are already local. No SGA source was used.

## What was wrong and what changed

The sole return is the human's re-split instruction: the old 5362-character proof was too large to assign as one work item. The sandbox had only dispatcher brief markers when I began; it contained no item, report, citations or search log to reuse. I read the current shared repository node and preserved it in `returned-node.json`. Its six proof steps agree with the return's quoted sizes. I preserved the statement byte-for-byte, and preserved the existing Lean and review metadata, while replacing only the stage-1 proof/dependencies, adding current search records, completing blueprint.same_as, and updating split_report. The immutable repository was only read, with no git command there.

The repair adds TWO comparable, independently assignable arguments, not a single replacement for the parent. The first new node concerns arbitrary schemes over a single field and contains no fibre-degree bound. The second concerns an arbitrary commuting square of field and scheme isomorphisms and contains neither bounds on fibres nor a quantifier over field-valued points. The parent still chooses the residue-field test for the reverse implication, supplies the arbitrary field-valued point for the forward implication, and applies the existing finite-fibre base-change theorem. No conclusion of the parent was weakened and no hypothesis was added.

## Preservation of the entire returned argument

Old step 1 remains assembly step 1. Its comparison of different choices of fibre product is an application of the second new node with identity field isomorphism. Its remaining content is the defining residue-field test.

Old steps 2 and 4 are assigned together to `lem-weil-pbc-field-base-point-fibre-isomorphism`. The future proof must identify the scheme residue field through the localization-at-zero and quotient-at-zero map, prove that this CANONICAL map is a field isomorphism, identify the canonical residue morphism with its spectrum and its global-sections map with that same map, then prove that the first fibre projection is an isomorphism by the displayed pullback universal property. The new statement explicitly specifies all these canonical maps and the structure-map equation; an abstract field isomorphism or a homeomorphism does not suffice.

Old step 3 remains assembly step 2, using `lem-weil-pbc-fibre-degree-base-change` with precisely S=Y, T=Spec K, t=xi, s=g(xi), and second projection h. The finite original fibre has degree d<=n by hypothesis; the existing cited node gives both finiteness of q and its degree d.

Old steps 5 and 6, and the choice-comparison part of step 1, are assigned to `lem-weil-pbc-finite-field-degree-isomorphism-transport`. For h:Z->Spec K, q:T->Spec L and u:T~Z with h u=Spec(phi) q, the factorization h=Spec(phi) q u^{-1} gives finiteness from q; conversely q=Spec(phi)^{-1} h u gives the other direction. The future proof uses `lem-weil-pbc-isomorphism-finite` and `lem-weil-pbc-finite-composition`. Applying global sections gives u* alpha=beta phi and hence the specified semilinear equation. A linear relation among the images pulls back via u* and phi^{-1} to a relation among the original family, so independence is preserved; every vector of B pulls back via (u*)^{-1}, is a finite sum in a basis of A, and its coefficients push forward via phi, so spanning is preserved. The inverse argument proves the iff on bases. With either finite structure map this gives equal finite dimensions. Thus all of the old semilinear basis argument and the finite-composition argument remain assigned work, with explicit conclusions available to the parent. The old proof text is retained verbatim below, rather than being shortened and discarded.

## Returned proof, verbatim

### Original step 1

*(2)$\Rightarrow$(1).* Assume (2) and let $y\in Y$. Take $K=\kappa(y)$ [def-weil-residue-field] and for $\operatorname{Spec}K\to Y$ the canonical morphism $j_y:\operatorname{Spec}\kappa(y)\to Y$. By [def-pc-scheme-fibre] the fibre $X_y$ is the fibre product $X\times_Y\operatorname{Spec}\kappa(y)$ of $f$ and $j_y$, regarded over $\kappa(y)$ through its second projection, and the $\kappa(y)$-algebra structure of $\Gamma(X_y,\mathcal O_{X_y})$ used in the degree [def-weil-pbc-fibre-degree-bound] is the one induced by that projection; this is exactly the scheme $X_K$ of (2) with its structure over $K$. (If $X_K$ is another choice of the fibre product, the unique isomorphism $u:X_K\to X_y$ of fibre products commutes with the second projections, so the projection of $X_y$ is that of $X_K$ composed with the isomorphism $u^{-1}$, finite by [lem-weil-pbc-isomorphism-finite] and [lem-weil-pbc-finite-composition], and $\Gamma(u)$ is an isomorphism of $\kappa(y)$-algebras, so finiteness and the dimension of global sections agree.) Hence (2) says that $X_y$ is finite over $\kappa(y)$ with $\dim_{\kappa(y)}\Gamma(X_y,\mathcal O_{X_y})\le n$. As $y$ was arbitrary, $n$ bounds the degrees of the fibres of $f$ [def-weil-pbc-fibre-degree-bound].

Uses: def-weil-residue-field, def-pc-scheme-fibre, def-weil-pbc-fibre-degree-bound, lem-weil-pbc-isomorphism-finite, lem-weil-pbc-finite-composition.

### Original step 2

*The point of $\operatorname{Spec}K$.* For the converse, let $K$ be a field and $g:\operatorname{Spec}K\to Y$ a morphism [def-weil-affine-spectrum]. Since $K$ is a field, $\operatorname{Spec}K$ has exactly one point $\xi=(0)$. Apply [lem-weil-pbc-spec-residue-field-identification] with $R=K$, $\mathfrak p=(0)$: the canonical morphism $j_\xi:\operatorname{Spec}\kappa(\xi)\to\operatorname{Spec}K$ of the residue field [def-weil-residue-field] equals $\operatorname{Spec}(\varphi)$ with $\varphi=e^{-1}\circ\pi:K\to\kappa(\xi)$, where $\pi:K\to K_{(0)}/(0)K_{(0)}$ and $e$ is a ring isomorphism. Every nonzero element of $K$ is a unit, so the localization $K\to K_{(0)}$ is an isomorphism, and the quotient by the zero ideal is an isomorphism; hence $\pi$ and $\varphi$ are isomorphisms of fields, and $j_\xi=\operatorname{Spec}(\varphi)$ is an isomorphism of schemes with inverse $\operatorname{Spec}(\varphi^{-1})$. Under $\Gamma(\operatorname{Spec}A,\mathcal O)=A$ the map induced by $j_\xi$ on global sections is $\varphi:K\to\kappa(\xi)$.

Uses: def-weil-affine-spectrum, def-weil-residue-field, lem-weil-pbc-spec-residue-field-identification.

### Original step 3

*(1)$\Rightarrow$(2): the base change of the fibre.* Assume (1); let $g$, $\xi$, $\varphi$ be as in step 2 and $y=g(\xi)$. Put $X_K=X\times_Y\operatorname{Spec}K$ with projections $\mathrm{pr}_1:X_K\to X$ and $\mathrm{pr}_2:X_K\to\operatorname{Spec}K$ [def-pc-fibre-product]. By (1), the fibre $X_y$ [def-pc-scheme-fibre] is finite over $\kappa(y)$ of degree $d=\dim_{\kappa(y)}\Gamma(X_y,\mathcal O_{X_y})\le n$ [def-weil-pbc-fibre-degree-bound]. Apply [lem-weil-pbc-fibre-degree-base-change] with $S=Y$, $T=\operatorname{Spec}K$, the morphisms $f$ and $g$, $X_T=X_K$, $f_T=\mathrm{pr}_2$, $t=\xi$ and $s=g(\xi)=y$: the fibre $F=(X_K)_\xi=X_K\times_{\operatorname{Spec}K}\operatorname{Spec}\kappa(\xi)$ of $\mathrm{pr}_2$ at $\xi$ (fibre product of $\mathrm{pr}_2$ and $j_\xi$), with projections $p:F\to X_K$ and $q:F\to\operatorname{Spec}\kappa(\xi)$, $\mathrm{pr}_2\circ p=j_\xi\circ q$, is finite over $\kappa(\xi)$ (the morphism $q$ is finite) and $\dim_{\kappa(\xi)}\Gamma(F,\mathcal O_F)=d$, where $\Gamma(F,\mathcal O_F)$ is a $\kappa(\xi)$-algebra through $q$.

Uses: def-pc-fibre-product, def-pc-scheme-fibre, def-weil-pbc-fibre-degree-bound, lem-weil-pbc-fibre-degree-base-change.

### Original step 4

*$F$ is $X_K$.* Since $j_\xi$ is an isomorphism (step 2), $(X_K,\mathrm{id}_{X_K},j_\xi^{-1}\circ\mathrm{pr}_2)$ is a fibre product of $\mathrm{pr}_2$ and $j_\xi$ [def-pc-fibre-product]: it commutes, $\mathrm{pr}_2\circ\mathrm{id}=j_\xi\circ(j_\xi^{-1}\circ\mathrm{pr}_2)$, and for a scheme $W$ with $a:W\to X_K$, $b:W\to\operatorname{Spec}\kappa(\xi)$, $\mathrm{pr}_2\circ a=j_\xi\circ b$, the morphism $a$ is the unique $h:W\to X_K$ with $\mathrm{id}\circ h=a$, and it satisfies $j_\xi^{-1}\circ\mathrm{pr}_2\circ a=b$. By uniqueness of fibre products up to unique isomorphism, the first projection $p:F\to X_K$ is an isomorphism, and $q=j_\xi^{-1}\circ\mathrm{pr}_2\circ p$.

Uses: def-pc-fibre-product.

### Original step 5

*$X_K$ is finite over $K$.* By step 4, $\mathrm{pr}_2=j_\xi\circ q\circ p^{-1}$. The isomorphisms $p^{-1}$ and $j_\xi$ are finite [lem-weil-pbc-isomorphism-finite], $q$ is finite (step 3), and a composition of finite morphisms is finite [lem-weil-pbc-finite-composition]; so $\mathrm{pr}_2:X_K\to\operatorname{Spec}K$ is finite [def-weil-finite-integral-morphism], i.e. $X_K$ is finite over $K$.

Uses: lem-weil-pbc-isomorphism-finite, lem-weil-pbc-finite-composition, def-weil-finite-integral-morphism.

### Original step 6

*The degree of $X_K$.* Apply $\Gamma(-,\mathcal O)$ to $\mathrm{pr}_2\circ p=j_\xi\circ q$: with $\alpha:K\to\Gamma(X_K,\mathcal O_{X_K})$ and $\beta:\kappa(\xi)\to\Gamma(F,\mathcal O_F)$ the maps induced by $\mathrm{pr}_2$ and $q$ (the algebra structures of the degree), $p^*:\Gamma(X_K,\mathcal O_{X_K})\to\Gamma(F,\mathcal O_F)$ the ring isomorphism induced by the isomorphism $p$, and $\varphi$ the map induced by $j_\xi$ (step 2), we get $p^*\circ\alpha=\beta\circ\varphi$. So $p^*(\alpha(a)v)=\beta(\varphi(a))p^*(v)$: $p^*$ is a bijection, additive and semilinear along the field isomorphism $\varphi$, hence maps a $K$-basis of $\Gamma(X_K,\mathcal O_{X_K})$ onto a $\kappa(\xi)$-basis of $\Gamma(F,\mathcal O_F)$ and conversely. Therefore $\dim_K\Gamma(X_K,\mathcal O_{X_K})=\dim_{\kappa(\xi)}\Gamma(F,\mathcal O_F)=d\le n$ (step 3). Together with step 5 this is (2) for $g$; as $K$ and $g$ were arbitrary, (1) implies (2).

Uses: def-weil-affine-spectrum.

## Searches and provenance

I read Stacks `morphisms.tex`, Tag 03J4 (`definition-universally-bounded`) and Tag 03J5 (`lemma-characterize-universally-bounded`), lines 15290–15360, verifying the tag/label pairs in `tags/tags`. The item is exactly the equivalence (1)<->(2) of 03J5, with degree the global-sections dimension through the projection. The further point-count assertion of 03J5 is not a clause of this item. The new statements make explicit the isomorphism and scalar-compatibility subarguments in the existing proof's expansion of 03J5, not a different route. I also read the canonical residue-field morphism discussion surrounding Schemes Tag 01J6 (`lemma-morphism-from-spec-local-ring`) and Tag 01J9 (`lemma-characterize-points`), and the existing residue-field identification node and its Mathlib source (ResidueField.lean, lines 299–328).

The chapter record sec-proper-base-change and unit sk-thm-p1 were read. I read the current main-20261015 blueprint ancestor's proof, `lemma-weil-pbc-h1-constructible-representation.proof.md`, and the current unit's section. The new nodes keep the ancestor and the exact existing place on the constructible-approximation branch, with the item prepended to blueprint.from.via and an explicit old-step description. No unit-level route is replaced.

Before creation I searched the entire DAG by 03J5, residue fields, unique/single points, semilinearity, field isomorphisms, finite degrees, and the project declaration finrankΓ_eq_of_iso. I searched the whole blueprint with tools/blueprint_refs.py for “residue field”, “field isomorphism”, “finite degree”, “unique point”, “03J5”, “semilinear”, “fibre degree”, “global sections”, and “field-valued”, and ran its ancestor lookup. No blueprint node states either complete new statement, and the existing tag-sharing nodes have the different hypotheses and conclusions listed below. I also checked both proposed new ids were absent. `lem-weil-pbc-spec-field-point-residue-field` identifies affine residue fields and factorizations of field-valued points; it does not identify the entire scheme-theoretic fibre of arbitrary W over a field. `lem-weil-pbc-spec-residue-field-identification` identifies the canonical map for an arbitrary ring, without asserting the field-case isomorphism and its pullback projection. `lem-weil-pbc-spec-map-global-sections` concerns the ring map induced by Spec(psi), not semilinear global sections of arbitrary schemes in a commuting isomorphism square.

All Mathlib queries recorded on the new nodes and newly appended to the parent were run through the required msearch.py and read in full. The full raw responses are in search-results-field-point.txt, search-results-degree-transport.txt and search-results-parent.txt; searches.jsonl is the command's original log. I used two natural-language phrasings for each statement, LeanSearch, LeanFinder, Loogle and grep. The first two Loogle patterns used the unqualified name IsIso, which Loogle rejected; I record them as unavailable for a valid search and ran corrected qualified/name-specific patterns. The corrected field-fibre Loogle pattern returned no hits. This is not a fabricated absence result from a failed query.

For the first new node, the hits SpecToEquivOfField, the unique-point instances and the fibre definitions do not assert the needed scheme isomorphism with its canonical scalar map. The grep hits Spec.residueFieldIso, Spec.algebraMap_residueFieldIso_inv and Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (ResidueField.lean:301,308,320) are already carried by the existing residue-field identification leaf, which a future split can use; they do not prove the whole new statement in one specialization. I read AlgClosed/Basic.lean:27–53: residueFieldIsoBase assumes an algebraically closed base field, finite type and a closed point; these are not hypotheses available here. Spec.fiberToSpecResidueFieldIso (Fiber.lean:79) is an affine tensor model, not the stated arbitrary-scheme identification.

For the second new node, I read Morphisms/Finite.lean:67–90 and the FlatRank hits. IsFinite's iso/composition instances cover finiteness ingredients; FlatRank's finrank is pointwise finite-flat rank and is not a statement of the whole global-sections isomorphism square. Loogle and grep found Algebra.finrank_eq_of_equiv_equiv, which I read at LinearAlgebra/Dimension/Finrank.lean:148–154: it requires the compatible algebra ring isomorphisms as input, whereas constructing precisely that square from scheme maps is part of this new node. It does not state either the scheme-induced semilinearity or finiteness equivalence. Thus no full Mathlib leaf is claimed. The project finrankΓ_eq_of_iso likewise provides a numerical consequence, discussed in Attachments.

## Review by Q102

I reviewed the unchanged item and both new statements against the local sources and the original six proof steps. This is my author self-review under the direct-delivery brief; no second worker was started. Both new nodes are statement-only, have complete hypotheses and introduced objects, definition dependencies, source tag and label, checked blueprint ancestry and recorded searches. They have empty proof/proof_deps and null proof_origin, so the assigned arguments remain open for independent workers. Their statements are comparable in size (1011 and 1108 characters) and their assigned original arguments are steps 2+4 versus steps 5+6 plus the comparison clause of step 1. The parent assembly has 1768 characters and no step exceeds 2000 characters.

In assembly step 1, I opened def-pc-scheme-fibre: it explicitly defines the fibre as the pullback against the canonical residue-field map and specifies the second projection. I opened def-pc-fibre-product: uniqueness is explicitly an isomorphism commuting with both projections. Hence the comparison isomorphism meets the second new node's commuting-square hypothesis with phi the identity, so both finiteness and the dimension, not only underlying schemes, agree. I read def-weil-pbc-fibre-degree-bound: it quantifies over EVERY y and uses exactly that projection to define the algebra action and degree. Thus this step derives (1) from (2) without a hidden finiteness-invariance fact.

In assembly step 2, the first new statement gives an actual FIELD ISOMORPHISM from K to the scheme residue field, the equality j=Spec(phi), an actual scheme isomorphism p (not just a homeomorphism), and h p=j q. I checked its universal quantifier allows W nonaffine and nonfinite at this point. I opened lem-weil-pbc-fibre-degree-base-change: its statement allows arbitrary f and g, and assumes only that X_s is finite of degree d. These hypotheses come from (1) at y=g(xi). Its conclusion is precisely that the fibre of the base-changed second projection h at xi is finite over L of the same degree d. This is F and q in the new node, with no extra finite-type, separatedness, reducedness or algebraic-closedness assumption.

In assembly step 3, I checked the second new node's orientation u:T->Z against p:F->W: Z=W, T=F, h=pr2 and q the fibre projection, with phi:K~L. The equation from step 2 has exactly the orientation h p=Spec(phi) q. The node's finite iff can therefore be applied from q to h. Its scalar compatibility conclusion uses the precise global-sections algebra actions, and its finite degree equality yields dim_K Gamma(W)=dim_L Gamma(F)=d<=n. The quantifiers K,g remain arbitrary. Every non-elementary assertion in the assembly is now in a cited statement, and citations.json copies actual statement text for each cited node. No step cites a definition for a theorem it does not state.

I tested the field-base identification for K=F_p and for a field with nontrivial automorphisms: the map is the CANONICAL germ/residue map, not an arbitrary choice of isomorphism. With W empty, both fibre and W are empty and p is still an isomorphism. For degree transport I tested the empty scheme (zero algebra, empty basis, degree zero), dual numbers K[epsilon]/(epsilon^2) (degree two, so nilpotents are not dropped), disconnected finite schemes (the assertion preserves total algebra dimension), and a nontrivial field automorphism with a twisted algebra structure (the map is semilinear along phi, not assumed K-linear). The basis conclusion is stated for every index set, so it also makes sense before finiteness. The dimension-as-degree conclusion is used only when the maps are finite; no infinite-dimensional Module.finrank convention enters the parent's proof. For n=0, empty fibres have degree zero; neither implication assumes positivity. If Y is empty there are no residue-field or field-valued tests, and both sides hold vacuously.

I checked B1–B10 by opening the new files and the search outputs; C1–C8 by matching every use to the statements above, with all proof dependencies equal to the union of uses; D1–D5 by checking the new nodes do not restate either implication and that the parent still carries the bound-specific argument; and E1–E7 by checking the precise maps, hypotheses and edge cases just described. The only correction needed was the requested workload re-split; there is no statement dispute. No new node depends on the parent, so this extraction introduces no circular argument. All citations stay within sk-thm-p1 or its definition tools; split_report.tool_uses is empty.

## Not duplicates

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-fibre-degree-bound-field-points: the existing item is the global equivalence of two fibre-bound conditions; this new node has no bound or quantifier over field-valued points and instead isolates one reusable isomorphism argument.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-finite-open-cover-degree-sum: the existing node bounds the degree of a scheme covered by finite opens by a sum; this node makes an isomorphism identification and uses no open cover or sum.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-composition-fibre-degree-bound: the existing node multiplies bounds for a composition of two arbitrary scheme morphisms; this node neither composes bounds nor assumes them.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-lqf-qc-source-bounded-fibres: the existing node asserts existence of a global bound from a quasi-compact source and local quasi-finiteness; neither hypothesis nor that conclusion occurs here.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-fibre-degree-base-change: the existing node preserves the degree of a finite residue fibre under arbitrary base change; the first new node identifies the canonical fibre with its entire source over a field without finiteness, and the second compares compatible global-sections algebra structures over field isomorphisms rather than forming an arbitrary base change.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-flat-fp-lqf-bounded-stratification: the existing node constructs a universal finite-locally-free degree stratification under flatness, finite presentation, separatedness, local quasi-finiteness and boundedness; this node has no stratification and none of those additional assumptions.

lem-weil-pbc-finite-field-degree-isomorphism-transport vs lem-weil-pbc-fibre-degree-bound-field-points: the existing item is the global equivalence of two fibre-bound conditions; this new node has no bound or quantifier over field-valued points and instead isolates one reusable isomorphism argument.

lem-weil-pbc-finite-field-degree-isomorphism-transport vs lem-weil-pbc-finite-open-cover-degree-sum: the existing node bounds the degree of a scheme covered by finite opens by a sum; this node makes an isomorphism identification and uses no open cover or sum.

lem-weil-pbc-finite-field-degree-isomorphism-transport vs lem-weil-pbc-composition-fibre-degree-bound: the existing node multiplies bounds for a composition of two arbitrary scheme morphisms; this node neither composes bounds nor assumes them.

lem-weil-pbc-finite-field-degree-isomorphism-transport vs lem-weil-pbc-lqf-qc-source-bounded-fibres: the existing node asserts existence of a global bound from a quasi-compact source and local quasi-finiteness; neither hypothesis nor that conclusion occurs here.

lem-weil-pbc-finite-field-degree-isomorphism-transport vs lem-weil-pbc-fibre-degree-base-change: the existing node preserves the degree of a finite residue fibre under arbitrary base change; the first new node identifies the canonical fibre with its entire source over a field without finiteness, and the second compares compatible global-sections algebra structures over field isomorphisms rather than forming an arbitrary base change.

lem-weil-pbc-finite-field-degree-isomorphism-transport vs lem-weil-pbc-flat-fp-lqf-bounded-stratification: the existing node constructs a universal finite-locally-free degree stratification under flatness, finite presentation, separatedness, local quasi-finiteness and boundedness; this node has no stratification and none of those additional assumptions.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-spec-residue-field-identification: the existing node identifies residue fields and canonical maps for arbitrary rings; this node proves the field case is an isomorphism and identifies the entire fibre of every scheme over that field, with projection compatibility.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-spec-field-point-residue-field: the existing node describes affine residue fields and factorization of a field-valued point; it does not assert that a scheme over a field is canonically isomorphic to its fibre.

lem-weil-pbc-finite-field-degree-isomorphism-transport vs lem-weil-pbc-spec-map-global-sections: the existing node identifies the map on sections of Spec(psi) between affine spectra; this node compares arbitrary schemes with compatible field-isomorphism structure maps, finiteness and bases.

lem-weil-pbc-field-base-point-fibre-isomorphism vs def-weil-geometric-fibre: the existing definition takes an algebraic closure of a residue field and defines the resulting geometric fibre; this statement instead identifies the ordinary residue fibre over Spec K with the whole source, for any field K and without algebraic closure.

lem-weil-pbc-field-base-point-fibre-isomorphism vs def-weil-geometric-point: the existing definition describes points valued in algebraically closed fields and the associated residue-field map; this statement proves the canonical residue map of Spec K and the first projection of every ordinary fibre over it are isomorphisms for arbitrary fields.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-field-point-factors-through-immersion: the existing lemma lifts a field-valued point through an immersion at a specified image point and compares residue fields along that immersion; this statement supplies no immersion hypothesis, and identifies an entire arbitrary scheme over a field with its ordinary fibre.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-morphism-from-spec-field: the existing lemma classifies field-valued points and gives their factorization through the image residue field; it does not state the canonical isomorphism of a whole scheme W with its fibre over the unique point of Spec K or its projection equation.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-weil-pbc-residue-field-point-naturality: the existing lemma says the canonical residue morphism is natural and that open immersions induce residue-field isomorphisms; this statement proves that the residue morphism of Spec K itself is an isomorphism and identifies every pullback along it with the whole original scheme.

lem-weil-pbc-field-base-point-fibre-isomorphism vs lem-trf-closed-point-residue-immersion: the existing lemma characterizes closed points by the canonical residue morphism being a closed immersion; this statement proves that morphism is an isomorphism for Spec of a field and identifies its base changes for arbitrary schemes W.

## What could not be finished

No unresolved mathematical repair. The two new nodes intentionally remain unsplit, as the return requires; their future proofs can be assigned in parallel. The parent and new-node statements have been checked without writing Lean or running a compiler, Lake or a build. Delivery validation is recorded below.

## Delivery validation

The first dry run stopped at the duplicate-tag gate. I opened and read all six additional 01J9-sharing node statements it named; none states the whole field-base fibre-isomorphism lemma. The pairwise differences above were added without changing the mathematics or removing the legitimate source tag.
