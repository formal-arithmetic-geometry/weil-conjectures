# Q33 stage-1 repair: lem-sfb-curve-frobenius-separable-factorization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-curve-frobenius-separable-factorization.json: unchanged statement; five assembly steps, 2113 characters in their proof texts.
- dag/nodes/sec-six-functors-basics/lem-sfb-curve-intermediate-field-realization.json: new statement, status unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-frobenius-twist-geometric-integrality-affine.json: new statement, status unsplit; no Mathlib match.
- citations.json: a verbatim statement quote for every citation of every parent step.
- report.md: this repair and independent self-review. Search queries and results are retained in searches.jsonl.

## Attachments

None. The search for the exact blueprint tag under lean/WeilConjectures returned no declaration. Concept searches in the Curve source found affine normalization, rational-map and additive-cohomology Frobenius constructions, not the item's full assertion. The existing Sheaf.AlgebraicGeometry.Curve.FrobeniusSeparableFactorization theorem ends in sorry and therefore is not an attachment. Its statement and six-step docstring were read as reference material. No Lean was written or compiled.

## WANTED

None. The Stacks sources used are present locally.

## Return repaired

The return asked for at least two comparable, independently workable statement-only nodes and a parent proof of at most 3000 characters. The former 3675-character proof has been redistributed, not replaced by a shorter unexplained assertion. The intermediate-field helper carries the entire field-finiteness/transcendence-degree check and the compatible model/morphism construction (old steps 3 and 4). The twisted-scheme helper carries old step 6, including the iterated-base-change identification, geometric integrality, the second projection, the balanced tensor formula, and the identity convention. The parent retains old steps 1, 2 and 5 and assembles the two helpers; these retained steps continue citing the existing non-elementary ingredients. The two extracted work packages occupy about 1311 and 1066 characters respectively in the original argument; their self-contained statements have comparable scope. Neither asserts the existence of the Frobenius/separable factorization of the item.

The initial sandbox had only dispatcher .brief files, with no node, report or searches. I copied the current read-only repository item, which contains the returned six-step proof, preserving its statement, sources, prior Mathlib records, ancestry and maintainer metadata. The original proof is reproduced below so each piece can be audited after the re-split. There was no local earlier split or report to overwrite. The existing source and Lean metadata are retained; the deliver tool rebases split-owned fields on current main.

## New nodes

lem-sfb-curve-intermediate-field-realization states the realization of an arbitrary intermediate field of an existing nonconstant map, with both function-field pullbacks pinned down. It does not assume separability or characteristic p, and does not assert any Frobenius identification. I read curves.tex Tag 0CD2, its intermediate-field sentence; Tag 0BY1, equivalence (1)/(6) and its full-faithfulness proof; and Tag 0BY3, smoothness over a perfect field. The pre-existing model theorem supplies the model, and the existing morphism correspondence supplies the compatible arrows: those remain independent ingredients for the future worker. Four logged Mathlib searches (LeanFinder, Loogle, grep and LeanSearch) used two natural-language formulations and name/concept queries. Hits were rational maps from a function field, affine image factorizations, Weierstrass points, universally closed global sections, and IntermediateField structures. Reading RationalMap.lean lines 510-563 confirmed that equivFunctionField and ofFunctionField give rational maps into an existing scheme, without constructing a proper smooth intermediate model or extending both compatible maps. They are not a one-line match.

lem-sfb-frobenius-twist-geometric-integrality-affine states the scalar-extension and affine incarnation of the iterated relative Frobenius on an arbitrary geometrically integral k-scheme. I read varieties.tex Tags 0CC9 and 0CCG, including their Cartesian diagrams and the initial pair formula, and the statement of def-pc-geometrically-irreducible, which explicitly defines geometric integrality, not only geometric irreducibility. The construction is stated inline, so it is not a definition with unspecified data. The assertion includes how the affine opens and their inverse images fit the global arrow; it is more than the two-line balancing calculation. Four logged searches used both natural-language formulations, a Loogle tensor query and a relative-Frobenius/twist grep. The hits were semilinear ring/field Frobenius, inseparability exponents, coalgebra Frobenius identities and Witt-vector isocrystals, not the complete scheme statement. The existing Mathlib GeometricallyIntegral base-change instance covers the integrality clause, but not the stated affine incarnation and global projection-compatible comparison; so this complete helper remains unsplit rather than being mislabeled a Mathlib leaf.

## Not duplicates

lem-sfb-curve-intermediate-field-realization vs lem-sfb-curve-frobenius-separable-factorization: the helper realizes an arbitrary intermediate field with prescribed pullbacks; it asserts neither a Frobenius twist nor a separable final factor.
lem-sfb-curve-intermediate-field-realization vs lem-sfb-finite-curve-genus-monotonicity: genus comparison is a numerical inequality, not realization of an intermediate field and its two compatible morphisms.
lem-sfb-curve-intermediate-field-realization vs lem-trf-algclosed-curve-model: model existence starts from an already finitely generated transcendence-degree-one field; the new helper checks these hypotheses for an arbitrary intermediate field and constructs both compatible arrows factoring the specified map.
lem-sfb-curve-intermediate-field-realization vs lem-sfb-proper-curve-function-field-morphisms: the correspondence concerns maps between existing curves; it does not construct a curve realizing a specified intermediate field and a factorization through it.
lem-sfb-frobenius-twist-geometric-integrality-affine vs lem-trf-scheme-frobenius-finite-radicial: that node asserts finite/radicial properties for scalar-extended q-power Frobenius from a finite-field model; the helper concerns arbitrary characteristic-p base fields, twisted targets, geometric integrality and the tensor-to-ring map.
lem-sfb-frobenius-twist-geometric-integrality-affine vs lem-trf-relative-frobenius-finite: finiteness under local finite type does not state the scalar-extension comparison, geometric integrality or the affine formula of the helper, which assumes no finite type.
lem-sfb-frobenius-twist-geometric-integrality-affine vs lem-sfb-purely-inseparable-curve-frobenius: classification of a given purely inseparable curve map does not assert the helper's geometric integrality after arbitrary scalar extension or its affine chart map for arbitrary schemes.
lem-sfb-frobenius-twist-geometric-integrality-affine vs lem-sfb-smooth-curve-relative-frobenius-degree: that node proves degree p^n and smooth proper integral curve structure, not geometric integrality and the affine incarnation for arbitrary geometrically integral schemes.
lem-sfb-frobenius-twist-geometric-integrality-affine vs def-weil-relative-frobenius-geometric-fiber: that definition fixes a finite-field model and its scalar-extended endomorphism; it does not address arbitrary-field twists or prove their geometric integrality.
lem-sfb-frobenius-twist-geometric-integrality-affine vs d-relative-frob: the finite-field model definition includes an affine formula for a different scalar-extended relative map; its statement does not give the arbitrary-field geometric-integrality comparison required here.

The whole DAG was searched by tags and by statement keywords; blueprint_refs searches for intermediate field, relative Frobenius, curve factorization and Frobenius twist were read. The finite-field-specific definitions, field-subextension coefficient nodes and affine-line definition do not state either helper. No existing node states either complete helper. The blueprint ancestor command returns None, matching the inherited null from.node; the exact inherited clause and via chain are retained and the new helpers prepend the parent to that chain. No ancestry was invented.

## Review by Q33

I read the return and checked the actual JSON and Stacks passages together. The item still says exactly what it said before; its statement was not weakened. Tag 0CD2 supplies the positive-characteristic route; Tag 030K supplies the characteristic-zero case. I also read the current blueprint direct-images proof: its clause (3) is the inherited distant application; this repair does not replace its compactification or coefficient route. Both new nodes have full hypotheses and empty proof/proof_deps/proof_origin, leaving their arguments to separate future workers.

Parent step 1 uses the statement of lem-sfb-proper-curve-function-field-morphisms, which explicitly gives finiteness, finite generation, transcendence degree one and full faithfulness for smooth proper integral dimension-one curves. All of those hypotheses are present, and the definition of nonconstant is the same. Step 2 uses lem-weil-pbc-separable-first-purely-inseparable for the finite, hence algebraic, extension L/K: its statement explicitly gives the intermediate field, separability, pure inseparability, and equality E=L in characteristic zero. Thus the identity case needs no extra curve construction.

Step 3 uses the entire intermediate-field helper, not a construction hidden in its proof. Its statement expressly gives finite E/K and L/E, a smooth proper integral dimension-one model, both nonconstant arrows, their pullback formulas and the equality u=b a. These formulas identify the induced extensions with E/K and L/E, so the separability/pure-inseparability assertions from step 2 apply to exactly the right maps. Step 4 uses lem-sfb-purely-inseparable-curve-frobenius, whose statement gives n and h with a=h F. Its hypotheses hold for C and Z by step 3, with positive characteristic fixed in step 2. Setting v=b h gives v F=b a=u. Since h is an isomorphism, smoothness, properness, integrality, dimension one, nonconstancy and finite separability transfer exactly as in the old argument. Step 5 uses the new twist helper, whose statement provides geometric integrality, the second-projection k-structure and the exact affine formula including n=0. Its only geometric hypothesis, geometric integrality of C, is explicitly an item hypothesis. citations.json contains actual verbatim statements for all five steps, checked against the files read.

I tested the intermediate helper at E=K and E=L, which give Z=Y and Z=X with the expected identity factor. For X=Y=P^1 and f(t)=t^(2p) in odd characteristic, E=k(t^p) gives a purely inseparable first map and separable second map; in characteristic 2 one takes the maximal separable E=k(t^4), so no unjustified assertion about separability of a degree-2 map is used. In characteristic zero, E=L and the identity Frobenius factor recover the parent. For the twist helper, n=0 is identity base change and multiplication on tensors; X=Spec k gives a twist isomorphic to Spec k with second projection, not an erroneous k-linear absolute-Frobenius endomorphism. For a possibly imperfect k and n>0 the composite iota phi_n is still injective, so it is a legitimate extension for geometric integrality. On a chart, (ca) tensor b = a tensor c^(p^n)b is respected by the formula. No perfection assumption was smuggled into the helper.

Against B-E: the two helper statements introduce every object and cite definition nodes; the statements carry no proof sketch. The Stacks labels and tags were checked in tags/tags. Every non-elementary parent input is a cited statement; no definition is substituted for a theorem. Both helpers are independent of the parent as dependencies, with no circular proof reference. No step exceeds 2000 characters; the parent total is 2113. The extracted work is recorded below rather than discarded. There is no statement dispute, source correction, WANTED reference, SGA citation, or Mathlib leaf claimed without a full match. The prior direct use of the off-unit model lemma is now part of the intermediate helper's future work; its existing parent metadata was not edited.

## Unfinished work

The two new helper proofs are intentionally left unsplit, as the return requires, and can be assigned independently. No other item work remains after the required dry run and delivery succeed. Search results and this report remain reviewable.

## Preserved original argument and work assignment

Original steps 1 and 2 remain parent steps 1 and 2 verbatim. Original step 5 remains parent step 4 verbatim. Original steps 3 and 4 are the proof assignment of lem-sfb-curve-intermediate-field-realization; the complete arguments follow. Original step 6 is the proof assignment of lem-sfb-frobenius-twist-geometric-integrality-affine; its complete argument follows. Future workers can use the original model and morphism nodes explicitly named here; the new node statement itself contains no proof steps.

Original step 1 (uses: lem-sfb-proper-curve-function-field-morphisms):

Apply [lem-sfb-proper-curve-function-field-morphisms] to $u$. Write $K=k(D)$ and $L=k(C)$ and regard $K$ as a subfield of $L$ by $u^*$. The cited statement gives that $L/K$ is finite, that both fields are finitely generated of transcendence degree one over $k$, and that morphisms of these smooth proper integral curves are determined by their induced field embeddings.

Original step 2 (uses: lem-weil-pbc-separable-first-purely-inseparable):

By [lem-weil-pbc-separable-first-purely-inseparable], the separable algebraic closure $E$ of $K$ in $L$ is a subfield with $E/K$ separable algebraic and $L/E$ purely inseparable. If $\operatorname{char}k=0$, the same cited statement says $E=L$. Thus $L/K$ is finite separable. In this case $C'=C$, $F=\operatorname{id}_C$, and $v=u$ give all the assertions. Henceforth assume $\operatorname{char}k=p>0$.

Original step 3 (uses: elementary):

The intermediate field $E$ is finite-dimensional over $K$: it is a $K$-linear subspace of the finite-dimensional space $L$. Also $L/E$ is finite, because any finite $K$-spanning set of $L$ spans it over the larger field $E$. Choose a finite $K$-basis $e_1,\ldots,e_r$ of $E$ and field generators $t_1,\ldots,t_s$ for $K/k$ from step 1. Then $E=k(t_1,\ldots,t_s,e_1,\ldots,e_r)$, so $E/k$ is finitely generated. It has transcendence degree one: a transcendental $t\in K$ stays transcendental in $E$, while each $x\in E\subset L$ is algebraic over $k(t)$ since $L/k$ has transcendence degree one. These observations verify the precise field hypotheses needed in the next step.

Original step 4 (uses: lem-trf-algclosed-curve-model, lem-sfb-proper-curve-function-field-morphisms):

Apply [lem-trf-algclosed-curve-model] to $E/k$ to obtain a smooth proper integral dimension-one curve $Z$ with a $k$-isomorphism $\theta:k(Z)\xrightarrow{\sim}E$. By [lem-sfb-proper-curve-function-field-morphisms], the embeddings $k(Z)\xrightarrow{\theta}E\hookrightarrow L$ and $K\hookrightarrow E\xrightarrow{\theta^{-1}}k(Z)$ give nonconstant maps $a:C\to Z$ and $b:Z\to D$. Their composite induces the original inclusion $K\hookrightarrow L$, so the same correspondence gives $u=b\circ a$. With these embeddings $k(C)/a^*k(Z)$ is the finite purely inseparable extension $L/E$, and $k(Z)/b^*K$ is the finite separable extension $E/K$.

Original step 5 (uses: lem-sfb-purely-inseparable-curve-frobenius):

The map $a$ has smooth proper integral dimension-one source and target and finite purely inseparable function-field extension. Thus [lem-sfb-purely-inseparable-curve-frobenius] gives $n\geq0$ and a $k$-isomorphism $h:C^{(p^n)}\xrightarrow{\sim}Z$ with $a=h\circ F_{C/k,n}$. Set $C'=C^{(p^n)}$, $F=F_{C/k,n}$, and $v=b\circ h$. Then $v\circ F=b\circ a=u$. Since $h$ is a $k$-isomorphism, $C'$ is smooth proper integral of dimension one, $v$ is nonconstant, and $k(C')/v^*K$ is isomorphic to $k(Z)/b^*K$, hence finite separable.

Original step 6 (uses: def-pc-base-change, def-pc-geometrically-irreducible):

It remains to check geometric integrality and the displayed affine formula. By the fibre-product universal property [def-pc-base-change], for any field extension $k\to k'$ there is a canonical identification
$$(C^{(p^n)})_{k'}\cong C\times_{\operatorname{Spec}k}\operatorname{Spec}k',$$
where the right-hand map $\operatorname{Spec}k'\to\operatorname{Spec}k$ corresponds to the composite $k\xrightarrow{\varphi_n}k\to k'$. This is a field extension, so the right-hand side is integral by geometric integrality of $C$ and [def-pc-geometrically-irreducible]. On $\operatorname{Spec}A\subset C$, the pair defining relative Frobenius in step 5 induces the map $A\otimes_{k,\varphi_n}k\to A$ sending $a\otimes b$ to $a^{p^n}b$. Indeed the two factor maps are $a\mapsto a^{p^n}$ and the structure map $b\mapsto b$, agreeing on $k$ after the twist: $(ca)^{p^n}b=a^{p^n}c^{p^n}b$. This verifies the tensor relation and the second-projection $k$-structure. For $n=0$ the formula is $a\otimes b\mapsto ab$ under the canonical identity base change. All required clauses follow.
