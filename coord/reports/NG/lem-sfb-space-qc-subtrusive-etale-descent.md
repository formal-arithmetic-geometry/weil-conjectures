## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiCompactSubtrusiveEtaleDescent` states
`AlgebraicGeometry.AlgebraicSpace.quasiCompact_subtrusive_etale_descent`, with
one postponed theorem proof. No definition, auxiliary theorem, or dependency
interface is introduced or replaced. The mathematical statement is unchanged; the chartwise-etale definition-owner citation
is added in the repair below.

Source read: David Rydh, *Submersions and effective descent of étale morphisms*,
author version dated 2010-03-03, https://davidrydh.se/papers/submersion20100305.pdf,
Theorem (5.17), printed p.22; Notation (5.1) and Remark (5.2), printed pp.17–18;
Remark (2.5)(2c), printed p.8. The theorem is effective E_qc descent; the remark
permits algebraic-space bases and makes explicit the standing absolute
quasi-separatedness convention. Remark (2.5)(2c) supplies the open-surjective
sufficient condition. The repair below adds only a missing definition-owner citation.

Hypotheses and clauses, matched individually:

- The base scheme is `{S : Scheme.{u}}`, with explicit universe `u`. All spaces,
  scheme tests and sheaf values use the existing size convention; no auxiliary
  smallness, finiteness or universe-equality assumption is imposed.
- `H H' : AlgebraicSpace S` and `p : H' ⟶ H` introduce precisely the two
  algebraic spaces and their map. Morphisms are the existing full-subcategory
  sheaf maps, not representable maps supplied as additional data.
- `_hH : IsAbsolutelyQuasiSeparated H` and `_hH' :
  IsAbsolutelyQuasiSeparated H'` are absolute quasi-separatedness. The definition
  tests quasi-compactness of affine-chart intersections, equivalently the
  absolute diagonal; it does not merely use the diagonal relative to S.
- `MapIsQuasiCompact p.hom.hom` is quasi-compactness on every affine scheme
  test. This is the existing topological finite-subcover predicate on the
  actual presheaf pullback, with no atlas selected.
- `MapIsUniversallySubtrusive p.hom.hom` uses the existing constructible
  quotient and specialization-pair lifting predicates on all affine tests.
  `Topology.IsQuotientMap` includes surjectivity. `pointConstructibleTopology`
  is final over all representable étale affine scheme charts and uses Mathlib's
  constructible topology on each chart. Its specialization condition is
  `y₁ ⤳ y₀`, precisely `y₀ ∈ closure {y₁}`, with both preimages required to
  have those specified images. Thus none of the three topological conditions
  has been weakened.
- `∀ (E' : AlgebraicSpace S) (f : E' ⟶ H')` introduces the given étale object.
  `MapIsQuasiCompact f.hom.hom`, `IsChartwiseEtale f`, and
  `IsAbsolutelyQuasiSeparated E'` express its three given properties.
- `D : Over.DescentDatum p (Over.mk f)` is the already defined, category-generic
  Yoneda transport form of precisely the specified overlap isomorphism. Its
  `transport_homMk_comp` gives naturality, `transport_self` gives the diagonal
  identity, and `transport_transport` gives the triple cocycle. Swapping the
  two arguments gives inverse transport. Conversely evaluating the overlap
  isomorphism on generalized points gives this transport; the Yoneda lemma
  recovers that isomorphism. This is the same datum, not an existence or
  effectivity hypothesis. The generic declaration applies directly to the
  category of algebraic spaces, without changing its definition.
- `∃ (E : AlgebraicSpace S) (g : E ⟶ H) (q : E' ⟶ E)` gives the descended
  algebraic space and its structural map, together with the comparison
  projection. `IsAbsolutelyQuasiSeparated E`, `MapIsQuasiCompact g.hom.hom`,
  and `IsChartwiseEtale g` give every requested property of E and E → H.
- `IsPullback q f g p` says this very square identifies E' with E ×_H H'
  over H'. Algebraic spaces form the full subcategory of fppf sheaves closed
  under the existing sheaf fibre products, by
  `fibreProduct_isAlgebraicSpace`; its categorical pullback property is
  therefore exactly this sheaf fibre-product identification. The comparison
  square is equivalent to the requested isomorphism in the other direction.
- For every algebraic-space generalized point T, maps `a b : T ⟶ H'` with
  the same composite to H, and `x : Over.mk a ⟶ Over.mk f`, the equation
  `(D.transport a b h x).left ≫ q = x.left ≫ q` states that the specified
  transport keeps the E-coordinate fixed. In the pullback square there is
  exactly one point over b with that E-coordinate. This is exactly agreement
  of D with the canonical descent datum, including its specified isomorphism,
  not just descent of the underlying object. No arbitrary comparison map
  has replaced the canonical datum.
- The second conjunct has `MapIsUniversallyOpen p` and
  `Function.Surjective (mapPoint p.hom.hom)` implying
  `MapIsUniversallySubtrusive p.hom.hom`. It is outside the first conjunct's
  quasi-compactness and subtrusiveness assumptions, so neither condition
  makes this sufficient-condition assertion tautological. The common base
  and source quasi-separatedness hypotheses remain in force.
- No flatness, finite presentation, separatedness, representability, or
  quasi-compactness of H or H' themselves is assumed. In particular
  quasi-compactness is relative for p, f and g, as the node requires.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its full
  locally-affine locally-ringed-space definition and morphism category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, and their docstrings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, including its sheaf pullback and universal
  property; `etaleCover_pullback` and `etale_fibreProduct_isScheme`.
- `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`:
  `chartwise_etale_permanence`; its underlying `IsChartwiseEtale` is in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` and quantifies over every
  representable étale scheme-source chart.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace` and `pointImage`, on the existing field-valued point
  quotient (not an additional point construction).
- `Sheaf.AlgebraicGeometry.SpaceSubtrusive`: `MapIsUniversallySubtrusive`
  and `MapIsSubtrusive`; their topology is the exact
  `pointConstructibleTopology` in `SpaceConstructibleTopology`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact` and
  `mapPoint`, reused as the existing canonical helpers.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsUniversallyOpen` (arbitrary algebraic-space base changes).
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum` and its field signatures, and
  `DescentDatum.IsEffective` as the model for the explicit compatibility
  condition. Its docstring explicitly identifies transport with the overlap
  isomorphism and cocycle and the effective pullback-square condition.

The last five definition nodes were added to stmt_deps under the authorization
for already landed notions. They already have usable records. No new nodes or
dependency modules were needed. Every already stated proof-dependency module
is imported with plain `import`, except the chartwise-etale statement dependency
which is public; the size-convention node has no module. Proof dependencies
without Lean records are not invented or needed to type this stage-2 statement.
The ten-step proof docstring records the retained full proof route, including
finite-presentation approximation, descent of the inverse and finitely many
cocycle equations, flat/proper refinements, affine atlas reduction and gluing.

Edge cases checked before writing:

- Empty H and H' are allowed; no Nonempty binder or chosen point appears.
  The empty étale object and empty descended object satisfy the same clauses.
- Empty source over a nonempty target is excluded by actual surjectivity in
  subtrusiveness, as required, rather than by an additional hypothesis.
- Identity p is permitted, including arbitrary identity descent data: diagonal
  transport makes them the canonical identity datum and the pullback square
  supplies the same object over H.
- Nonseparated étale E' is permitted; only its absolute quasi-separatedness is
  required. No representation by a scheme or separatedness is imposed on E.
- The base S itself need not be quasi-separated. Absolute quasi-separatedness
  uses the existing affine-intersection predicate, not a relative diagonal.
- Neither p nor H,H' is required to be of finite presentation or flat. The
  proof's finite-presentation stages occur solely in the docstring, not as
  hypotheses restricting the theorem.
- No test-universe independent of u is introduced; no directed system is
  introduced into the statement. All existing scheme tests are retained.

Searches actually run:

- msearch leanfinder: “Quasi compact universally subtrusive morphisms are
  effective descent for quasi compact etale algebraic spaces”: 8 hits,
  headed by scheme property descent along flat qc covers; none states this
  algebraic-space object-effectivity result.
- msearch loogle: `Over.DescentDatum, IsEffective, AlgebraicSpace`: 0 hits;
  the service reports unknown identifier `Over.DescentDatum` (it is upstream,
  not Mathlib). Local source reading resolves the actual generic declaration.
- msearch leansearch: “descent datum algebraic space etale universally
  subtrusive”: 8 hits, including general pseudofunctor descent data and scheme
  étale topology, with no matching object-effectivity statement.
- msearch grep: `Subtrusive|subtrusive|effective.*descent`, Mathlib
  `AlgebraicGeometry`: 0 hits.
- rg in `lean/WeilConjectures`: `subtrusive|Subtrusive`, and grep of the exact
  item id: no matches. The separate source read of generic `Over.DescentDatum`
  found the exact reusable datum and its effectivity condition.
- rg in `lean/Sheaf`: subtrusive/étale/descent patterns find the existing
  topology-calculus and scheme flat/proper refinement modules, not this
  object-effectivity theorem. Searches for `MapIsUniversallySubtrusive`,
  `IsAbsolutelyQuasiSeparated`, `DescentDatum`, and quasi-compactness helpers
  located all reused notions. The chosen full declaration name has no match
  in Mathlib, upstream, or the project before this delivery.

Validation: scompile.py compiled the single module cleanly in both sandbox and
library module modes (3.7 s and 1.5 s). `autoImplicit` is false; u is explicit;
there are no local notation/instance declarations, hidden data choices, or
proofs other than the single expected `sorry`. No statement is disputed.

## Returned delivery repair

H2 (returned immutable head 94eaf404a25f): added the landed owner
`def-sfb-space-chartwise-etale-morphism` to `stmt_deps` and cited it
immediately after “chartwise etale” in the statement, retaining the permanence
theorem citation. Read its definition node and the exact declaration
`AlgebraicGeometry.AlgebraicSpace.IsChartwiseEtale` at
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, line 47: every
representable étale scheme chart remains representable étale after composition.
This is exactly the predicate used for f and g in the delivered Lean.
The module is byte-for-byte the returned module; its existing public imports
already expose the definition. The maintainer's advisory to use D.IsEffective
did not request a change; the explicitly stated effective realization is retained.

Compared the sandbox node with current main: the statement before this repair
agrees verbatim; main has the original six statement dependencies and no Lean
record. The repair retains the five previously delivered owner dependencies,
adds this sixth owner, and preserves all main fields other than the authorized
statement citation, dependencies, Lean record, and statement_change metadata.
The delivery wrapper rebases this packet onto the current main tip.

## Statement corrected

This is a citation-only correction requested by the maintainer, not a change
to the mathematical statement. Source: Rydh Theorem (5.17) and Remark (5.2),
with the existing chartwise-etale definition (Stacks 03FR/03G0) now cited directly.
The original statement was:

Let $S$ be a scheme [def-pc-scheme], with universes [def-weil-size-convention]. Work with algebraic spaces over $S$ [def-trf-algebraic-space], their sheaf fibre products [lem-trf-space-fibre-products-etale-covers] and point topology [def-a1-space-point-topology]. A space is quasi-compact if its point space has a finite subcover for every open cover; it is quasi-separated if its absolute diagonal over $\operatorname{Spec}\mathbf Z$ is quasi-compact on affine scheme tests. A morphism is quasi-compact if its pullback to every affine scheme test has quasi-compact source. On scheme affine charts the constructible topology is generated by quasi-compact opens and their complements; on an algebraic space $X$ give $|X|$ the final (quotient) topology of the constructible topologies of its representable etale affine scheme charts, as in Rydh Remark (1.8). Call $p:H'\to H$ universally subtrusive if for every affine scheme $T$ and morphism $T\to H$, the point map of $H'\times_HT\to T$ is surjective and a quotient map for the constructible topologies, and every specialization pair $t_0\in\overline{\{t_1\}}$ in $|T|$ lifts to a pair $t'_0\in\overline{\{t'_1\}}$ in $|H'\times_HT|$. Let $p$ be quasi-compact and universally subtrusive, with $H,H'$ quasi-separated. Let $E'\to H'$ be quasi-compact and chartwise etale [lem-trf-space-chartwise-etale-permanence], with $E'$ quasi-separated. Suppose an isomorphism $\theta:p_1^*E'\xrightarrow{\sim}p_2^*E'$ over $H'\times_HH'$ is the identity on the diagonal and satisfies $p_{23}^*\theta\circ p_{12}^*\theta=p_{13}^*\theta$ on the triple fibre product. Then there exist a quasi-separated algebraic space $E$, a quasi-compact chartwise etale map $E\to H$, and an isomorphism $E\times_HH'\simeq E'$ identifying the canonical datum with $\theta$. In particular, the universal-subtrusiveness hypothesis holds whenever $p$ is universally open and surjective on point spaces. No flatness or finite-presentation hypothesis on $p$ is required.

The only text addition is `[def-sfb-space-chartwise-etale-morphism]`
at the first explicit “chartwise etale” citation. The node's statement_change
records the old statement verbatim and the main branch's old dependency list.
Full citer audit of both stmt_deps and proof_deps found:

- `lem-sfb-space-open-surjection-etale-descent`: holds true. Only the chartwise-etale definition-owner citation is added; application of effective descent to each quasi-compact saturated open is unchanged.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
