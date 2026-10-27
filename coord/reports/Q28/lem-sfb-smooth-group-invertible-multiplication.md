## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothGroupInvertibleMultiplication` states the
node without changing its mathematical statement. It constructs restriction
homomorphisms, pointwise n-th power, its actual sheaf kernel, and the kernel
inclusion. The sole postponed theorem is
`AlgebraicGeometry.AlgebraicSpace.smoothGroup_invertible_multiplication`.
All definition data are explicit. The proofs inside the definitions only check
naturality and preservation of the existing operations.

Hypothesis and conclusion correspondence:

- A scheme S is `{S : Scheme.{u}}`. The arbitrary algebraic space over S is
  `(G : AlgebraicSpace S)`, using the recorded fppf-sheaf definition.
- The commutative group law is `(H : CommutativeSpaceGroup G)`: its `group T`
  gives all group operations and identities, and its `map_mul` and `map_one`
  give naturality. Natural inverse follows from these group homomorphisms.
  This uses only that structure, not `IsSmoothIntegralGroupSpace` and none of
  the latter predicate's separation, finite presentation or integral-fibre conditions.
- Smoothness on etale scheme charts is
  `hsmooth : MapIsLocally (@Smooth) (groupSpaceProjection G)`.
- A positive integer is `(n : ℕ) (hn : 1 ≤ n)`. This indexes exactly the integers
  at least one, including n = 1.
- Invertibility in every local ring is
  `hunit : ∀ s : S, IsUnit (n : S.presheaf.stalk s)`.
- `[n]` is `H.npow n`. Since the existing group structure is multiplicative,
  its component is `NPow.npow n x`, that is x raised to n, the source's n-fold sum.
  Naturality follows from `H.restrictionHom f` and `MonoidHom.map_pow`.
- Etaleness of multiplication is the first conjunct
  `MapIsLocally (@Etale) (H.npow n)`.
- `H.torsionSpace n` is exactly
  `enlargedFibreProduct (H.npow n) H.identity`, the sheaf fibre product
  G ×_{G,[n],e} S already bundled as an algebraic space. Its inclusion is
  `enlargedFibreProductFst (H.npow n) H.identity`.
- The second conjunct is
  `MapIsLocally (@Etale) (groupSpaceProjection (H.torsionSpace n))`, the
  asserted etale structure morphism to S.
- The third conjunct supplies a `CommutativeSpaceGroup` on this precise kernel,
  and requires that its inclusion preserve identity and multiplication. These
  equations force the induced group law: the inclusion is a monomorphism because
  it is the pullback of the section e from the terminal base. Inverses are also
  preserved by every group homomorphism. Thus this is the kernel group structure,
  rather than an unspecified group law on an unrelated space.
- The last conjunct quantifies over every `B : Over S`, thus every S' → S.
  `Functor.whiskerLeft (Over.map B.hom).op` restricts presheaves from S-schemes
  to S'-schemes. The displayed `IsPullback` uses the actual kernel inclusion,
  actual second pullback projection, `[n]`, and e. It says the restricted kernel
  square is still a pullback. The restricted G is precisely G_{S'} on test schemes;
  its multiplication and identity are the same pointwise operations. The
  restricted h_S is terminal on S'-schemes. Consequently this is exactly the
  canonical identification G[n] ×_S S' ≅ G_{S'}[n], fixed by the projections.
  It also respects the induced group law. No arbitrary comparison map or
  nonempty choice is substituted for that comparison.
- No properness, finiteness, connectedness, quasi-compactness or separatedness
  is included as a hypothesis or conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and the scheme's structure presheaf and stalks.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsAlgebraicSpace`; schemes and maps are retained in `Over S`.
- `Sheaf.AlgebraicGeometry.RegularGroupSpace`: `CommutativeSpaceGroup`,
  `CommutativeSpaceGroup.identity`, `groupSpaceProjection`, `groupSpaceBase`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `enlargedFibreProduct`
  and `enlargedFibreProductFst`, owned by the existing
  `def-sfb-space-sheaf-fibre-product` node and imported as a statement dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` and the base-change
  instance `Etale.etale_isStableUnderBaseChange`.

The five already landed nodes owning the additional interfaces are added to
`stmt_deps`: `def-sfb-smooth-integral-group-space`,
`def-sfb-space-morphism-properties`,
`def-sfb-space-sheaf-fibre-product`, `def-sbc-smooth-morphisms`, and
`def-weil-etale-morphism`. The enlarged-site theorem node is not a statement
dependency because these definitions are direct fibre-product constructions,
not choices from that theorem. Their recorded modules are public imports.
No new node or dependency repair is needed.

The recorded proof modules are imported without `public`:
`SpaceLocalPropertiesChartTest`, `SpaceLfpFormallyEtaleCriterion`,
`SpaceEtaleSourceAtlasDetection`, `AlgebraicSpaceFibreProductsEtaleCovers`, and
`ChartwiseEtalePermanence`. The smoothness and etale scheme base-change
modules are already public statement imports. At inspection time the nodes
`lem-sfb-space-relative-lfp-permanence`,
`lem-sfb-group-space-square-zero-kernel-module`,
`lem-sfb-smooth-space-affine-infinitesimal-lift`, and
`lem-sfb-unramified-etale-compatible-charts` have no recorded declaration or
Mathlib match, so there is no corresponding proof import yet. They are not
needed to type this statement and are not restated in this delivery.

Sources inspected: `literature/stacks-project/groupoids.tex`,
`lemma-group-scheme-addition-tangent-vectors` (0BF5) and
`lemma-abelian-variety-multiplication-by-d-etale` (0BFH), together with the
node's five-step infinitesimal proof. The docstring carries all five steps,
including the atlas conversion needed before etale base-change permanence.
No statement dispute or source correction is necessary.

Edge cases checked mathematically before writing:

- n = 1 gives identity multiplication and the trivial group kernel S.
- Empty S is allowed: invertibility is vacuous, and the statement remains valid.
- The trivial group G = S is allowed, including zero-dimensional fibres.
- For G_a, multiplication by a unit is an isomorphism; in characteristic p,
  n = p would fail etaleness, and is correctly excluded by `hunit`.
- G_m gives the etale group μ_n. Neither G_a nor G_m is required to be proper.
- Infinite constant etale groups are allowed, so no finiteness conclusion about
  the torsion kernel can be inferred or is asserted.
- The final quantifier includes identity, empty, nonflat and nonreduced base
  changes: no property of `B.hom` is assumed.
- Every S, test scheme and base-change scheme uses the scheme universe u.
  There is no independent smaller universe that would make a test vacuous.

Searches actually run:

- `msearch.py ... leanfinder`: “Multiplication by an integer invertible on the
  base of a smooth commutative group algebraic space is etale and the torsion
  kernel commutes with base change”. Eight results, principally ring etale
  base change and formal etaleness; no exact statement.
- `msearch.py ... leansearch`: “multiplication by n on a smooth commutative
  group scheme is etale when n is invertible on the base”. Eight results,
  including scheme etale smoothness/base change and abstract group divisibility;
  no exact statement.
- `msearch.py ... loogle 'nsmul, Etale'`: zero results with the service message
  `loogle: unknown identifier 'nsmul'`; this query was unavailable as a valid
  identifier search and is not treated as evidence of absence.
- A second valid Loogle query, `'"Etale", "pow"'`, returned only
  `StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x`, a polynomial
  identity unrelated to group-space multiplication.
- `msearch.py ... grep '(nsmul|npow).*[Ee]tale|[Ee]tale.*(nsmul|npow)'`:
  zero Mathlib matches.
- Direct `rg` of those expressions in `lean/WeilConjectures` and `lean/Sheaf`
  found `AlgebraicGeometry.etale_npow_id` in
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion`. Its full signature
  and docstring were read: it assumes an abelian variety over a field with
  characteristic p, so cannot supply the present arbitrary-base, nonproper,
  algebraic-space theorem. The torsion-kernel theorem there has the same extra
  abelian-variety hypotheses.
- Direct `rg` for this node id in both source trees found no declaration.
- Direct `rg` for natural commutative group spaces found and reused
  `RegularGroupSpace.CommutativeSpaceGroup`; it also found the existing
  `enlargedFibreProduct` construction. DAG records were then read for their
  owning nodes. No private replacement was introduced.
- Full proposed declaration names were searched in Mathlib, WeilConjectures,
  Sheaf, and `dag/lean_names_upstream.json`; no collision was found.

Validation: the module compiled cleanly through the prescribed `scompile.py`
against the server's published library. Initial elaboration faults in explicit
class projections and the qualified whiskering name were repaired. All variables
and universes are bound explicitly, `autoImplicit` is false, the file uses module
mode, and every line has at most 100 characters.

## Second reading by Q28

This is the author's second reading; the maintainer supplies the independent review.
I reopened the node and the complete final module and checked every clause above.
The arbitrary-base group hypothesis uses only `CommutativeSpaceGroup`, not the
stronger `IsSmoothIntegralGroupSpace`. Both occurrences of etaleness use the same
`MapIsLocally` chart convention as the node. The integer is positive and a unit in
every actual stalk. The fibre product has the correct orientation: first map
[n]:G → G, second map e:S → G; hence its second projection goes to S. The
inclusion homomorphism equations pin down the induced group operations. The
base-change square uses this same second projection and these same maps, after
restriction to every S'-scheme; it includes arbitrary and identity base changes.
No mathematical statement changed on this reading. I made explicit public
imports and added the already landed owning nodes to `stmt_deps`, so each reused
interface is recorded. The single theorem remains `sorry`; no missing proof
node was disguised as a definition or extra hypothesis.

## Repair of returned head 045ca7feb414

H2: replaced the statement dependency
`lem-trf-space-enlarged-etale-ringed-site-model` with the existing definition
node `def-sfb-space-sheaf-fibre-product`. I read the latter's statement and
`existing: true` record, and the definitions at
`EnlargedEtaleRingedSite.lean:230` and `:236`: they construct the actual sheaf
pullback and its first projection. They are not chosen from the enlarged-site
theorem. The public import now names `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`
instead of `SpaceCotangentRingMap`. The remainder of the Lean file, including all
definitions and the theorem signature, is unchanged from the returned delivery.
The node's `lean.note` and this report now cite the definition's owner.

Second reading of the repair: the new dependency states exactly the two reused
constructions. The kernel still has the same defining fibre product, projection,
induced group law, etaleness clauses and arbitrary-base-change square. No
mathematical or signature change was made. The current shared node was read to
check that all fields other than the permitted Lean record and added statement
dependencies remain identical; delivery bookkeeping refreshes the base through
the prescribed wrapper.
