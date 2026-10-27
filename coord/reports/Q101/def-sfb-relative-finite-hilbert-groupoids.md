## Worker report

The delivery defines `AlgebraicGeometry.RelativeFiniteHilbert.groupoid` in
`Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids`, together with its explicit
objects, arrows, pullback, target functor, represented relative fibre, induced map,
and full unramified-lci subcategory. No theorem of algebraicity, openness, or descent
for the Hilbert category is asserted. All three named theorem proofs are `sorry`;
their docstrings give the structural arguments, and their statements are the
composition, pullback, and map-over-the-base clauses of this definition node.
Every construction has real data. The only choices are Mathlib's cartesian lifts
and the inverse of a specified equivalence, both determined up to their relevant
canonical isomorphisms. No object or map is chosen from a bare existence axiom.

The complete source places read are examples-stacks.tex, section-hilbert-d-stack,
the construction before 05WC; criteria.tex, section-lci and equation-relative-map;
spaces-more-morphisms.tex, definition-lci (06C4); spaces-morphisms.tex,
definition-unramified (03ZH) and lemma-local-source-target (03MJ); divisors.tex,
definition-regular-immersion (063J); and more-morphisms.tex, definition-lci (069F).
The current blueprint's sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
was also read. This is a supporting definition, not the unit's statement.

Clause-by-clause rendering:

- The base scheme is `S : Scheme.{u}`. The scheme category has its existing object
  universe u+1 and morphism universe u. The object/morphism universes of the two
  based categories are independent explicit levels w₁/v₁ and w₂/v₂; no equality
  between them or with the scheme universes is imposed. The space-valued sheaves
  use the existing `AlgebraicSpace S` size convention.
- Stacks on the big fppf site are the two `IsFppfModuliStack` arguments of
  `groupoid` and `Lci`. This is the recorded fppf definition, not the recorded
  moduli module's étale-only `IsModuliStack`. The base-preserving morphism is
  `F : BasedFunctor X Y`. `IsFppfModuliStack` includes fibred-in-groupoids,
  sheaf gluing of arrows and effective object descent.
- A positive integer degree is `d : ℕ+`; its coercion to ℕ is used by the existing
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree`. Thus degree zero is not silently
  included in the source construction.
- The objects `(Z → T,y,x,α)` are `RelativeFiniteHilbert F d`: fields T, Z, p,
  finite, y and x give the schemes, the finite locally free degree-d morphism,
  and actual objects in the two fibres. These are not isomorphism classes.
- The α convention is reversed only in its encoding. Instead of choosing `p*y`
  and storing `α : p*y ≅ F(x)`, `comparison : F(x) → y` is an arrow over p,
  with `comparison_lift` recording that exact base arrow. In a category fibred
  in groupoids, factoring through the chosen cartesian lift of y along p gives
  the vertical isomorphism `F(x) ≅ p*y`, whose inverse is α. Conversely α gives
  precisely this arrow. This retains α and all automorphisms, and avoids a
  second independently chosen pullback object.
- An arrow over g consists of `Hom.g`, `Hom.h` and `Hom.cartesian`. The latter
  is `IsPullback h A.p B.p g` in Over S, hence is the cartesian scheme square.
  The fields b/b_lift and a/a_lift are the cartesian arrows over g and h,
  equivalently the isomorphisms `y ≅ g*y'` and `x ≅ h*x'` in the node.
  The equation `F.map a ≫ B.comparison = A.comparison ≫ b`, after inverting
  the comparison convention, is exactly `F(a) ∘ α = h*α' ∘ (b|Z)`.
- `category` uses componentwise identities and composition. The named
  `hom_operations` proof obligation supplies identity and composite pullback
  squares, lifts, and comparison squares; no categorical data are postponed.
- `base` remembers T and g. `Fiber T` is its actual fibre category, i.e.
  `H_d(F)(T)`. `groupoid` bundles the total category with this projection.
- `pullbackX`, `pullbackY`, their Arrow declarations, `pullbackComparison`,
  `pullback`, and `pullbackArrow` implement scheme fibre product, cartesian
  object pullback, and the uniquely induced comparison. The comparison uses
  `IsStronglyCartesian.map` and the scheme pullback equation. The named
  `pullback_properties` supplies only finite-degree stability, base identities,
  and the lifts/comparison equation needed to assemble these explicit data.
- The requested p_d is `target`, the actual functor taking A to A.y.val and
  arrows to their b component. It remembers the specified object, not its class.
- `discreteModuli` is reused for h_T and space-valued discrete groupoids.
  `relativeFiber y` is the node's explicit relative-fibre description, using
  Mathlib's `CostructuredArrow F.toFunctor y`: an object ξ comes with an arrow
  `F(ξ) → y`; `relativeProjection` takes its base arrow. Factoring that arrow
  through cartesian pullback gives exactly `(t,ξ,β : t*y ≅ F(ξ))`. Its arrows
  are the comparison-compatible arrows of ξ, and fibre arrows are isomorphisms.
  This is the explicit triple presentation of the same 2-fibre product already
  supplied by the dependency's iso-comma construction; it is not a new notion
  of representability.
- Representability itself is the existing
  `CategoryTheory.IsRepresentableByAlgebraicSpaces F` hypothesis of `Lci`.
  `Representative T y` is the fixed representative requested by the node:
  an existing algebraic space, its projection, and a based equivalence with
  this explicit triple category. Its `projection_compatibility` retains the
  map to T, rather than just an equivalence of underlying categories.
- `relativePoint` is the actual point `(p,x,α)` in that triple category.
  `representativePoint` applies the inverse representing equivalence;
  `representativeBaseIso` is its counit on scheme bases. `inducedMap` transports
  the resulting section along the inverse base isomorphism. Thus u is constructed
  from the specified representative and object, rather than an arbitrary map.
  `inducedMap_over` is the named property asserting `u ≫ projection = yoneda.map p`.
- `SpaceProperty P f` is exactly the stated chart test: V → B is representable,
  étale and surjective; U → E ×_B V is representable, étale and surjective;
  its composite to V is yoneda.map q; and P holds for q.left. Both surjectivity
  clauses are present, and the source chart is to the actual fibre product.
- `FlatLfp R` requires every representative's projection to have both `Flat`
  and `LocallyOfFinitePresentation` by that chart test. These are separate
  properties, exactly as in the node. `Lci` takes this hypothesis.
- `IsLciObject` requires `SpaceProperty IsUnramified` and `SpaceProperty SchemeLci`
  of the canonical induced map. `Lci` is `ObjectProperty.FullSubcategory` of
  precisely this predicate, retaining every arrow between its objects.
- `IsUnramified` is the dependency's locally-finite-type/open-diagonal conjunction.
  `SchemeLci` says at every source point there is an open neighbourhood and a
  factorization as a closed immersion followed by a smooth map. The closed
  immersion has the existing `CotangentPresentation.IsKoszulImmersion` property,
  i.e. locally finite Koszul-regular generators of its actual ideal. This
  reuses the recorded Koszul complex definition and permits length zero.
  No Noetherian or regular-sequence hypothesis has been added.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom`.
- def-weil-size-convention: metatheoretic only; explicit universe binders above.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: `Scheme.fppfTopology`, with its slice
  `.over S`, as used by the fppf stack predicate.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `IsFibredInGroupoids`,
  `discreteModuli`, `IsRepresentableByAlgebraicSpaces`; its full stack,
  2-fibre and representability signatures/docstrings were read.
- WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree:
  `Scheme.Hom.IsFiniteLocallyFree` and `IsFiniteLocallyFreeOfDegree`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, fst,
  snd, the pullback equation, and `IsPullback`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `Flat`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `LocallyOfFinitePresentation`.
- Sheaf.AlgebraicGeometry.UnramifiedMorphism: `IsUnramified`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, with their actual sheaf and scheme-test interfaces.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- WeilConjectures.RingTheory.KoszulRegularSequence:
  `RingTheory.Sequence.IsKoszulRegular`, used by the closed-chart predicate.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: `Etale`, used by the space chart tests.
- Added already-landed dependency def-sfb-fppf-stackification:
  Sheaf.CategoryTheory.SiteStackification, `IsFppfModuliStack`.
- Added already-landed dependency def-sfb-koszul-closed-immersion-chart:
  Sheaf.AlgebraicGeometry.LciCotangentPresentation,
  `CotangentPresentation.IsKoszulImmersion`.

The last two additions supply already-existing definitions; neither node nor module
is changed or delivered. The original statement and all other fields are unchanged.
The lci and chart-property helpers belong to notions explicitly expanded in the
item's own statement; they are not additional independent definition nodes.

Edge cases checked before and after writing:

- Empty T permits the empty cover in every positive degree, since the fibre-degree
  condition has no base points to test. Neither objects nor chart tests require
  Nonempty, connectedness, or nonempty fibres.
- Degree one is permitted; degree zero is excluded by ℕ+. No characteristic
  assumptions occur.
- For F = identity, the represented relative fibre is T, the induced map is p,
  and the unramified-lci finite locally free objects are the finite étale covers.
  The rank-two dual-number cover of a field belongs to H_2 but fails the
  unramified condition in L_2. Thus membership is not vacuous.
- Identity base arrows leave all fibre automorphisms visible: no skeleton,
  quotient, Subsingleton hypothesis, or unrelated set equivalence is used.
- Empty Koszul sequence is allowed; the ideal predicate then means zero ideal.
  Closed immersion and smoothness are still separate conditions.
- The same universal scheme universe is used throughout; stack object/hom
  universes remain independent and unchanged by the constructions.

Searches actually run (not inherited searches):

- msearch.py leanfinder, "relative finite Hilbert groupoid finite locally free
  covers maps to stack": eight hits, including Pseudofunctor.IsStack.toIsPrestack,
  finite morphism instances, fppf/étale site and local-finite-presentation notions;
  no relative finite Hilbert category.
- msearch.py loogle, `"Hilbert"`: twelve analytic Hilbert-space/Hilbert-basis and
  Hilbert-cube hits; no algebraic Hilbert groupoid.
- msearch.py grep, `HilbertStack|FiniteHilbert|RelativeHilbert`: zero Mathlib hits.
- msearch.py leansearch, "Relative finite Hilbert category of finite locally free
  covers with a map to a stack": eight site/precoverage/hypercover hits; no match.
- rg of lean/WeilConjectures and lean/Sheaf for
  `HilbertStack|FiniteHilbert|RelativeHilbert|def-sfb-relative-finite-hilbert-groupoids`:
  no existing declaration before this delivery.
- Further rg searches of the two source trees for fppf-stack, space-chart and lci
  vocabulary found the fppf stack definition and the Koszul closed-chart predicate
  listed above. Searches for Lci/LCI/LocalCompleteIntersection found field-relative
  predicates and the closed-chart predicate, but no general scheme-map lci predicate
  or the node's two-surjective-chart definition. Those clauses are rendered here
  exactly as the node expands them.

No statement correction, disputed statement, new definition node, or dependency
module repair is needed. The maintained independent delivery review remains to run.

## Second reading by Q101

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
