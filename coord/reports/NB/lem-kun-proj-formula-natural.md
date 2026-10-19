## Worker report

Recorded an existing declaration, with no new Lean module:
`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap`,
in `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange`,
lines 85–117 in the read-only upstream source. Its full signature and docstring were
read, and `scompile.py --source` confirmed the published source. The node copy changes
only `lean`. No new nodes, dependency repairs, or statement corrections are required.

The existing theorem states precisely the projection/exchange compatibility, with the
canonical identifications the node suppresses displayed explicitly. Here is the
hypothesis-by-hypothesis specialization:

- The four schemes and four arrows are its `X', X, Y', Y` and `g', f', f, g`.
  A square `sq : ChosenCartesianSquare g' f' f g`, from the recorded Cartesian-square
  module, is used through `sq.toCommSq`. Its chosen pullback isomorphism and projection
  equations remain the Cartesian data. The canonical inverse-image square depends on
  the commuting arrows, so the existing theorem applies to every such chosen Cartesian
  square, without requiring another choice or an assumption about the choice.
- The commutative coefficient ring is `Λ : Type (u + 1)` with `[CommRing Λ]`.
  Specialize `A` to `ModuleCat.{u + 1} Λ`. The category, Grothendieck, symmetric monoidal,
  monoidal closed, monoidal preadditive, and functorial flat-resolution instances are
  the standard module-category instances. `UpperStarPreservesFlat` is supplied by
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`. These are properties
  of the canonical categories, not additional hypotheses on Λ or on the morphisms.
- The node's `E` and `K` are the theorem's `K` and `L`, respectively. Their types are
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))` and the analogous
  category for Y. These are the constant-module coefficient encoding used by the
  recorded tensor and projection declarations, with unbounded integer-indexed complexes.

For clarity in matching the clauses below, put `A = ModuleCat Λ`, `θ =
derivedSquareUpperStarIso A sq.toCommSq`, and let `c_u(P,Q)` denote
`((leftDerivedUpperStarTensorComparison A u).app P).app Q`. This notation is only
explanatory text; no local notation or private copy is introduced in Lean.

- The top arrow is
  `L((g)^*[A]).map (((rightDerivedLowerStarProjectionMap A f).app E).app K)`.
- The exchange on the top-right vertex is
  `(derivedBaseChangeMap A sq.toCommSq).app
    (((derivedTensor A X).obj E).obj (L((f)^*[A]).obj K))`.
- The canonical tensor identification on the left of the diagram is
  `c_g(R((f)_*[A]).obj E, K)`. The exchange tensored with the identity is
  `((derivedTensor A Y').map ((derivedBaseChangeMap A sq.toCommSq).app E)).app
    (L((g)^*[A]).obj K)`.
- The bottom arrow is
  `((rightDerivedLowerStarProjectionMap A f').app (L((g')^*[A]).obj E)).app
    (L((g)^*[A]).obj K)`.
- The existing equality has common target
  `Rf'_*(g'^{-1}E ⊗ g'^{-1}f^{-1}K)`. Its left side explicitly ends with
  `R((f')_*[A]).map (c_g'(E, L((f)^*[A]).obj K))`. Its right side ends with
  `R((f')_*[A]).map
    (((derivedTensor A X').obj (L((g')^*[A]).obj E)).map (θ.hom.app K))`.
  Postcomposing both sides with the inverse of this last canonical isomorphism gives
  exactly the node's common target `Rf'_*(g'^{-1}E ⊗ f'^{-1}g^{-1}K)`.
  On the right it cancels; on the left it is the specified tensor/square identification
  following exchange. Thus no identification is silently replaced by an arbitrary map.
- Commutativity is the equality of these two composites in the theorem's conclusion.
  Neither projection nor exchange is assumed invertible.
- The node's final “Thus” clause follows by viewing this equality as a `CommSq`.
  When its four arrows are isomorphisms, use `CommSq.vert_inv` followed by
  `CommSq.horiz_inv` (in `Mathlib.CategoryTheory.CommSq`, lines 89–97), with each arrow
  regarded as `asIso`. This gives exactly `v⁻¹ ≫ a⁻¹ = b⁻¹ ≫ u⁻¹` for a forward
  square `a ≫ v = u ≫ b`: the same compatibility for the reversed square. This is
  the stated consequence of the equality, not an additional geometric assertion.

The recorded exchange interface uses exact inverse image `D((u)^*[A])`, whereas this
existing theorem uses `L((u)^*[A])`. These are canonically the same presentation:
`leftDerivedUpperStarIsoMapDerivedCategory A u : L((u)^*[A]) ≅ D((u)^*[A])`.
Read `UpperLowerStar.lean` lines 264–314 and `UpperLowerStarAdjunctionCompat.lean`:
`mapDerivedUpperStarLowerStarAdjunction_eq` states that the adjunction used by
`exactDerivedBaseChangeMap` is the left-derived adjunction transported along precisely
this isomorphism. The definition of `leftDerivedUpperStarComp` derives the ordinary
`upperStarComp` and then uses `leftDerivedFunctorCompIso` for exact functors.
`exactDerivedSquareUpperStarIso` instead descends that same ordinary square comparison
termwise with `mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso`. Consequently
the two square comparisons, and their adjunction mates, are the same after the stated
canonical transport. The existing theorem therefore uses the recorded exchange of
`def-kun-unbounded-exchange`, in its left-derived presentation. This is the same
identification already specified in the projection and monoidality dependency records.

Dependency declarations read and used:

- `def-weil-pbc-cartesian-square`: `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`, with `toCommSq` and its chosen pullback data.
- `def-kun-projection-formula-map`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`,
  `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`; its component and
  transpose declarations identify the counit/tensor mate.
- `def-kun-unbounded-exchange`: `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`,
  `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap` and
  `AlgebraicGeometry.Etale.exactDerivedSquareUpperStarIso`, through the canonical
  left-derived/exact comparison just described.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`, the K-flat-derived tensor bifunctor.
- The recorded proof dependency `lem-kun-inverse-image-monoidal`:
  `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`,
  `leftDerivedUpperStarTensorNatIso`, its hom `leftDerivedUpperStarTensorComparison`,
  and `leftDerivedUpperStarIsoMapDerivedCategory`.

The proof in the existing source is the node's common-mate argument:
`derivedSquareUpperStarIso_hom_tensor` verifies monoidality of θ from inverse-image
composition, and `Adjunction.rightAdjointProjectionMap_mate` uses the projection
transpose and the exchange transpose to equate the two routes. Reading the source
confirms that no invertibility of exchange is used. As an existing-declaration delivery,
there is no new module in which to add proof-dependency imports.

Edge cases checked against the hypotheses and expression: empty schemes are allowed;
zero E or zero K are allowed; the zero coefficient ring is allowed (no `Nontrivial`
instance); identity arrows are allowed; arbitrary unbounded complexes are allowed;
noninvertible exchange and projection maps are allowed in the forward square. The
coefficient universe is the project's established u+1 convention; any smaller ring
can be used in that universe, so no cardinality case is discarded. There is no added
properness, quasi-compactness, torsion, finiteness, or boundedness condition.

Searches performed on 2026-10-15:

- `msearch.py ... leansearch "Naturality of projection formula under derived base change"`:
  service unavailable, Internal Server Error; no absence conclusion drawn.
- `msearch.py ... leanfinder "Naturality of derived projection formula with base change
  for etale module sheaves"`: eight hits, mainly Kähler differentials and relative
  differentials; none is this theorem.
- `msearch.py ... loogle "rightAdjointProjectionMap, mateEquiv"`: zero hits, with unknown
  upstream identifier `rightAdjointProjectionMap`; not evidence of absence upstream.
- `msearch.py ... loogle "CategoryTheory.mateEquiv"`: twelve mate-calculus hits;
  these supply abstract identities, not the specialized projection/base-change square.
- `msearch.py ... grep "projectionFormula|projection_formula|mate.*tensor"
  CategoryTheory`: zero Mathlib hits for this pattern.
- `rg` of the upstream derived and adjunction directories for
  `leftDerivedUpperStarIsoMapDerivedCategory|squareUpperStarIso|derivedBaseChangeMap|
  projection.*[Nn]atural|Projection.*[Bb]aseChange` found the existing
  `LowerStarProjectionBaseChange.lean`; its theorem signature, docstring, and proof
  were read in full. This is the exact match used here.
- `rg` over `lean/Sheaf` for projection/base-change and naturality patterns found
  unrelated declarations and no second copy of this theorem.
- `rg` of `dag/lean_names_upstream.json`, upstream `WeilConjectures/`, and `lean/Sheaf`
  for `rightDerivedLowerStarProjectionMap_derivedBaseChangeMap|
  lem-kun-proj-formula-natural` found the theorem and its use by the lower-shriek
  projection/base-change theorem; no existing side declaration of this node was found.

Validation: `scompile.py NB lem-kun-proj-formula-natural
scratchpad/ExistingSpecialization.lean` succeeded cleanly in the local isolated overlay
and in server confirmation. It checked the exact specialization to `ModuleCat Λ`,
`ChosenCartesianSquare.toCommSq`, E and K, as well as the derived-adjunction transport,
the exact-inverse-image comparison, and the recorded exact-exchange declaration.
The scratch probe is outside `lean/` and is not delivered. No statement dispute found.

## Second reading by NB

I independently opened the immutable node, its blueprint source
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-proj-formula-natural.md`,
all four statement-dependency nodes and their recorded source declarations, and the
recorded monoidality proof dependency. I read Stacks `sites-cohomology.tex`,
`lemma-pullback-tensor-product` (07A4), `remark-base-change` (07A7),
`equation-projection-formula-map` (0B56), and `remark-compatible-with-diagram` (0E48),
including the surrounding projection-formula section. In particular the perfectness
hypothesis in the intervening projection-isomorphism lemma does NOT belong to the
projection-map construction or to 0E48. Those constructions use arbitrary objects of
unbounded derived categories. The blueprint's original word “ring” is resolved by the
already reviewed node to “commutative ring”, consistently with the tensor definitions;
this delivery does not change that statement.

The following is my object/hypothesis/conclusion inventory, with its Lean rendering
and verdict. Here `A` is specialized to `ModuleCat.{u + 1} Λ`, the upstream theorem's
`K,L` are the node's `E,K`, and `c_h(P,Q)` denotes the component of
`leftDerivedUpperStarTensorComparison A h` only in this report.

1. Four schemes X', X, Y', Y and maps g', f', f, g, with a specified Cartesian
   identification and commutativity: the recorded structure
   `ChosenCartesianSquare g' f' f g` has `isoPullback`, `hom_fst`, `hom_snd`, and
   inherited `CommSq`. The existing theorem is applied to `sq.toCommSq`.
   PASS: it covers every chosen Cartesian square, and the canonical inverse-image
   square depends on the commuting maps. It does not require a different choice of
   fibre product or any additional hypothesis. Its availability for general commuting
   squares is a more general existing theorem, specialized here to the node's objects.
2. Arbitrary commutative coefficient ring: `Λ : Type (u + 1)` and `[CommRing Λ]`.
   PASS: the standard `ModuleCat` instances supply the categorical hypotheses;
   `upperStarPreservesFlat_moduleCat` supplies the hypothesis for every scheme map,
   with no flatness assumption on a scheme map or a particular coefficient object.
   The chosen u+1 coefficient/module size is the same convention as the dependency
   records; resizing coefficients uses the usual universe lift, not a finiteness
   restriction on Λ. There is no `Nontrivial`, field, torsion, or invertibility hypothesis.
3. Arbitrary E in D(X_et,Λ) and K in D(Y_et,Λ): binders
   `K : DerivedCategory (Sheaf X.smallEtaleTopology A)` and
   `L : DerivedCategory (Sheaf Y.smallEtaleTopology A)` in the existing declaration.
   PASS: these are exactly the unbounded module-derived categories used by the
   recorded projection/tensor interfaces, not their bounded or constructible subcategories.
4. The top-left vertex is g⁻¹(Rf_*E tensor K): the domain of
   `L((g)^*[A]).map (((rightDerivedLowerStarProjectionMap A f).app E).app K)`.
   Its target is the displayed top-right vertex. PASS: this is the recorded projection
   morphism pulled back along g, with the same argument order.
5. The left edge consists of the monoidal identification c_g followed by exchange
   on E tensored with the identity on g⁻¹K: the first two factors of the existing
   equality's right side are `c_g(R((f)_*[A]).obj E,K)` and
   `((derivedTensor A Y').map ((derivedBaseChangeMap A sq.toCommSq).app E)).app
   (L((g)^*[A]).obj K)`. PASS: only the E-factor is exchanged. The tensor is exactly
   `derivedTensor` from `def-kun-derived-tensor`, with no new tensor construction.
6. The bottom edge is PF_f' at g'⁻¹E and g⁻¹K: the third factor on the right is
   `((rightDerivedLowerStarProjectionMap A f').app
   (L((g')^*[A]).obj E)).app (L((g)^*[A]).obj K)`.
   PASS: its target is Rf'_*(g'⁻¹E tensor f'⁻¹g⁻¹K), the node's bottom-right vertex.
7. The right edge is exchange on N = E tensor f⁻¹K, followed by the canonical
   tensor/square identifications. The left side of the theorem is g⁻¹PF_f followed
   by `(derivedBaseChangeMap A sq.toCommSq).app N` and `R((f')_*[A]).map
   (c_g'(E,L((f)^*[A]).obj K))`. Its common target is the alternative presentation
   Rf'_*(g'⁻¹E tensor g'⁻¹f⁻¹K). The final factor of the right side is Rf'_* of
   tensoring the identity with `(derivedSquareUpperStarIso A sq.toCommSq).hom.app K`.
   PASS: this last factor is an isomorphism. Postcomposing the equation with its
   inverse cancels it on the right, and supplies precisely the missing square
   identification on the left. Thus the existing equality is equivalent to the
   displayed square, rather than an equality to a weaker or arbitrarily chosen map.
8. The exchange in the node is the recorded `exactDerivedBaseChangeMap`.
   I opened `ExactUnboundedExchange.lean`, `DerivedUnbounded.lean`,
   `UpperLowerStar.lean`, and `UpperLowerStarAdjunctionCompat.lean` to check this
   object, rather than infer it from similar names. PASS: the exact square is the
   descent of `squareUpperStarIso`; the left-derived square composes the derived
   ordinary `upperStarComp` maps. The comparison
   `leftDerivedUpperStarIsoMapDerivedCategory` identifies these descent presentations.
   `mapDerivedUpperStarLowerStarAdjunction_eq` identifies their adjunctions, and
   `conjugateEquiv_leftDerivedUpperStarComp_hom` explicitly identifies the conjugates
   of their composition comparisons. Taking the mates therefore gives exactly the
   recorded exchange after canonical transport. No base-change invertibility is used.
9. The conclusion is equality of top-then-right and left-then-bottom, for all the
   objects in 1–3. PASS: this is the conclusion of
   `rightDerivedLowerStarProjectionMap_derivedBaseChangeMap`, with the canonical
   target change in 7. Quantifiers remain square, E, K with no intervening hypotheses.
10. Conditional inverse compatibility: when the four displayed arrows are
    isomorphisms, the reversed square commutes. PASS: I read Mathlib
    `CategoryTheory/CommSq.lean`, `vert_inv` and `horiz_inv`. Apply these successively
    to the forward `CommSq`, using `asIso` for the arrows. For a forward equality
    `a ≫ v = u ≫ b`, the reversed equality is
    `inv v ≫ inv a = inv b ≫ inv u`. This clause is an immediate equivalent-square
    consequence, with no extra geometric assertion; it does not assume invertibility
    in the forward statement.

The existing proof matches the four node steps: first
`derivedSquareUpperStarIso_hom_tensor` establishes monoidality of theta through the
canonical composition comparisons. Then `Adjunction.rightAdjointProjectionMap_mate`
applies the inverse adjunction Hom bijection injectively, expands the two transposes,
uses the defining projection counit equation and the exchange counit equation, and
uses tensor compatibility/naturality to identify them. Finally the inverse-square
consequence is the calculation in item 10. I read the generic mate theorem's signature
and proof, not just its name. No additional theorem is proved or postponed in this
delivery. Because this is an existing declaration, there is no new module requiring
blueprint docstrings or proof imports, no data definition, and no hollow construction.
There are no new nodes, dependency modules, or statement correction to audit.

Edge cases: empty schemes and identity maps are admitted by the scheme/square binders;
zero E and zero K by the whole derived-category binders; the zero ring by `[CommRing Λ]`
without `[Nontrivial Λ]`; all characteristics and infinite rings are allowed. Arbitrarily
unbounded complexes, including a complex concentrated in degree zero, are admitted.
There is no index set or n parameter, so an empty indexing case and n = 0 impose no
additional condition. I checked explicit universe binders `u' u` and all category
instances in the source; the specialization uses the dependency size convention.
There is no hidden Noetherian, separatedness, properness, quasi-compactness, or
boundedness requirement, and neither exchange nor projection is presumed invertible.

Independent searches on 2026-10-15, using different terms from the worker:

- LeanFinder via `msearch.py`: “Compatibility of pushforward projection morphisms with
  Beck Chevalley mates” returned eight exponentiable-morphism pushforward-composition
  results; these concern over categories, not this unbounded étale square.
- Loogle via `msearch.py`: `CategoryTheory.CommSq.vert_inv` returned the exact general
  inverse-square lemma; its source and `horiz_inv` were read as described above.
- Grep via `msearch.py`: `ProjectionMap|projectionMap` in Mathlib CategoryTheory
  returned zero hits. Independently, `rg` in all upstream `WeilConjectures/` for
  `projection.*(base.change|mate)|rightAdjointProjectionMap_mate|ProjectionMapCompat`
  found the abstract mate theorem and the exact existing étale specialization.
  I opened both. An exact-name `rg` in Mathlib found no copy. An independent `rg` in
  `lean/Sheaf` for projection/base-change, naturality, and mate terms found schemes'
  projection-mate and ringed-site projection interfaces, not another instance of this
  naturality theorem. The upstream lower-shriek variants have different functors.
  These searches support using the worker's existing attachment and writing no duplicate.

Mismatches and changes: no mathematical or signature mismatch found; no module or node
record changed by this second reading. I appended this independent inventory, source
checks, universe/edge-case audit, and search results. A direct comparison verified that
`lean.statement` is verbatim the source signature, and comparison with the base node
verified that only `lean` differs.

Validation: independently reran
`scompile.py NB lem-kun-proj-formula-natural scratchpad/ExistingSpecialization.lean`.
Both the isolated local compile and server confirmation passed, each in 2.2 seconds,
without warnings or errors. It elaborates the module-category specialization and
`ChosenCartesianSquare.toCommSq`, plus the exact/left-derived comparison and adjunction
transport. `scompile.py --source` independently confirmed the live source of the
recorded theorem. The scratch file is not a delivered module. Delivery dry-run and
final delivery perform their own existing-declaration compilation/preflight.
