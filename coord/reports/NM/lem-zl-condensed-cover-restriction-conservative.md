## Worker report

The module `Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative` states
`AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative` with one `sorry`.
It defines no new objects and proves nothing. The node is unchanged except for `lean`.
No statement correction, disputed assertion, new node, or dependency module is needed.

I read the node and all ten statement dependencies, including their Lean records and
source declarations/docstrings, and the additional proof dependencies. I read the local
Hemo--Richarz--Scholbach PDF: Section 3 defines arbitrary commutative condensed rings,
Lambda_X = p_X^{-1} Lambda and exact inverse image, and Lemma 4.5's proof says restriction
along a w-contractible affine cover is conservative. The node's six proof steps extend
this to arbitrary covers by the cover-local sheaf criterion and cohomology. The theorem
keeps the node's ordinary unbounded derived-category interpretation.

Hypotheses and clauses, matched to the Lean signature:

- A commutative condensed ring is `(Λ : Profinite.CondensedRing.{u})
  [IsCommMonObj Λ.X]`. This is the general ring-object category on the coherent profinite
  site. No presentation by a topological ring, finiteness, or discreteness is imposed.
- An arbitrary scheme is `(X : Scheme.{u})`, with no geometric hypotheses.
- The covering family is `(𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X)`.
  `Scheme.Cover` is `Precoverage.ZeroHypercover`: it bundles the type `𝒰.I₀`, schemes
  `𝒰.X i`, maps `𝒰.f i`, and membership in the specified precoverage. That precoverage is
  the fpqc weakly-etale precoverage, not merely joint surjectivity. Each map is therefore
  an object of the small pro-etale site. Universes `u` and `v` are explicitly bound;
  `v` is independent and imposes no finiteness or nonemptiness restriction.
- Lambda_T is the published `condensedRingObj Λ.X T`, the underlying object of
  `coefficientRing T Λ`. Its construction is `upperStarFromPoint T` applied to the
  ring object, with the transported unit and multiplication.
- D(T,Lambda) is `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
  (condensedRingObj Λ.X T))`. This is the published internal-module presentation of
  sheaves of modules: the action is a sheaf morphism from the tensor product, hence
  exactly the sectionwise bilinear action with restrictions; its morphisms are linear
  sheaf morphisms. The sectionwise presentation `ringedSiteModules` is reexported by its
  recorded module; no second module category is defined. This internal-module encoding
  is also the one used by the consuming `condensed_dualizable_iff_proetale_cover`.
- The specified u_i^* = Lu_i^* is
  `(CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory`.
  `upperStar` is inverse image of abelian sheaves and extension along the actual
  `condensedPullbackHom Λ.X (𝒰.f i)`, not an arbitrary identification. It is exact.
  `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory` identifies this exact
  levelwise functor with the total left derived functor. The site-localization and
  arbitrary-ring/abelian inverse-image clauses of the recorded localization lemmas
  identify it with the node's restriction. This explanatory identification introduces
  no additional hypothesis or extra conclusion.
- The first conjunct universally quantifies `K`, `L` and `f : K ⟶ L`, then states
  `IsIso f ↔ ∀ i : 𝒰.I₀, IsIso (...map f)`. Thus both directions of joint conservativity
  hold for every derived morphism, not just chain maps or maps from bounded complexes.
- The second conjunct universally quantifies `K` and states
  `(∀ i : 𝒰.I₀, IsZero (...obj K)) → IsZero K`. `IsZero` expresses zero as an object
  of the category, without asking for equality to a selected representative of zero.
  This is precisely the final equivalent zero-detection assertion of the node.

Dependency declarations used and imported:

- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing` (transparent `Mon` of profinite abelian sheaves).
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`, `Scheme.proetalePrecoverage`.
- `sk-def-sfb-pulled-back-coefficients` and `sk-def-sfb-coefficient-morphisms`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`,
  `condensedPullbackHom`, `coefficientPullbackIso` and its invertibility instance.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`. The actual coefficient input is a tensor ring
  object, so the already published `CategoryTheory.Mod` supplies its internal encoding.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `DerivedCategory.Q` and `HasDerivedCategory`.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`. Although its primary
  declaration is the constant specialization, its public import of
  `ProEtaleOperationsCanonicalAdjunction` reexports the full arbitrary-ring-sheaf
  operations `Scheme.proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`,
  `proEtaleRingDerivedPullback`, and their exactness and adjunctions from
  `ProEtaleOperations`. This general interface is present, not a missing prerequisite.
  For the condensed ring-object encoding the exact published operations are
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar` and
  `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`, from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` and
  `.Derived.UpperLowerStar`. No constant-ring specialization is used for Lambda.
- `lem-weil-proetale-weakly-etale-localization`:
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
  `AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization`, clause (1).
- `lem-sfb-proetale-object-inverse-image-restriction`:
  `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`,
  `AlgebraicGeometry.Scheme.proEtaleObjectInverseImageRestriction` and
  `ProEtaleObjectRestrictionComparison`, the arbitrary abelian- and ring-sheaf clauses.
- Additional proof imports: `Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`,
  `Scheme.proetale_site_properties`; `Mathlib.CategoryTheory.Sites.LocalProperties`,
  `CategoryTheory.Sheaf.isIso_of_coversTop`; and
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`,
  `CategoryTheory.Functor.homologyFunctorIso`; and
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.isIso_iff`. These are all the additional stated proof dependencies.

Edge cases checked against the statement and source:

- The empty covering of the empty scheme is allowed: no `Nonempty 𝒰.I₀` is assumed.
  The empty covering makes all module sheaves zero, so both conclusions are correct.
  An empty family over a nonempty scheme cannot satisfy the bundled covering condition.
- Infinite coverings and non-quasi-compact schemes are included. Cover membership retains
  the actual fpqc local finite-affine refinement condition. No cover is replaced by a
  globally finite cover.
- The zero condensed ring is allowed; its module categories are zero categories and
  both assertions hold. No nontriviality or invertible-prime hypothesis was introduced.
- Arbitrarily unbounded complexes and arbitrary derived morphisms are quantified. The
  argument uses every integral cohomology degree, rather than bounded-below resolutions.
- Identity covers and covers by non-monomorphic weakly-etale arrows are included;
  no open-immersion or monomorphism hypothesis appears.
- The site is the small pro-etale site with objects at universe `u + 1`, arrows at `u`,
  and abelian coefficients at `u + 1`; no equality of those site universes was imposed.

Searches performed (all on 2026-10-18):

- `msearch.py ... leanfinder "Restrictions of derived module sheaves along a pro-etale
  covering family with condensed coefficients jointly detect isomorphisms"`: eight
  results, including `CondensedMod.ofSheafProfinite`, solidification and dense-subsite
  restriction results; none is the derived condensed-coefficient statement.
- `msearch.py ... loogle "CategoryTheory.Sheaf.isIso_of_coversTop,
  DerivedCategory.isIso_iff"`: zero hits. The known individual ingredients were opened
  directly and their full signatures/docstrings checked.
- `msearch.py ... grep "isIso_of_coversTop|mapDerivedCategoryHomologyFunctorIso|CoversTop"
  CategoryTheory/Sites`: twenty hits, including `LocalProperties.lean:35,68` and
  `CoversTop/Basic.lean:41`. These concern sheaves before deriving.
- `msearch.py ... leansearch "Derived restriction along a pro-etale covering family
  detects isomorphisms for condensed module sheaves"`: eight results, including
  `Scheme.Modules.restrictFunctorIsoPullback` and condensed solid/discrete criteria;
  none states this theorem.
- `rg` of `condensed.*(conservative|cover)|cover.*(conservative|isIso)` and the item id
  in upstream `WeilConjectures` and side `lean/Sheaf` found the ordinary-sheaf theorem
  `ProEtale.isIso_of_isIso_localizationRestriction` in
  `SixFunctors/ProEtale/LowerShriek/OpenImmersion/Conservative.lean`, plus adic-cover
  variants and the parent condensed-lisse-locality theorem. I read the ordinary-sheaf
  theorem in full: its objects are `Sheaf ... A`, not derived module categories.
  The adic variants have different coefficient categories. The parent uses this item;
  it does not already state joint conservativity. No duplicate theorem was found.
- `grep -rn` for this item's id in upstream `WeilConjectures` returned no match.
  `rg` for condensed cover/conservativity names in `dag/lean_names_upstream.json`
  returned no match. The new full declaration name is absent from the source libraries.

Validation: prescribed `scompile.py NM lem-zl-condensed-cover-restriction-conservative`
compiled the sandbox and final library-path forms separately, each under 60 seconds
(5.5 s and 5.6 s). No errors or warnings were printed. Every variable/universe is bound
explicitly and `autoImplicit` is disabled. All writes are confined to this item's sandbox;
no live source edits, direct git commands, global builds, or other agents were used.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
