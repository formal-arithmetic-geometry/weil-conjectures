## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleCoverCechStageComparison` states
`AlgebraicGeometry.finite_etale_cover_cech_stage_comparison`, with one `sorry` proof.
The statement, proof plan, and dependency lists of the DAG item are unchanged.
Four helper abbreviations expose the actual site fibre products and their second
projections; they construct data directly using Mathlib's `pullback`, `pullback.fst`,
and `pullback.snd`. There are no added notions, dependency repairs, axioms, or
postponed helper theorems.

Hypotheses and objects, clause by clause:

- “X affine” is `{X : Scheme.{u}} [IsAffine X]`.
- The finite discrete coefficient ring is `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]`.
  The fixed-ring module category uses only this algebraic data: the topology of the
  coefficient ring is its discrete topology, and no topological coefficient category
  is substituted. `Ring`, rather than `CommRing`, retains noncommutative rings.
- The étale left-module sheaf is
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  `ModuleCat` is the category of left modules. The recorded comparison dependency
  explicitly supplies this fixed-ring encoding and its adjunction for finite rings.
- `M = ν_X^*F` is written directly as
  `(ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F`.
  There is no arbitrary pro-étale coefficient object or arbitrary map into one.
  The `finiteCoefficientRealization` of the recorded pro-étale module dependency
  identifies this encoding with modules over its specified coefficient ring sheaf.
  Only the underlying abelian presheaf is used, exactly as cover-cech prescribes.
- The small nonempty directed set is `{L : Type u} [Preorder L]
  [IsDirected L (· ≤ ·)] [Nonempty L]`. It has the same universe as the schemes;
  no independent smaller index universe is imposed.
- The inverse system over X is `D : Lᵒᵖ ⥤ X.Etale`, with
  `[∀ i, IsAffine (D.obj i).left]`. Membership in `X.Etale` supplies étaleness;
  since X and the stages are affine, the structure maps are affine, hence
  quasi-compact and separated. Together with étale local finite presentation this
  is exactly finite presentation. The transition maps are affine because both
  their source and target are affine. These consequences are not additional
  hypotheses.
- The limit over X is `U : X.ProEt`, the cone `π`, and `_hlim : IsLimit ...`
  after forgetting to schemes. This states the scheme limit, not merely a limit
  internal to the pro-étale site. Its membership in that site is the object
  encoding for the stated limit, whose affine ind-étale presentation implies
  weak étaleness; no affineness, ind-étaleness, or continuity is assumed separately.
- The chosen stage is `i₀ : L`. The finite affine covering is
  `W : Fin m → X.Etale`, `[∀ a, IsAffine (W a).left]`, and arrows
  `f : ∀ a, W a ⟶ D.obj (op i₀)`, with `_hcover` the covering sieve.
  Morphisms of `X.Etale` are étale on underlying schemes by étale cancellation.
  Thus this is the same affine étale covering over the initial stage. Conversely
  the node's cover gives these objects by composition with the stage map to X.
- The later covering objects and arrows are exactly
  `finiteEtaleCoverStageObject D i₀ W f i` and
  `finiteEtaleCoverStageArrow D i₀ W f i`: pullback of `f a` along the map
  from stage `i.val` to `i₀`, for `i : {i : L // i₀ ≤ i}`.
- The limit covering objects and arrows are exactly
  `finiteEtaleCoverLimitObject D i₀ W f U π` and
  `finiteEtaleCoverLimitArrow D i₀ W f U π`: pullback of the included initial
  arrows along `π.app (op i₀)` in `X.ProEt`. The forgetful site functors preserve
  these finite limits, so these are the scheme fibre products of the node,
  with their canonical projection-compatible identifications.
- `S i` and `T` are `SiteCechComplex` choices for these families. Their fields
  contain the full tuple-product universal properties and face projections.
  They are the product choices already required by the recorded cover-cech
  interface, not hypotheses of acyclicity, injectivity, or section continuity.

Conclusions and canonical maps, clause by clause:

- The quantified tuple `t : Fin (p + 1) → Fin m` is ordered and allows repetitions.
  `(S i).complex (F.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat)` is precisely
  the recorded nonnegative Čech complex on underlying abelian groups. Likewise
  `T.complex` uses the underlying presheaf of the actual comparison inverse image.
  These reuse the recorded `SiteCechComplex.complex`, not a replacement complex.
- `r h p t` is a map from the later tuple product to the earlier one. The first
  conjunction fixes its composites both to every original covering factor and
  to the earlier base stage. Fibre-product uniqueness forces the actual canonical
  transition. `s i p t` is similarly fixed by its composites to every original
  factor and by the cone projection to the stage. There is no assumption that
  arbitrary choices of maps are isomorphisms: the theorem asserts existence of
  these uniquely characterized maps.
- `A`, `eA`, `K`, and `eK` exhibit a diagram with precisely the stage complexes
  and a cocone with precisely the limit complex. The following coordinate equation
  fixes each diagram map as restriction along `r`. The next coordinate equation
  fixes each cocone leg as the actual component of
  `(ProEtale.comparisonAdjunction ... X).unit.app F`, followed by restriction
  along `s`. Both equations quantify over all cochains and tuple coordinates.
  Thus the asserted comparison is the node's section-restriction comparison;
  unnormalized existential isomorphisms would not suffice.
- `Nonempty (IsColimit K)` says that this specified cocone is colimiting in
  nonnegative complexes. Transport through `eK` gives the claimed canonical
  complex isomorphism from the filtered colimit of stages.
- `IsColimit` for the image of K under
  `ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat` records the same
  comparison for integer complexes with negative terms zero. This is exactly
  `SiteCechComplex.integerComplexFunctor`, used in `coverComplex` of the dependency.
- For every `q : ℕ`, `IsColimit` of K under
  `HomologicalComplex.homologyFunctor ... (ComplexShape.up ℕ) q` gives the
  canonical isomorphism from the filtered colimit of stage Čech cohomology to
  the limit Čech cohomology. The induced legs are the homology maps of the same
  restriction cochain maps. The dependency's `cohomologyFunctor q` is this composite.
- There is no injectivity, vanishing, augmentation exactness, or positivity
  assumption. Degree zero is explicitly included. The use of colimit universal
  properties avoids presupposing a chosen colimit object or a chosen inverse.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, using the existing `Scheme.toProEt`,
  `ProEtale.comparisonUpperStar`, and `ProEtale.comparisonAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `ProEtale.FiniteCoefficientModules`, `finiteCoefficientRealization`, and
  `finiteCoefficientComparison`, which supply the equivalence with the fixed-ring
  encoding used here. No coefficient ring sheaf is redefined.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`: `RingHom.IndEtaleAcrossUniverses`,
  publicly importing the existing `Algebra.IndEtale` and affine inverse-limit
  characterization `proAffineEtale_Spec_iff`. Here the presentation is given as
  a scheme diagram; no second ind-étale predicate is introduced.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`,
  `Scheme.Etale`, and the covering criterion `ofArrows_mem_smallEtaleTopology_iff`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, and `pullback.snd`.
- `Sheaf.AlgebraicGeometry.CoverCech`: its recorded underlying-presheaf convention
  and its public dependency `WeilConjectures.CategoryTheory.SiteCechComplex`:
  `SiteCechComplex`, `complex`, `cochains`, `integerComplexFunctor`, and
  `cohomologyFunctor`. `Scheme.etaleCoverCechComplex` only specializes one
  commutative-ring encoding; using its underlying generic construction retains
  the full finite-ring statement, including noncommutative coefficients.

The stated proof dependencies are imported. Their planned uses are detailed in
all seven steps of the theorem docstring. In particular the module-valued section
formula is recorded with `CommRing`; for general `Ring`, its recorded set-valued
formula, or the upstream coefficient-independent affine comparison formula, gives
bijectivity of the same unit-and-restriction map, which is already additive.
Consequently the statement does not restrict coefficients to a commutative ring.

Edge cases checked against the source and the chosen interfaces:

- `m = 0` is allowed. Covering then forces the initial base to be empty, but no
  nonemptiness is imposed on bases or on covers. Tuple-index sets are empty in
  every degree, so both complexes are zero.
- `m = 1`, repeated tuple indices, identity transitions, singleton index sets,
  and directed preorders that are not partial orders are all retained.
- The zero ring, zero coefficient sheaf, and empty affine scheme are allowed.
- `q = 0` uses zero incoming differential and unaugmented cohomology. Negative
  complex terms are zero via the same recorded extension functor.
- No finite type bound, injective hypothesis, cohomological vanishing hypothesis,
  or equality of site object and morphism universes is introduced.

Searches (2026-10-21), before writing:

- `msearch.py leanfinder`: “The Cech complex of a finite affine etale cover over
  an affine inverse limit is the filtered colimit of its stage Cech complexes
  after pro etale inverse image”. Eight results concerned affine-transition-limit
  approximation and maps (`ExistsHomHomCompEqCompAux` and related facts); no exact match.
- `msearch.py loogle`: `"SiteCechComplex", "comparisonUpperStar"`: zero hits.
- `msearch.py grep`: `cech.*colimit|Cech.*Colimit`, in Mathlib
  `AlgebraicGeometry/Sites`: zero hits.
- `msearch.py leansearch`: “Finite etale Cech complexes over affine inverse limits
  and pro etale inverse image are filtered colimits”. Eight hits on general
  homological-complex colimits and finite-limit/filtered-colimit commutation;
  none states this geometric comparison with its specified legs.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for Čech colimit and
  stage-comparison names found `FiniteEtaleCechFilteredColimit`,
  `EtaleLimitFiniteCechComplexColimit`, `ColimitSiteCechColimit`, and other
  general/different-site results. Their statements were inspected: the first
  varies coefficients on a fixed cover; the second varies scheme étale sites;
  the third concerns a specified colimit site. None states this comparison from
  an étale sheaf to its pro-étale inverse image over a fixed scheme.
- Literal node-id search in `lean/WeilConjectures` gave no match. Searches for
  the five new declaration names in the upstream name index, Mathlib, and
  both source trees gave no clash.

No statement dispute or source correction was needed. The example `CompactObject`
module is withdrawn in the supplied tree; its node now records the upstream
`WeilConjectures.CategoryTheory.CompactObject` declaration. The new module follows
the live project's `module`, `public import`, source-docstring, and public-section style.

Validation: `scompile.py` checked the module against the published live build in
both sandbox and library namespaces. The first check found one 101-character line;
it was wrapped, and the next check was clean in both namespaces (3.7 s / 4.1 s).
The final required dry-run and delivery checks are run after preparing this report.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
