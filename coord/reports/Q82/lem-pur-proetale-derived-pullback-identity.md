## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity` states
`AlgebraicGeometry.Scheme.proEtaleDerivedPullback_identity`. Its only theorem has
proof `sorry`; its docstring gives all seven steps of the node's natural-language
proof. Four helpers have actual data and belong to this identity normalization:
the existing inverse-image functor followed by scalar restriction, the distinguished
module coprojection, the ordinary tensor's sheafification-unit pure tensor, and the
existing localization Q with explicitly instantiated coefficient universes.
There are no new independent notions, dependency repairs, or statement corrections.

Hypotheses and clauses, in statement order:

- A scheme X is `(X : Scheme.{u})`; a finite commutative ring A is
  `(A : Type u) [CommRing A] [Finite A]`. There is no nontriviality, point,
  separatedness, boundedness, or constructibility hypothesis. The site's objects
  remain in universe `u+1` and its morphisms in universe `u`.
- The small site is precisely `X.ProEt` with `ProEt.topology X`. The constant ring is
  the published `proEtaleConstantRing X A`, namely `constantSheaf` of
  `CommRingCat.of (ULift A)`, with the prescribed coefficient lift. The module category
  is `proEtaleRingModules X (proEtaleConstantRing X A)`, transparently the recorded
  `ringedSiteModules`/Mathlib `SheafOfModules` after forgetting commutativity.
- The inverse image is the published `proEtaleSheafInverseImage (𝟙 X)`.
  The first witness `e` is a natural isomorphism from this functor to the identity
  on commutative-ring sheaves. Its first conjunct fixes each section map to
  `proEtaleIsoInverseImageIdentification (𝟙 X) CommRingCat`, followed by restriction
  along the inverse component of `MorphismProperty.Over.mapId`. This is exactly
  the recorded comma-coprojection-normalized objectwise comparison, with the
  harmless postcomposition-by-identity structure-map identification made explicit.
- The equality `e.hom.app (proEtaleConstantRing X A) =
  proEtaleCoefficientInverseImageMap (𝟙 X) A` is equality of commutative-ring-sheaf
  morphisms. Forgetting commutativity gives exactly the node's ring-sheaf equality;
  it concerns the specified coefficient map, not a replacement isomorphism.
- For every module, `eM : proEtaleIdentityTransportedInverseImage X A ≅ 𝟭 _`
  is a natural isomorphism in the category of module sheaves, so both its maps are
  linear and commute with restrictions. The helper's source functor is the
  existing `proEtaleModuleInverseImage` followed by `restrictScalars` along the
  inverse of the specified coefficient comparison. Thus its source action is
  exactly `a • m = c⁻¹(a) • m` on the original inverse-image abelian groups.
  The section formula for `eM.inv` fixes it to the actual model-site module
  adjunction unit, evaluated at U, then restricted along
  `(MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U`.
  This is the distinguished `(U, delta_U)` coprojection, so `eM` is the module lift
  of the objectwise identity comparison, rather than an arbitrary module isomorphism.
- `alpha : proEtaleConstantRingPullback A (𝟙 X) ≅ 𝟭 _` is the required natural
  isomorphism on the actual tensor module pullback. The next two conjuncts say
  `alpha(m ⊗ a) = a • eM(m)` and `alpha⁻¹(z) = eM⁻¹(z) ⊗ 1`, with the tensors
  interpreted by the actual presheaf-module sheafification unit in
  `proEtaleIdentityPullbackTmul`. The upstream ordinary tensor writes its scalar
  factor first, so the Lean generator is `a ⊗ m`. These formulas are precisely the
  canonical scalar-transport identification: its forward map is
  `m ⊗ a ↦ c⁻¹(a)m`, followed by `eM`. They assert no false sectionwise
  surjectivity of the sheafification unit and quantify over all modules and sections.
- `b` is a natural isomorphism from the termwise ordinary pullback on all
  `CochainComplex ... ℤ` to the identity. For every complex K and every integer j,
  `(b.hom.app K).f j = alpha.hom.app (K.X j)`. Thus its maps are exactly the
  specified termwise identity maps after scalar transport, including at every
  differential and naturally for every cochain map.
- `gamma : proEtaleConstantRingDerivedPullback A (𝟙 X) ≅
  𝟭 (proEtaleDerivedCategory X A)` is the required ordinary unbounded derived
  natural isomorphism. For every cochain representative K, its component at QK
  equals `proEtaleRingDerivedPullbackFactors.hom.app K ≫ Q.map (b.hom.app K)`.
  The helper `proEtaleIdentityLocalization` is literally Mathlib Q, with existing
  abelian-sheafification infrastructure instantiated in universe `u+1`.
  This final equation includes arbitrary representatives, not just resolutions
  or complexes in a bounded or constructible subcategory.
- The zero ring and the empty scheme are included by the binders. For the zero
  ring, unitary modules are zero and all formulas specialize to their unique maps.
  For the empty scheme, the empty-cover sheaf condition makes abelian sheaves zero;
  no step or binder needs an inhabited scheme or a nonempty covering. The case
  where both degeneracies occur is also included. The integer degree has no lower
  or upper bound, and degree zero is treated by the same representative formula.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- The recorded `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction` reexports
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`,
  `proEtaleModelRingUnit`, `proEtaleModuleToModel`, `proEtaleModuleInverseImage`,
  `proEtaleConstantRing`, `proEtaleCoefficientInverseImageMap`. Its finite-module
  adjunction was read; this statement uses the reexported intrinsic commutative-ring
  module construction to agree exactly with the recorded ordinary derived operations.
- The recorded `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
  publicly reexports `Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage`:
  `proEtaleIsoInverseImageIdentification`, whose full coprojection normalization
  supplies the first conjunct. No higher coefficient universe is needed here.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, which is precisely
  `SheafOfModules`. `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `proEtaleConstantRingComparison`, `proEtaleConstantRingPullback`,
  `proEtaleConstantRingDerivedPullback`. Its public `ProEtaleOperations` supplies
  `proEtaleRingModules` and `proEtaleRingDerivedPullbackFactors`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`:
  `SheafOfModules.pullbackPushforwardAdjunction`; the actual unit fixes the raw
  module coprojection. `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`:
  `changeOfRingsPresheaf`, the ordinary scalar extension used by the pullback.
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafificationAdjunction`, fixing the actual tensor generators.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`:
  `exists_scalarExtensionRingIso` is the proof input for the tensor normalization;
  its public tensor infrastructure supplies the named identity local-bijectivity
  proofs used by the helper. The ordinary and mixed-universe tensor objects are
  not silently identified: the helper uses the ordinary change-of-rings construction.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `ExactFunctor`:
  `DerivedCategory`, `DerivedCategory.Q`, `Functor.mapDerivedCategoryFactors`.
  `Mathlib.CategoryTheory.Sites.Sheafification` and `Sites.Pullback` supply the
  sheafification and continuous inverse-image adjunctions used in the proof plan.
  `Mathlib.CategoryTheory.Localization.Predicate`: `Localization.liftNatIso` and
  `natTrans_ext` are the proof inputs for normalized descent.
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`:
  `MorphismProperty.Over.pullbackId`; Mathlib's same-named source topic supplies
  `MorphismProperty.Over.mapId`. The inverse projection is the canonical identity
  fibre-product comparison, not an arbitrary site map.
- The isomorphism dependency reexports `Sheaf.Paper.CompletedIntegralCoefficients`.
  Its `WeilConjectures.integralCoefficientAbSheafify` and
  `integralCoefficientAbLocallyBijective` are explicitly instantiated at `.{u,u}`
  inside the tensor and Q helpers. Their general output size is `max r (t+1)`;
  leaving r implicit produced stuck maximum-universe constraints during inference.
  Specializing these existing proofs fixes inference without changing the site,
  coefficient, module, or derived category and without any new universe equality.

Searches for an existing statement:

- `msearch.py leanfinder`, query "Canonical derived identity pullback on pro-etale
  ring sheaf modules normalized termwise on cochain representatives": eight hits,
  chiefly ordinary module pullback/unit/free-object results and scheme-module
  pseudofunctor identities; none gives the prescribed pro-etale coefficient equality
  and the normalized unbounded representative equation.
- `msearch.py loogle`, query `SheafOfModules.pullbackId`: four hits. Read the full
  signature and docstring in Mathlib's `Sheaf/PullbackContinuous.lean`. It is for
  the literal identity site functor and identity ring map, not the specified
  pro-etale base-change functor with its constructed inverse image and coefficient map.
- `msearch.py grep`, query `pullbackId|mapDerivedCategoryId`: 25 hits, ordinary
  site/module/pullback identities. None states this node's combination of comparisons.
- `rg` in the upstream `WeilConjectures` and project `lean/Sheaf` trees, queries
  `proEtaleIdentity`, pro-etale pullback identity name patterns, and the exact item id:
  no matching statement or preexisting helper name. Also checked
  `dag/lean_names_upstream.json`. The upstream finite-coefficient identity and the
  existing intrinsic realization identity `sfIntrinsicPullbackId` were read; they
  do not give this node's equality to its canonical coefficient map and raw-module
  coprojection with termwise derived normalization.

The source `literature/stacks-project/proetale.tex`, `section-morphism` (Tag 09A5),
and the current `main-20261015` blueprint's diagonal-base-change proof, final sentence,
were read. The assertion is the identity specialization extracted in the node's
seven proof steps, rather than a different theorem claimed to be verbatim Stacks.
There is no `STATEMENT-DISPUTED` issue.

Validation: the complete delivered module passed `scompile.py` cleanly, both as
sandbox source and under its actual module path (6.4 s and 8.7 s respectively).
Only file compilation was used; every universe and variable is bound explicitly.

## Second reading by Q82

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
