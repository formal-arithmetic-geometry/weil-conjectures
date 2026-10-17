/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-!
# The twisted inverse image as a right adjoint of `Rf_!` on `Dctf`

Let `f : X ⟶ Y` be smooth separated of pure relative dimension `d`, `Y` separated of finite type
over a field, and `Λ` a finite coefficient ring whose exponent is invertible on `X` and `Y`.
The exceptional inverse image `Rf^!` is constructed as a right adjoint of `Rf_!` on the
unbounded derived categories (Brown representability), and restricts to the small categories
`Dctf`. This file compares it with the explicit functor `K ↦ Lf^* K(d)[2d]`:

* `Lf^*(-)(d)[2d]` restricts to a functor `Dctf(Y, Λ) ⥤ Dctf(X, Λ)`
  (`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.twistShiftPullback`), right adjoint to the
  restriction of `Rf_!`, the adjunction being transported along the smooth purity isomorphism;
  its counit is the smooth trace (blueprint `det-sp-comparison-brown-explicit`);
* the restriction of the Brown adjoint `Rf^!` is a right adjoint of the restriction of `Rf_!`,
  with the restricted counit, and there is a unique isomorphism `Lf^*(-)(d)[2d] ≅ Rf^!` on
  `Dctf(Y, Λ)` compatible with the counits (blueprint `det-sp-comparison-brown-unique`).

The uniqueness is the categorical fact that right adjoints are unique up to a unique
counit-compatible isomorphism (`CategoryTheory.Adjunction.existsUnique_iso_counit`, blueprint
`det-sp-unique-right-adjoint`).

## Implementation notes

Only finite coefficient rings `Λ` are treated: the blueprint's integral and rational cases
(`Λ = 𝒪_E, E, ℚ̄_ℓ`) are the adjunctions of `det-sp-integral-adjunction-bijection`,
`det-sp-rational-adjunction` and `det-sp-qbar-adjunction`, for which the repository has no
exceptional inverse image on `Dctf`. The transport of an adjunction along an isomorphism of
right adjoints used in the finite case is `CategoryTheory.Adjunction.ofNatIsoRight`, and the
uniqueness statement `CategoryTheory.Adjunction.existsUnique_iso_counit` is general.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  {G J : D ⥤ C}

/-- A family of morphisms `φ_K : G K ⟶ J K` between two right adjoints of `F` compatible with
the counits is the comparison isomorphism `rightAdjointUniq`: each `φ_K` is the transpose of
`ε^G_K` under `F ⊣ J`. -/
theorem eq_rightAdjointUniq_hom_app_of_counit (adj₁ : F ⊣ G) (adj₂ : F ⊣ J) (K : D)
    (φ : G.obj K ⟶ J.obj K) (hφ : F.map φ ≫ adj₂.counit.app K = adj₁.counit.app K) :
    φ = (adj₁.rightAdjointUniq adj₂).hom.app K := by
  apply (adj₂.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit, hφ, rightAdjointUniq_hom_app_counit]

/-- Blueprint `det-sp-unique-right-adjoint`: Right adjoints are unique up to a unique
counit-compatible isomorphism.

Let `F` have two right adjoints `G` and `J`, with counits `ε^G` and `ε^J`. There is a unique
isomorphism `γ : G ≅ J` compatible with the counits, `ε^J_K ∘ F(γ_K) = ε^G_K`; it is
`CategoryTheory.Adjunction.rightAdjointUniq`. It is even the only family of morphisms
compatible with the counits (`CategoryTheory.Adjunction.eq_rightAdjointUniq_hom_app_of_counit`). -/
theorem existsUnique_iso_counit (adj₁ : F ⊣ G) (adj₂ : F ⊣ J) :
    ∃! γ : G ≅ J, ∀ K : D, F.map (γ.hom.app K) ≫ adj₂.counit.app K = adj₁.counit.app K :=
  ⟨adj₁.rightAdjointUniq adj₂, rightAdjointUniq_hom_app_counit adj₁ adj₂, fun _ hγ ↦
    Iso.ext (NatTrans.ext (funext fun K ↦
      eq_rightAdjointUniq_hom_app_of_counit adj₁ adj₂ K _ (hγ K)))⟩

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open Scheme

namespace Etale

open Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
  [HasTateTwist.IsNormalized Λ] {k : Type u} [Field k] {X Y : Scheme.{u}}
  (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
  {d : ℕ} (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
  [QuasiCompact f]

/-- The functor `K ↦ Lf^* K(d)[2d]` of a smooth `f` preserves `Dctf`: `Lf^* K(d)[2d]` is
isomorphic to `Rf^! K` by smooth purity, and `Rf^!` preserves `Dctf`. -/
lemma constructibleFiniteTor_twistShift_leftDerivedUpperStar
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) f aY
  exact (constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).prop_of_iso
    ((smoothPurityNatIso Λ f θ).app K).symm
    (constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hK)

/-- The twisted inverse image `K ↦ Lf^* K(d)[2d]` of a smooth `f`, as a functor
`Dctf(Y, Λ) ⥤ Dctf(X, Λ)`. -/
noncomputable def DerivedCategoryFiniteTor.twistShiftPullback :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  ObjectProperty.lift _
    (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) Y ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ⋙
      twistShift Λ X d)
    fun K ↦ constructibleFiniteTor_twistShift_leftDerivedUpperStar Λ aY f K.property

/-- The restriction of `Rf_!` to `Dctf` is compatible with the inclusions. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedLowerShriekCompatibility :
    DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ⋙ R(f)_![ModuleCat.{u + 1} Λ] ≅
      DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⋙
        DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) Y :=
  (ObjectProperty.liftCompιIso _ _ _).symm

/-- The restriction of `Rf^!` to `Dctf` is compatible with the inclusions. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedUpperShriekCompatibility :
    DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) Y ⋙ R(f)^![ModuleCat.{u + 1} Λ] ≅
      DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f ⋙
        DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X :=
  (ObjectProperty.liftCompιIso _ _ _).symm

/-- The restriction of the Brown adjunction `Rf_! ⊣ Rf^!` to the small categories `Dctf`
(`CategoryTheory.Adjunction.restrictFullyFaithful`). -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction :
    DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
      DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (DerivedCategoryFiniteTor.rightDerivedLowerShriekCompatibility Λ aY f)
    (DerivedCategoryFiniteTor.rightDerivedUpperShriekCompatibility Λ aY f)

/-- The counit of the restricted Brown adjunction is the counit of `Rf_! ⊣ Rf^!`. -/
lemma DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction_counit_app
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y) :
    ((DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction Λ aY f).counit.app K).hom =
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K.obj := by
  have := Adjunction.map_restrictFullyFaithful_counit_app
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (DerivedCategoryFiniteTor.rightDerivedLowerShriekCompatibility Λ aY f)
    (DerivedCategoryFiniteTor.rightDerivedUpperShriekCompatibility Λ aY f) K
  simpa [DerivedCategoryFiniteTor.rightDerivedLowerShriekCompatibility,
    DerivedCategoryFiniteTor.rightDerivedUpperShriekCompatibility] using this

/-- The smooth purity isomorphism `γ_f : Lf^*(-)(d)[2d] ≅ Rf^!`
(`AlgebraicGeometry.Etale.smoothPurityNatIso`, for an orientation `θ : ω_f ≅ Λ_X(d)[2d]`),
restricted to `Dctf(Y, Λ)`. -/
noncomputable def DerivedCategoryFiniteTor.smoothPurityNatIso
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) :
    DerivedCategoryFiniteTor.twistShiftPullback Λ aY f ≅
      DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ ((Etale.smoothPurityNatIso Λ f θ).app K.obj))
    (fun g ↦ by
      ext
      exact (Etale.smoothPurityNatIso Λ f θ).hom.naturality g.hom)

/-- Blueprint `det-sp-comparison-brown-explicit`: The twisted inverse image is right adjoint to
`Rf_!` (finite coefficients).

For `f` smooth separated of pure relative dimension `d` and an orientation
`θ : ω_f ≅ Λ_X(d)[2d]`, the functor `K ↦ Lf^* K(d)[2d]`, `Dctf(Y, Λ) ⥤ Dctf(X, Λ)`, is right
adjoint to `Rf_! = R f̄_* ∘ j_! : Dctf(X, Λ) ⥤ Dctf(Y, Λ)`: the finite adjunction
`Rf_! ⊣ Rf^!` transported along the smooth purity isomorphism `γ_f`. Its counit at `K` is the
smooth trace `Tr^sm_{f,K} = ε_K ∘ Rf_!(γ_{f,K})` of `def-pur-smooth-trace`
(`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.twistShiftPullbackAdjunction_counit_app`).

Only the finite coefficient case is formalised: see the module docstring. -/
noncomputable def DerivedCategoryFiniteTor.twistShiftPullbackAdjunction
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) :
    DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
      DerivedCategoryFiniteTor.twistShiftPullback Λ aY f :=
  (DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction Λ aY f).ofNatIsoRight
    (DerivedCategoryFiniteTor.smoothPurityNatIso Λ aY f θ).symm

/-- Blueprint `det-sp-comparison-brown-explicit`: the counit of the explicit adjunction
`Rf_! ⊣ Lf^*(-)(d)[2d]` at `K` is the smooth trace `Tr^sm_{f,K}`. -/
lemma DerivedCategoryFiniteTor.twistShiftPullbackAdjunction_counit_app
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y) :
    ((DerivedCategoryFiniteTor.twistShiftPullbackAdjunction Λ aY f θ).counit.app K).hom =
      smoothPurityTrace Λ d f ((Etale.smoothPurityNatIso Λ f θ).app K.obj) := by
  have h : (DerivedCategoryFiniteTor.twistShiftPullbackAdjunction Λ aY f θ).counit.app K =
      ((DerivedCategoryFiniteTor.twistShiftPullbackAdjunction Λ aY f θ).homEquiv _ _).symm
        (𝟙 _) := by
    simp [Adjunction.homEquiv_counit]
  rw [h, DerivedCategoryFiniteTor.twistShiftPullbackAdjunction,
    Adjunction.homEquiv_ofNatIsoRight_symm_apply, Adjunction.homEquiv_counit,
    ObjectProperty.FullSubcategory.comp_hom,
    DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction_counit_app, smoothPurityTrace]
  simp [DerivedCategoryFiniteTor.smoothPurityNatIso,
    DerivedCategoryFiniteTor.rightDerivedLowerShriek]

/-- Blueprint `det-sp-comparison-brown-explicit`: The twisted inverse image is right adjoint to
`Rf_!` for every finite coefficient ring.

For `f` smooth separated of pure relative dimension `d` over a separated finite-type
`k`-scheme `Y` and a finite `Λ` whose exponent is invertible on `X` and `Y`, the functor
`K ↦ Lf^* K(d)[2d]` on `Dctf` is right adjoint to `Rf_!`, by an adjunction whose counit at
every `K` is the smooth trace `Tr^sm_{f,K}` of the purity isomorphism. -/
theorem DerivedCategoryFiniteTor.exists_twistShiftPullbackAdjunction :
    ∃ (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
        (twistShift Λ X d).obj (constantComplex Λ X))
      (adj : DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
        DerivedCategoryFiniteTor.twistShiftPullback Λ aY f),
      ∀ K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y, (adj.counit.app K).hom =
        smoothPurityTrace Λ d f ((Etale.smoothPurityNatIso Λ f θ).app K.obj) := by
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) f aY
  exact ⟨θ, _, DerivedCategoryFiniteTor.twistShiftPullbackAdjunction_counit_app Λ aY f θ⟩

/-- Blueprint `det-sp-comparison-brown-unique`: Identification of the explicit adjoint with the
restricted Brown adjoint (finite coefficients).

The restriction of the Brown adjoint `Rf^!` to `Dctf` is a right adjoint of the restriction of
`Rf_!` (`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction`),
whose counit is the restricted counit
(`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction_counit_app`),
and for every adjunction `adj : Rf_! ⊣ Lf^*(-)(d)[2d]` on `Dctf`, for instance the explicit one
of `det-sp-comparison-brown-explicit`, there is a unique isomorphism
`Lf^*(-)(d)[2d] ≅ Rf^!` of functors on `Dctf(Y, Λ)` compatible with the counits. -/
theorem DerivedCategoryFiniteTor.existsUnique_twistShiftPullbackIso_counit
    (adj : DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
      DerivedCategoryFiniteTor.twistShiftPullback Λ aY f) :
    ∃! γ : DerivedCategoryFiniteTor.twistShiftPullback Λ aY f ≅
        DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f,
      ∀ K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y,
        (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f).map (γ.hom.app K) ≫
          (DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction Λ aY f).counit.app K =
        adj.counit.app K :=
  Adjunction.existsUnique_iso_counit adj
    (DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction Λ aY f)

end Etale

end AlgebraicGeometry
