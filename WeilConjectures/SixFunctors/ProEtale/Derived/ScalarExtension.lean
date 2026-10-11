/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionComparison
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-!
# Extension of scalars and the projection map of `Rg_*` on the pro-étale site

Let `S` be a finite free algebra over a Noetherian ring `R`, for instance the ring of integers
`𝒪_{E'}` of a finite extension `E'/E` of `ℓ`-adic fields over `𝒪_E`. Extension of scalars
`N = S ⊗_R - : D(X_proét, R) ⥤ D(X_proét, S)` commutes with the derived pullbacks `Lg^*`, with the
derived tensor products and with the derived direct images `Rg_*`, and it carries the projection
map `Rg_* M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^* L)` over `R` to the one over `S`.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app`:
  the base change map `N (Rg_* M) ⟶ Rg_* (N M)` is invertible. Restriction of scalars `U` is
  conservative, and `U N M` is the sum of copies of `M` indexed by a basis of `S`, on which `U` of
  the base change map is the iterated mate of the commutation of `N` with `Lg^*`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_extendScalars`:
  the transport of the projection formula for `Rg_*` along extension of scalars.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] [HasDerivedCategory C]
  [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.ReflectsIsomorphisms]

/-- An exact functor reflecting isomorphisms induces a functor on derived categories reflecting
isomorphisms: a morphism is an isomorphism iff it is one on all homology objects, and
`F.mapDerivedCategory` commutes with homology. -/
instance reflectsIsomorphisms_mapDerivedCategory : F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects f _ := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ F

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u})

/-- Restriction of scalars of pro-étale sheaves preserves finite colimits: it is the sheafified
postcomposition with restriction of scalars, which is left adjoint to coextension of scalars. -/
instance preservesFiniteColimits_sheafComposeRestrictScalars :
    PreservesFiniteColimits (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)) := by
  have hadj := ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
    hadj.rightAdjoint_preservesLimits
  have : (Scheme.ProEt.topology X).HasSheafCompose
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction (Scheme.ProEt.topology X) hadj).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

/-- Restriction of scalars of pro-étale sheaves reflects isomorphisms, isomorphisms of sheaves
being detected on sections. -/
instance reflectsIsomorphisms_sheafComposeRestrictScalars :
    (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)).ReflectsIsomorphisms where
  reflects {F G} f hf := by
    have : IsIso ((sheafToPresheaf _ _).map ((sheafCompose (Scheme.ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} φ)).map f)) := inferInstance
    have : IsIso f.hom := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro U
      have : IsIso ((ModuleCat.restrictScalars.{u + 1} φ).map (f.hom.app U)) :=
        NatIso.isIso_app_of_isIso
          ((sheafToPresheaf _ _).map ((sheafCompose (Scheme.ProEt.topology X)
            (ModuleCat.restrictScalars.{u + 1} φ)).map f)) U
      have : IsIso ((forget (ModuleCat R)).map
          ((ModuleCat.restrictScalars.{u + 1} φ).map (f.hom.app U))) := inferInstance
      have : IsIso ((forget (ModuleCat S)).map (f.hom.app U)) := this
      exact isIso_of_reflects_iso _ (forget (ModuleCat S))
    have : IsIso ((sheafToPresheaf _ _).map f) := this
    exact isIso_of_reflects_iso f (sheafToPresheaf _ _)

section Linear

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type*) [Ring Λ] [Linear Λ A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pushforward `g_*` on pro-étale sheaves with values in a `Λ`-linear category is
`Λ`-linear: it acts on morphisms by whiskering. -/
instance linear_lowerStar : (g)_*[A].Linear Λ where

/-- The pullback `g^*` on pro-étale sheaves with values in a `Λ`-linear category is `Λ`-linear,
being left adjoint to the `Λ`-linear pushforward. -/
instance linear_upperStar : (g)^*[A].Linear Λ :=
  (upperStarLowerStarAdjunction A g).left_adjoint_linear

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived pullback `Lg^*` on pro-étale sheaves is `Λ`-linear: it is isomorphic to the
functor `D(g^*)` induced by the `Λ`-linear exact functor `g^*`. -/
instance linear_leftDerivedUpperStar : (L((g)^*[A])).Linear Λ :=
  Functor.linear_of_iso Λ ((g)^*[A]).leftDerivedFunctorIsoMapDerivedCategory.symm

/-- The derived pushforward `Rg_*` on pro-étale sheaves is `Λ`-linear, being right adjoint to the
`Λ`-linear `Lg^*`. -/
instance linear_rightDerivedLowerStar : (R((g)_*[A])).Linear Λ :=
  (derivedUpperStarLowerStarAdjunction A g).right_adjoint_linear

end Linear

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]
  (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] [ProEtale.UpperStarPreservesFlat B]
  {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  (E_Y : Sheaf (Scheme.ProEt.topology Y) A ⥤ Sheaf (Scheme.ProEt.topology Y) B) [E_Y.Additive]
  [PreservesFiniteLimits E_Y] [PreservesFiniteColimits E_Y] [E_Y.PreservesFlat]
  [E_Y.IsLeftAdjoint] [E_Y.Monoidal]
  (E_Z : Sheaf (Scheme.ProEt.topology Z) A ⥤ Sheaf (Scheme.ProEt.topology Z) B) [E_Z.Additive]
  [PreservesFiniteLimits E_Z] [PreservesFiniteColimits E_Z] [E_Z.PreservesFlat]
  [E_Z.IsLeftAdjoint] [E_Z.Monoidal]
  (τ : E_Y ⋙ (g)^*[B] ≅ (g)^*[A] ⋙ E_Z) [NatTrans.IsMonoidal τ.hom]

/-- For exact monoidal functors `E` between pro-étale sheaves with coefficients in `A` and in `B`
commuting monoidally with the pullbacks `g^*`, the tensor comparisons of `Lg^*` and of `LE` are
compatible with the derived commutation isomorphism `LE ⋙ Lg^* ≅ Lg^* ⋙ LE`. -/
lemma comparisonCompatible_leftDerivedFunctorCompNatIso :
    Adjunction.ComparisonCompatible
      (Functor.leftDerivedFunctorCompNatIso (ProEtale.upperStar A g) E_Z E_Y
        (ProEtale.upperStar B g) τ)
      (leftDerivedUpperStarTensorComparison _ g) (leftDerivedUpperStarTensorComparison _ g)
      (asIso E_Z.leftDerivedTensorComparison) (asIso E_Y.leftDerivedTensorComparison) := by
  intro a b
  rw [leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison,
    leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison,
    asIso_hom, asIso_hom,
    Functor.map_leftDerivedTensorComparison_comp_eq_of_iso _ _ _ _ τ, tensorHom_def]
  rfl

end General

section ScalarExtension

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- Restriction of scalars preserves pro-étale sheaves, being a right adjoint. -/
instance hasSheafCompose_restrictScalars (φ : R →+* S) :
    (Scheme.ProEt.topology X).HasSheafCompose (ModuleCat.restrictScalars.{u + 1} φ) :=
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.restrictScalars.{u + 1} φ) :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).rightAdjoint_preservesLimits
  hasSheafCompose_of_preservesLimitsOfSize _

/-- Restriction of scalars of pro-étale sheaves preserves limits, being a right adjoint. -/
instance preservesLimits_sheafComposeRestrictScalars (φ : R →+* S) :
    PreservesLimits (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)) :=
  (sheafExtendScalarsAdjunction φ X).rightAdjoint_preservesLimits

/-- Extension of scalars along a flat algebra is exact on pro-étale sheaves. -/
instance preservesFiniteLimits_sheafExtendScalars_algebraMap [Module.Flat R S] :
    PreservesFiniteLimits (sheafExtendScalars (algebraMap R S) X) :=
  preservesFiniteLimits_sheafExtendScalars X (RingHom.flat_algebraMap_iff.2 inferInstance)

variable [Module.Flat R S]

/-- The adjunction `L(S ⊗_R -) ⊣ D(res)` on the derived categories of pro-étale sheaves induced
by extension and restriction of scalars, both of which are exact. -/
noncomputable def derivedSheafExtendScalarsAdjunction :
    L(sheafExtendScalars (algebraMap R S) X) ⊣
      D(sheafCompose (Scheme.ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))) :=
  (sheafExtendScalarsAdjunction (algebraMap R S) X).mapDerivedCategoryAdjunction.ofNatIsoLeft
    (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorIsoMapDerivedCategory.symm

variable {X}

/-- For a basis `b` of the finite free `R`-algebra `S` and `M` in `D(X_proét, R)`, the maps
`M ⟶ U N M` obtained from the unit of `N = L(S ⊗_R -) ⊣ U = D(res)` by multiplication with the
`b i` exhibit `U N M` as a sum of copies of `M`. -/
theorem isIso_biproductDesc_derivedSheafExtendScalarsAdjunction_unit {ι : Type} [Finite ι]
    (b : Module.Basis ι R S)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) :
    IsIso (biproduct.desc fun i ↦ (derivedSheafExtendScalarsAdjunction X).unit.app M ≫
      D(sheafCompose (Scheme.ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map ((b i : S) • 𝟙 _)) := by
  sorry

variable [Module.Finite R S] [Module.Free R S]
  [Nontrivial R] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The isomorphism `L(S ⊗_R -) ⋙ Lg^* ≅ Lg^* ⋙ L(S ⊗_R -)` of derived functors
`D(Y_proét, R) ⥤ D(Z_proét, S)`, obtained by deriving the isomorphism
`g^* (S ⊗_R F) ≅ S ⊗_R g^* F` of `AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso`. -/
noncomputable abbrev leftDerivedSheafExtendScalarsCompUpperStarIso :
    L(sheafExtendScalars (algebraMap R S) Y) ⋙ L((g)^*[ModuleCat.{u + 1} S]) ≅
      L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) Z) :=
  Functor.leftDerivedFunctorCompNatIso (ProEtale.upperStar _ g)
    (sheafExtendScalars (algebraMap R S) Z) (sheafExtendScalars (algebraMap R S) Y)
    (ProEtale.upperStar _ g) (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g)

/-- **Extension of scalars commutes with `Rg_*`.** For a finite free algebra `S` over a
Noetherian ring `R`, the base change map `L(S ⊗_R -) (Rg_* M) ⟶ Rg_* (L(S ⊗_R -) M)`, the mate of
`AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsCompUpperStarIso`, is an isomorphism.

Restriction of scalars `U` is conservative, and for a basis `b` of `S` the maps `M ⟶ U N M`
given by the unit and the multiplications by the `b i` exhibit `U N M` as a sum of copies of
`M`; the base change map commutes with these multiplications, both sides being `S`-linear, so
`CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_biproductDesc` applies. -/
theorem isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))) :
    IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedSheafExtendScalarsCompUpperStarIso (R := R) (S := S) g).hom).app M) := by
  let b := Module.finBasis R S
  have := isIso_biproductDesc_derivedSheafExtendScalarsAdjunction_unit b M
  have := isIso_biproductDesc_derivedSheafExtendScalarsAdjunction_unit b
    ((R((g)_*[ModuleCat.{u + 1} R])).obj M)
  refine Adjunction.isIso_mateEquiv_app_of_isIso_biproductDesc _ _ _
    (derivedSheafExtendScalarsAdjunction (R := R) (S := S) Y)
    (derivedSheafExtendScalarsAdjunction (R := R) (S := S) Z) M
    (fun i ↦ (b i : S) • 𝟙 _) (fun i ↦ (b i : S) • 𝟙 _) fun i ↦ ?_
  rw [Linear.smul_comp, Category.id_comp, Functor.map_smul, CategoryTheory.Functor.map_id,
    Linear.comp_smul]
  simp

variable [IsNoetherianRing R] [IsNoetherianRing S]

/-- The tensor comparisons of `Lg^*` over `R` and over `S` and those of `L(S ⊗_R -)` are
compatible with `AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsCompUpperStarIso`. -/
lemma comparisonCompatible_leftDerivedSheafExtendScalarsCompUpperStarIso :
    Adjunction.ComparisonCompatible
      (leftDerivedSheafExtendScalarsCompUpperStarIso (R := R) (S := S) g)
      (leftDerivedUpperStarTensorComparison _ g) (leftDerivedUpperStarTensorComparison _ g)
      (asIso (sheafExtendScalars (algebraMap R S) Z).leftDerivedTensorComparison)
      (asIso (sheafExtendScalars (algebraMap R S) Y).leftDerivedTensorComparison) :=
  comparisonCompatible_leftDerivedFunctorCompNatIso _ _ g _ _
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g)

/-- **Extension of scalars carries the projection map of `Rg_*` over `R` to the one over `S`.**
Let `S` be a finite free algebra over a Noetherian ring `R`, both Noetherian, and let
`N = L(S ⊗_R -)`. If the projection map `Rg_* M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^* L)` of pro-étale complexes
of `R`-modules is an isomorphism, so is the projection map over `S` at `(N M, N L)`. -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_extendScalars
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R)))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)))
    [IsIso (((rightDerivedLowerStarProjectionMap _ g).app M).app L)] :
    IsIso (((rightDerivedLowerStarProjectionMap _ g).app
      ((L(sheafExtendScalars (algebraMap R S) Z)).obj M)).app
        ((L(sheafExtendScalars (algebraMap R S) Y)).obj L)) :=
  have : IsIso ((((derivedUpperStarLowerStarAdjunction _ g).rightAdjointProjectionMap
      (leftDerivedUpperStarTensorComparison _ g)).app M).app L) :=
    inferInstanceAs (IsIso (((rightDerivedLowerStarProjectionMap _ g).app M).app L))
  have := isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app (S := S) g M
  have := isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app (S := S) g
    ((derivedTensor _ Z).obj M |>.obj ((L((g)^*[ModuleCat.{u + 1} R])).obj L))
  Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv
    (derivedUpperStarLowerStarAdjunction _ g) (derivedUpperStarLowerStarAdjunction _ g)
    (comparisonCompatible_leftDerivedSheafExtendScalarsCompUpperStarIso g) M L

end ScalarExtension

end AlgebraicGeometry.ProEtale
