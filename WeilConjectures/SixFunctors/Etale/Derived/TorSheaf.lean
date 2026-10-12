/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Tor sheaves of constructible sheaves

For a finite ring `Λ` and constructible sheaves `F` and `G` of `Λ`-modules on `X_ét`, the
homology sheaves `Hʳ(F ⊗ᴸ G)` of the derived tensor product of `F[0]` and `G[0]` are
constructible (blueprint `lem-sf-tor-sheaf-constructible`).

## Strategy

* The pullback along any morphism commutes with `Hʳ(- ⊗ᴸ -)` of sheaves placed in degree `0`
  (`AlgebraicGeometry.Etale.upperStarHomologyDerivedTensorSingleFunctorIso`), so on a common
  stratification trivialising `F` and `G` it suffices to treat finite locally constant sheaves.
* For finite locally constant `F` and `G`, finite local constancy of `Hʳ(F ⊗ᴸ G)` is étale
  local, and étale locally `F` is the constant sheaf at a finite module `M`. A presentation
  `0 ⟶ M₁ ⟶ Λⁿ ⟶ M ⟶ 0` gives a short exact sequence of constant sheaves whose middle term
  is flat, so `Hʳ(Λⁿ ⊗ᴸ G)` vanishes for `r ≠ 0`; the long exact homology sequence then
  exhibits `Hʳ(M ⊗ᴸ G)` as a kernel of a map between `Hʳ⁺¹`'s for `r < 0`, and `H⁰(M ⊗ᴸ G)`
  as a cokernel of a map between `H⁰(Λᵐ ⊗ᴸ G) = G^m` and `H⁰(Λⁿ ⊗ᴸ G) = Gⁿ`. A descending
  induction on `r` concludes, since finite locally constant sheaves are closed under kernels
  and cokernels.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

/-- A finite module `M` over a noetherian ring is the cokernel in a short exact sequence
`0 ⟶ M₁ ⟶ Rⁿ ⟶ M ⟶ 0` with `M₁` finite and `Rⁿ` finite and flat. -/
lemma ModuleCat.exists_shortExact_flat {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ S : ShortComplex (ModuleCat.{u} R), S.ShortExact ∧ Module.Finite R S.X₁ ∧
      Module.Finite R S.X₂ ∧ Module.Flat R S.X₂ ∧ Nonempty (S.X₃ ≅ M) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  refine ⟨ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker π).subtype) (ModuleCat.ofHom π)
    (by ext x; simp), ShortComplex.ShortExact.mk'
      (ShortComplex.Exact.moduleCat_of_range_eq_ker _ _ (by simp))
      ((ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype _))
      ((ModuleCat.epi_iff_surjective _).2 hπ),
    ?_, ?_, ?_, ⟨Iso.refl _⟩⟩
  · exact inferInstanceAs (Module.Finite R (LinearMap.ker π))
  · exact inferInstanceAs (Module.Finite R (Fin n → R))
  · exact inferInstanceAs (Module.Flat R (Fin n → R))

namespace AlgebraicGeometry

open Scheme

/-! ### Étale locality of finiteness -/

section Finite

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  {X : Scheme.{u}}

/-- **Finiteness is étale local**: if the pullbacks of `G` to the members of an étale cover
are finite, so is `G`. A geometric point of `X` lifts to a member of the cover, and the stalk
of the pullback at the lift is the stalk of `G`. -/
theorem Scheme.IsFiniteSheaf.of_cover (𝒰 : Cover.{u} etalePrecoverage X)
    (G : Sheaf X.smallEtaleTopology A)
    [∀ i, IsFiniteSheaf ((Etale.upperStar A (𝒰.f i)).obj G)] : IsFiniteSheaf G where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (s default)
    have : Etale (𝒰.f i) := 𝒰.map_prop i
    obtain ⟨s', rfl, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s x hx
    exact (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA)
      (F := (Etale.upperStar A (𝒰.f i)).obj G) Ω s').of_iso
      ((Etale.upperStarCompSheafFiberIso A (𝒰.f i) s').app G)

end Finite

namespace Etale

/-! ### Homology of derived tensor products of sheaves in degree zero -/

section Generic

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The homology sheaves of `F[0] ⊗ᴸ G[0]` vanish in positive degrees. -/
lemma isZero_homology_derivedTensor_singleFunctor_of_pos (F G : Sheaf X.smallEtaleTopology A)
    {r : ℤ} (hr : 0 < r) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) := by
  have : ((((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G))).IsLE (0 + 0) :=
    _root_.DerivedCategory.isLE_tensor ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G) 0 0
  exact _root_.DerivedCategory.isZero_of_isLE _ (0 + 0) r (by simpa using hr)

/-- For a flat sheaf `L`, the homology sheaves of `L[0] ⊗ᴸ F[0]` vanish outside degree `0`. -/
lemma isZero_homology_derivedTensor_singleFunctor_of_flat {L : Sheaf X.smallEtaleTopology A}
    (hL : ObjectProperty.flat L) (F : Sheaf X.smallEtaleTopology A) {r : ℤ} (hr : r ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  refine IsZero.of_iso ?_
    ((_root_.DerivedCategory.homologyFunctor _ r).mapIso (singleFunctorObjTensorIso L F hL))
  rcases lt_or_gt_of_ne hr with hr | hr
  · exact _root_.DerivedCategory.isZero_of_isGE _ 0 r hr
  · exact _root_.DerivedCategory.isZero_of_isLE _ 0 r hr

/-- For a flat sheaf `L`, the homology sheaf in degree `0` of `L[0] ⊗ᴸ F[0]` is `L ⊗ F`. -/
noncomputable def homologyZeroDerivedTensorSingleFunctorIsoOfFlat
    {L : Sheaf X.smallEtaleTopology A} (hL : ObjectProperty.flat L)
    (F : Sheaf X.smallEtaleTopology A) :
    (_root_.DerivedCategory.homologyFunctor _ 0).obj
      (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≅ L ⊗ F :=
  (_root_.DerivedCategory.homologyFunctor _ 0).mapIso (singleFunctorObjTensorIso L F hL) ≪≫
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _

/-- **Dimension shifting, kernel form.** For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of
sheaves and a sheaf `G`, if `Hʳ(X₂ ⊗ᴸ G)` vanishes then `Hʳ(X₃ ⊗ᴸ G)` is the kernel of a
morphism `Hʳ⁺¹(X₁ ⊗ᴸ G) ⟶ Hʳ⁺¹(X₂ ⊗ᴸ G)`, by the long exact homology sequence. -/
lemma exists_iso_kernel_homology_derivedTensor_singleFunctor
    {S : ShortComplex (Sheaf X.smallEtaleTopology A)} (hS : S.ShortExact)
    (G : Sheaf X.smallEtaleTopology A) (r n : ℤ) (h : r + 1 = n)
    (h₂ : IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj S.X₂)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G)))) :
    ∃ f : (_root_.DerivedCategory.homologyFunctor _ n).obj
        (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj S.X₁)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) ⟶
        (_root_.DerivedCategory.homologyFunctor _ n).obj
        (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj S.X₂)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)),
      Nonempty ((_root_.DerivedCategory.homologyFunctor _ r).obj
        (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj S.X₃)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) ≅ kernel f) := by
  let Φ := (-⊗ᴸ-(X)[A]).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj G)
  let : Φ.CommShift ℤ := _root_.DerivedCategory.commShiftTensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj G)
  have : Φ.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj G)
  have hT := Φ.map_distinguished _ hS.singleTriangle_distinguished
  let T := Φ.mapTriangle.obj hS.singleTriangle
  refine ⟨(_root_.DerivedCategory.homologyFunctor _ n).map T.mor₁, ⟨?_⟩⟩
  have hex₃ := _root_.DerivedCategory.HomologySequence.exact₃ _ hT r n h
  have : Mono (_root_.DerivedCategory.HomologySequence.δ T r n h) :=
    hex₃.mono_g (h₂.eq_of_src _ _)
  exact IsLimit.conePointUniqueUpToIso
    (_root_.DerivedCategory.HomologySequence.exact₁ _ hT r n h).fIsKernel (limit.isLimit _)

/-- **Dimension shifting, cokernel form.** Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` and
`0 ⟶ X₁' ⟶ X₂' ⟶ X₃' ⟶ 0` be short exact sequences of sheaves with `X₃' ≅ X₁`, and `G` a
sheaf. If `Hʳ⁺¹(X₁ ⊗ᴸ G)` and `Hʳ⁺¹(X₁' ⊗ᴸ G)` vanish, then `Hʳ(X₃ ⊗ᴸ G)` is the cokernel of
a morphism `Hʳ(X₂' ⊗ᴸ G) ⟶ Hʳ(X₂ ⊗ᴸ G)`: it is the cokernel of `Hʳ(X₁ ⊗ᴸ G) ⟶ Hʳ(X₂ ⊗ᴸ G)`,
and `Hʳ(X₂' ⊗ᴸ G) ⟶ Hʳ(X₃' ⊗ᴸ G) ≅ Hʳ(X₁ ⊗ᴸ G)` is an epimorphism. -/
lemma exists_iso_cokernel_homology_derivedTensor_singleFunctor
    {S S' : ShortComplex (Sheaf X.smallEtaleTopology A)} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (e : S'.X₃ ≅ S.X₁) (G : Sheaf X.smallEtaleTopology A) (r : ℤ)
    (h₁ : IsZero ((_root_.DerivedCategory.homologyFunctor _ (r + 1)).obj
      (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj S.X₁)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))))
    (h₁' : IsZero ((_root_.DerivedCategory.homologyFunctor _ (r + 1)).obj
      (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj S'.X₁)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G)))) :
    ∃ f : (_root_.DerivedCategory.homologyFunctor _ r).obj
        (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj S'.X₂)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) ⟶
        (_root_.DerivedCategory.homologyFunctor _ r).obj
        (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj S.X₂)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)),
      Nonempty ((_root_.DerivedCategory.homologyFunctor _ r).obj
        (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj S.X₃)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) ≅ cokernel f) := by
  let Φ := (-⊗ᴸ-(X)[A]).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj G)
  let : Φ.CommShift ℤ := _root_.DerivedCategory.commShiftTensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj G)
  have : Φ.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj G)
  have hT := Φ.map_distinguished _ hS.singleTriangle_distinguished
  have hT' := Φ.map_distinguished _ hS'.singleTriangle_distinguished
  let T := Φ.mapTriangle.obj hS.singleTriangle
  let T' := Φ.mapTriangle.obj hS'.singleTriangle
  let H := _root_.DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) r
  have : Epi (H.map T.mor₂) :=
    (_root_.DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT r (r + 1)).2
      (h₁.eq_of_tgt _ _)
  have : Epi (H.map T'.mor₂) :=
    (_root_.DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT' r (r + 1)).2
      (h₁'.eq_of_tgt _ _)
  let ψ := H.mapIso (Φ.mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso e))
  refine ⟨(H.map T'.mor₂ ≫ ψ.hom) ≫ H.map T.mor₁, ⟨?_⟩⟩
  exact IsColimit.coconePointUniqueUpToIso
      (_root_.DerivedCategory.HomologySequence.exact₂ _ hT r).gIsCokernel
      (colimit.isColimit _) ≪≫
    (cokernelEpiComp (H.map T'.mor₂ ≫ ψ.hom) (H.map T.mor₁)).symm

/-- The pullback along `g` commutes with the homology sheaves of the derived tensor product of
sheaves placed in degree `0`: `g^* Hʳ(F[0] ⊗ᴸ G[0]) ≅ Hʳ((g^* F)[0] ⊗ᴸ (g^* G)[0])`. -/
noncomputable def upperStarHomologyDerivedTensorSingleFunctorIso {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) [(Etale.upperStar A g).PreservesFlat] (F G : Sheaf Y.smallEtaleTopology A)
    (r : ℤ) :
    (Etale.upperStar A g).obj ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(Y)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ≅
    (_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(Z)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((Etale.upperStar A g).obj F))).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((Etale.upperStar A g).obj G))) :=
  (leftDerivedUpperStarHomologyFunctorIso A g r).app _ ≪≫
    (_root_.DerivedCategory.homologyFunctor _ r).mapIso
      (leftDerivedUpperStarTensorIso A g _ _ ≪≫
        ((-⊗ᴸ-(Z)[A]).mapIso ((singleFunctorCompLeftDerivedUpperStarIso A g).app F)).app _ ≪≫
        ((-⊗ᴸ-(Z)[A]).obj _).mapIso ((singleFunctorCompLeftDerivedUpperStarIso A g).app G))

end Generic

/-! ### Finite locally constant sheaves of modules over a finite ring -/

section Modules

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The constant sheaf at a flat module is flat. -/
lemma flat_constantSheaf {X : Scheme.{u}} (M : ModuleCat.{u + 1} Λ) [Module.Flat Λ M] :
    ObjectProperty.flat ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  GrothendieckTopology.flat_presheafToSheaf_obj _ _ _ fun _ ↦
    (ModuleCat.flat_iff_flat M).2 inferInstance

variable [Finite Λ]

/-- **Local step**: let `M` be a finite `Λ`-module and `G` a finite locally constant sheaf on
`Y`. If `r ≤ 0` and, when `r < 0`, the homology sheaves `Hʳ⁺¹(F[0] ⊗ᴸ G'[0])` of finite locally
constant `F` and `G'` are finite locally constant, then so is `Hʳ(M_Y[0] ⊗ᴸ G[0])`.

A presentation `0 ⟶ M₁ ⟶ Λⁿ ⟶ M ⟶ 0` gives a short exact sequence of constant sheaves with
flat middle term. For `r < 0` the homology sheaf is a kernel of a morphism between `Hʳ⁺¹`'s;
for `r = 0` it is a cokernel of a morphism `Λᵐ_Y ⊗ G ⟶ Λⁿ_Y ⊗ G`, using a presentation of
`M₁` as well. -/
lemma isFiniteLocallyConstantSheaf_homology_derivedTensor_constantSheaf {Y : Scheme.{u}}
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf G]
    (r : ℤ) (hr : r ≤ 0)
    (ih : r < 0 → ∀ (F G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsFiniteLocallyConstantSheaf F → IsFiniteLocallyConstantSheaf G' →
      IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ (r + 1)).obj
        (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G')))) :
    IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) := by
  have : IsNoetherianRing Λ := inferInstance
  let c := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have : PreservesFiniteLimits c := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits c := comp_preservesFiniteColimits _ _
  obtain ⟨S, hS, _, _, _, ⟨eM⟩⟩ := ModuleCat.exists_shortExact_flat M
  have hSc := hS.map_of_exact c
  suffices h : IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (c.obj S.X₃))).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) by
    exact IsFiniteLocallyConstantSheaf.of_iso ((_root_.DerivedCategory.homologyFunctor _ r).mapIso
      (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso (c.mapIso eM))).app _))
  rcases hr.lt_or_eq with hr | rfl
  · obtain ⟨f, ⟨e⟩⟩ := exists_iso_kernel_homology_derivedTensor_singleFunctor hSc G r (r + 1) rfl
      (isZero_homology_derivedTensor_singleFunctor_of_flat (flat_constantSheaf S.X₂) G hr.ne)
    have : IsFiniteLocallyConstantSheaf
        ((_root_.DerivedCategory.homologyFunctor _ (r + 1)).obj
          (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj (S.map c).X₁)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) :=
      ih hr (c.obj S.X₁) G inferInstance inferInstance
    have : IsFiniteLocallyConstantSheaf
        ((_root_.DerivedCategory.homologyFunctor _ (r + 1)).obj
          (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj (S.map c).X₂)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) :=
      ih hr (c.obj S.X₂) G inferInstance inferInstance
    have := IsFiniteLocallyConstantSheaf.kernel f
    exact IsFiniteLocallyConstantSheaf.of_iso e.symm
  · obtain ⟨S', hS', _, _, _, ⟨e'⟩⟩ := ModuleCat.exists_shortExact_flat S.X₁
    have hS'c := hS'.map_of_exact c
    obtain ⟨f, ⟨e⟩⟩ := exists_iso_cokernel_homology_derivedTensor_singleFunctor hSc hS'c
      (c.mapIso e') G 0
      (isZero_homology_derivedTensor_singleFunctor_of_pos _ _ (by norm_num))
      (isZero_homology_derivedTensor_singleFunctor_of_pos _ _ (by norm_num))
    have := (inferInstance : IsFiniteLocallyConstantSheaf (c.obj S'.X₂)).tensorObj
      (inferInstance : IsFiniteLocallyConstantSheaf G)
    have := (inferInstance : IsFiniteLocallyConstantSheaf (c.obj S.X₂)).tensorObj
      (inferInstance : IsFiniteLocallyConstantSheaf G)
    have : IsFiniteLocallyConstantSheaf
        ((_root_.DerivedCategory.homologyFunctor _ (0)).obj
          (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj (S'.map c).X₂)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) :=
      IsFiniteLocallyConstantSheaf.of_iso
        (homologyZeroDerivedTensorSingleFunctorIsoOfFlat (flat_constantSheaf S'.X₂) G).symm
    have : IsFiniteLocallyConstantSheaf
        ((_root_.DerivedCategory.homologyFunctor _ (0)).obj
          (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj (S.map c).X₂)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) :=
      IsFiniteLocallyConstantSheaf.of_iso
        (homologyZeroDerivedTensorSingleFunctorIsoOfFlat (flat_constantSheaf S.X₂) G).symm
    have := IsFiniteLocallyConstantSheaf.cokernel f
    exact IsFiniteLocallyConstantSheaf.of_iso e.symm

/-- **Gluing step**: let `r ≤ 0`, and assume, when `r < 0`, that `Hʳ⁺¹(F[0] ⊗ᴸ G[0])` is finite
locally constant for all finite locally constant `F` and `G` on all schemes. Then
`Hʳ(F[0] ⊗ᴸ G[0])` is finite locally constant for finite locally constant `F` and `G`: this
is étale local, and étale locally `F` is the constant sheaf at a finite module. -/
lemma isFiniteLocallyConstantSheaf_homology_derivedTensor_singleFunctor_of_succ
    {Y : Scheme.{u}} (r : ℤ) (hr : r ≤ 0)
    (ih : r < 0 → ∀ {Z : Scheme.{u}} (F G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsFiniteLocallyConstantSheaf F → IsFiniteLocallyConstantSheaf G →
      IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ (r + 1)).obj
        (((-⊗ᴸ-(Z)[ModuleCat.{u + 1} Λ]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G))))
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] [IsFiniteLocallyConstantSheaf G] :
    IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) := by
  obtain ⟨𝒰₀, h𝒰₀⟩ := IsLocallyConstantSheaf.exists_cover₂ F F
  let 𝒰 := 𝒰₀.nonemptyMembers
  have key (i : 𝒰.I₀) : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj
        ((_root_.DerivedCategory.homologyFunctor _ r).obj
          (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G)))) := by
    suffices h : IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
        (((-⊗ᴸ-(𝒰.X i)[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F))).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj G)))) by
      exact IsFiniteLocallyConstantSheaf.of_iso
        (upperStarHomologyDerivedTensorSingleFunctorIso (𝒰.f i) F G r).symm
    have : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F).IsConstant
        (𝒰.X i).smallEtaleTopology := (h𝒰₀ i.1).1
    obtain ⟨M, ⟨eM⟩⟩ :=
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F).mem_essImage_of_isConstant
    have := IsFiniteLocallyConstantSheaf.upperStar (𝒰.f i) F
    have := IsFiniteLocallyConstantSheaf.upperStar (𝒰.f i) G
    have : IsFiniteSheaf ((constantSheaf (𝒰.X i).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj M) := IsFiniteSheaf.of_iso eM.symm
    have : Module.Finite Λ M := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := 𝒰.X i) M
    have := isFiniteLocallyConstantSheaf_homology_derivedTensor_constantSheaf M
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj G) r hr
      fun h F' G' hF' hG' ↦ ih h F' G' hF' hG'
    exact IsFiniteLocallyConstantSheaf.of_iso ((_root_.DerivedCategory.homologyFunctor _ r).mapIso
      (((-⊗ᴸ-(𝒰.X i)[ModuleCat.{u + 1} Λ]).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso eM)).app _))
  have (i : 𝒰.I₀) := (key i).toIsLocallyConstantSheaf
  have (i : 𝒰.I₀) := (key i).toIsFiniteSheaf
  exact { toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_cover 𝒰 _
          toIsFiniteSheaf := IsFiniteSheaf.of_cover 𝒰 _ }

/-- For a finite ring `Λ` and finite locally constant sheaves `F` and `G` of `Λ`-modules on
`X_ét`, every homology sheaf `Hʳ(F[0] ⊗ᴸ G[0])` is finite locally constant: it vanishes for
`r > 0`, and for `r ≤ 0` this is a descending induction on `r`
(`isFiniteLocallyConstantSheaf_homology_derivedTensor_singleFunctor_of_succ`).
-/
theorem isFiniteLocallyConstantSheaf_homology_derivedTensor_singleFunctor {X : Scheme.{u}}
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] [IsFiniteLocallyConstantSheaf G] (r : ℤ) :
    IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) := by
  rcases le_or_gt r 0 with hr | hr
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hr
    induction n generalizing X with
    | zero =>
      exact isFiniteLocallyConstantSheaf_homology_derivedTensor_singleFunctor_of_succ _ hr
        (fun h ↦ by simp at h) F G
    | succ n ih =>
      refine isFiniteLocallyConstantSheaf_homology_derivedTensor_singleFunctor_of_succ _ hr
        (fun _ Z F' G' hF' hG' ↦ ?_) F G
      have h : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
      rw [h]
      exact ih F' G' (by omega)
  · exact IsFiniteLocallyConstantSheaf.of_isZero
      (isZero_homology_derivedTensor_singleFunctor_of_pos F G hr)

end Modules

end Etale

end AlgebraicGeometry
