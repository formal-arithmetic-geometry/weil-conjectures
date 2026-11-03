/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
public import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorPresentation
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteProjectiveDualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.ProEtalePullbackInternalHom

/-!
# Closed support and sequential derived limits

Source: Stacks Project, Tag 09AA; blueprint
`sec-six-functors-basics/sk-lem-formal-closed-support-ii`, node
`det-formal-closed-support-ii-limits`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w x

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/--
The properties required of each functor in the closed-support limits statement, for a
functor `F` with its given (canonical) commutation with shifts.
Source: Stacks Project, Tag 09AA; blueprint
`det-formal-closed-support-ii-limits`.
-/
structure ClosedSupportLimitFunctorProperties
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] : Prop where
  additive : F.Additive
  triangulated : F.IsTriangulated
  products : ∀ (I : Type (max u v w x)),
    PreservesLimitsOfShape (Discrete I) F
  fibers : ∀ (T : Triangle C), T ∈ distTriang C →
    F.mapTriangle.obj T ∈ distTriang D
  sequential_limits :
    ∀ {K : ℕ → C} [HasProduct K]
      (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
      (L : C) (p : L ⟶ ∏ᶜ K)
      (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle f L p δ →
      ∀ [HasProduct (fun n : ℕ => F.obj (K n))],
      ∃ e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n : ℕ => F.obj (K n)),
        (∀ n : ℕ, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) ∧
        IsDerivedLimitTriangle (fun n : ℕ => F.map (f n))
          (F.obj L) (F.map p ≫ e.hom)
          (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L)
  comparison_isIso :
    ∀ {K : ℕ → C} [HasProduct K]
      (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
      (L : C) (p : L ⟶ ∏ᶜ K)
      (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle f L p δ →
      ∀ [HasProduct (fun n : ℕ => F.obj (K n))]
      (L' : D) (p' : L' ⟶ ∏ᶜ (fun n : ℕ => F.obj (K n)))
      (δ' : (∏ᶜ (fun n : ℕ => F.obj (K n))) ⟶ L'⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle (fun n : ℕ => F.map (f n)) L' p' δ' →
      (e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n : ℕ => F.obj (K n))) →
      (∀ n : ℕ, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) →
      (ψ : F.obj L ⟶ L') →
      (ψ ≫ p' = F.map p ≫ e.hom) →
      ((e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) ≫
        (shiftFunctor D (1 : ℤ)).map ψ = δ') →
      IsIso ψ

open CategoryTheory.MonoidalCategory in
open CategoryTheory.MonoidalCategory in

private theorem coverRetract_dualizable
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (S : Scheme.{u}) (L : FormalSupportModules Λ S)
    (hL : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
      ∀ c : 𝒰.I₀, ∃ n : ℕ,
        Nonempty (Retract ((formalSupportPullback Λ (𝒰.f c)).obj L)
          (Mod.finiteFree (condensedRingObj Λ (𝒰.X c)) n))) :
    IsDualizable L := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hL
  let t := MonoidalClosed.ihomUnitTensorToIhom L L
  have ht : IsIso t := by
    apply ProEtale.isIso_mapMod_of_cover 𝒰 (condensedRingObj Λ S) t
    intro c
    have : WeaklyEtale (𝒰.f c) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk c)
    obtain ⟨n, ⟨r⟩⟩ := h𝒰 c
    have hd : IsDualizable ((supportPullback Λ (𝒰.f c)).obj L) :=
      finiteFree_retract_isDualizable Λ (𝒰.X c) n _ r.i r.r r.retract
    obtain ⟨hd⟩ := hd
    let M := (supportPullback Λ (𝒰.f c)).obj L
    let : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
    have : IsIso (MonoidalClosed.ihomUnitTensorToIhom M M) :=
      MonoidalClosed.isIso_ihomUnitTensorToIhom Mᘁ M M
    have := supportPullback_ihomComparison_isIso Λ (𝒰.f c) L
    have : IsIso ((supportPullback Λ (𝒰.f c)).map t) :=
      Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_of_ihomComparison _ _ _
    have : IsIso ((Mod.comap
        (asIso (condensedPullbackHom Λ (𝒰.f c))).inv).map
          (((ProEtale.upperStar Ab.{u + 1} (𝒰.f c)).mapMod _).map t)) := this
    exact isIso_of_reflects_iso _
      (Mod.comap (asIso (condensedPullbackHom Λ (𝒰.f c))).inv)
  let := MonoidalClosed.exactPairingOfIsIso L
  let := BraidedCategory.exactPairing_swap ((ihom L).obj (𝟙_ _)) L
  exact ⟨⟨(ihom L).obj (𝟙_ _)⟩⟩

private theorem fiberProducts
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (I : Type*) [HasProductsOfShape I C]
    (G J : C ⥤ C) (a : G ⟶ 𝟭 C) (b : 𝟭 C ⟶ J)
    (δ : J ⟶ G ⋙ shiftFunctor C (1 : ℤ))
    (h : ∀ K, Triangle.mk (a.app K) (b.app K) (δ.app K) ∈ distTriang C)
    [PreservesLimitsOfShape (Discrete I) J] :
    PreservesLimitsOfShape (Discrete I) G := by
  have (K : I → C) : IsIso (piComparison G K) := by
    let T (K : C) := Triangle.mk (a.app K) (b.app K) (δ.app K)
    let q : T (∏ᶜ K) ⟶ productTriangle (fun t ↦ T (K t)) :=
      productTriangle.lift _ (fun t ↦ Triangle.homMk _ _
        (G.map (Pi.π K t)) (Pi.π K t) (J.map (Pi.π K t))
        (by exact (a.naturality (Pi.π K t)).symm)
        (by exact (b.naturality (Pi.π K t)).symm)
        (by exact (δ.naturality (Pi.π K t)).symm))
    have h₂ : IsIso q.hom₂ := by
      change IsIso (piComparison (𝟭 C) K)
      infer_instance
    have h₃ : IsIso q.hom₃ := by
      change IsIso (piComparison J K)
      infer_instance
    exact isIso₁_of_isIso₂₃ q (h _) (productTriangle_distinguished _ (fun t ↦ h (K t)))
      h₂ h₃
  have (K : I → C) : PreservesLimit (Discrete.functor K) G :=
    PreservesProduct.of_iso_comparison G K
  exact preservesLimitsOfShape_of_discrete G

/-- Assertions that closed support and finite-free tensoring preserve products,
fibers, and sequential derived limits. Source: Stacks Project, Tag 09AA;
blueprint `det-formal-closed-support-ii-limits`.

Proof: the support kernel is computed sectionwise and commutes with products and
finite limits; the inverse-image and direct-image module functors preserve these
limits and their derived functors are triangulated. K-injective resolutions and
termwise products identify the derived products, and the Roos triangle is carried
to the Roos triangle of the image tower. On a covering trivializing the finite
locally free module, tensor is a finite direct-sum functor, hence exact and
product preserving; the same termwise calculation gives its derived statement.
The product comparison is the one commuting with every projection, and every
Roos-triangle completion with those product comparisons is invertible by TR3.
-/
structure ClosedSupportIILimitsAssertions
    {Z V X S : Scheme.{u}} (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (i : Z ⟶ X) (j : V ⟶ X) (u : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion u]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : FormalSupportModules Λ S) : Prop where
  j_star : ClosedSupportLimitFunctorProperties
    ((formalSupportPullback Λ j).mapDerivedCategory)
  u_star : ClosedSupportLimitFunctorProperties
    ((formalSupportPullback Λ u).mapDerivedCategory)
  u_star_closed_support : ClosedSupportLimitFunctorProperties
    ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
      (formalSupportPullback Λ u).mapDerivedCategory)
  i_star : ClosedSupportLimitFunctorProperties
    ((formalSupportPullback Λ i).mapDerivedCategory)
  rj_star : ClosedSupportLimitFunctorProperties
    ((lowerStar Λ j).rightDerivedFunctor)
  closed_support : ClosedSupportLimitFunctorProperties
    ((formalClosedSupport Λ i j).rightDerivedFunctor)
  tensor : ClosedSupportLimitFunctorProperties
    ((derivedTensor Λ S).obj
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L))

end AlgebraicGeometry.ProEtale.CondensedRing
