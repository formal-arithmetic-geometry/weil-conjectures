/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.Paper.ModuleCupGlobalTensorPullback
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # Global ringed-space pullback comparisons

The ringed-space map throughout is `toGlobalSectionsPoint X`, with target
`globalSectionsPoint X`, not a morphism of schemes. Modules on this point are
identified with Γ(X,O_X)-modules by evaluation. No condition on X is imposed.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Naturality of the two tensor-comparison paths in a square of functors. -/
private theorem tensorComparison_paths_natural
    {C₁ C₂ D₁ D₂ : Type*}
    [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    (Q : C₁ ⥤ D₁) [Q.LaxMonoidal] (Q' : C₂ ⥤ D₂) [Q'.LaxMonoidal]
    (F : C₁ ⥤ C₂) (L : D₁ ⥤ D₂) (α : Q ⋙ L ⟶ F ⋙ Q')
    (δ : ∀ A B, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B)
    (hnat : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      L.map (f ⊗ₘ g) ≫ (δ A' B').hom = (δ A B).hom ≫ (L.map f ⊗ₘ L.map g))
    (c : (Functor.postcompose₂.obj F).obj (curriedTensor C₁) ⟶
      (((Functor.whiskeringLeft₂ C₂).obj F).obj F).obj (curriedTensor C₂))
    {K₀ K M₀ M : C₁} (a : K₀ ⟶ K) (b : M₀ ⟶ M) :
    (L.map (Q.map a ⊗ₘ Q.map b) ≫
        (L.map (Functor.LaxMonoidal.μ Q K M) ≫
          α.app (K ⊗ M) ≫ Q'.map ((c.app K).app M)) =
      (L.map (Functor.LaxMonoidal.μ Q K₀ M₀) ≫
          α.app (K₀ ⊗ M₀) ≫
            Q'.map ((c.app K₀).app M₀)) ≫
        Q'.map (F.map a ⊗ₘ F.map b)) ∧
    (L.map (Q.map a ⊗ₘ Q.map b) ≫
        ((δ (Q.obj K) (Q.obj M)).hom ≫
          (α.app K ⊗ₘ α.app M) ≫
            Functor.LaxMonoidal.μ Q' (F.obj K) (F.obj M)) =
      ((δ (Q.obj K₀) (Q.obj M₀)).hom ≫
          (α.app K₀ ⊗ₘ α.app M₀) ≫
            Functor.LaxMonoidal.μ Q' (F.obj K₀) (F.obj M₀)) ≫
        Q'.map (F.map a ⊗ₘ F.map b)) := by
  have hc : F.map (a ⊗ₘ b) ≫ (c.app K).app M =
      (c.app K₀).app M₀ ≫ (F.map a ⊗ₘ F.map b) := by
    exact (Functor.OplaxMonoidal.app_app_comp_tensorHom c a b).symm
  have hleft :
      L.map (Q.map a ⊗ₘ Q.map b) ≫
        (L.map (Functor.LaxMonoidal.μ Q K M) ≫
          α.app (K ⊗ M) ≫ Q'.map ((c.app K).app M)) =
      (L.map (Functor.LaxMonoidal.μ Q K₀ M₀) ≫
          α.app (K₀ ⊗ M₀) ≫
            Q'.map ((c.app K₀).app M₀)) ≫
        Q'.map (F.map a ⊗ₘ F.map b) := by
    have hμ := congrArg
      (fun t => L.map t ≫ α.app (K ⊗ M) ≫
        Q'.map ((c.app K).app M))
      (Functor.LaxMonoidal.μ_natural Q a b)
    simp only [Functor.map_comp, Category.assoc] at hμ
    have hα := congrArg
      (fun t => L.map (Functor.LaxMonoidal.μ Q K₀ M₀) ≫ t ≫
        Q'.map ((c.app K).app M))
      (α.naturality (a ⊗ₘ b))
    have hδ := congrArg
      (fun t => L.map (Functor.LaxMonoidal.μ Q K₀ M₀) ≫
        α.app (K₀ ⊗ M₀) ≫ Q'.map t) hc
    simp only [Functor.map_comp] at hδ
    simp only [Functor.comp_map, Category.assoc] at hα
    have ht := hμ.trans (hα.trans hδ)
    simpa only [Category.assoc] using ht
  have hright :
      L.map (Q.map a ⊗ₘ Q.map b) ≫
        ((δ (Q.obj K) (Q.obj M)).hom ≫
          (α.app K ⊗ₘ α.app M) ≫
            Functor.LaxMonoidal.μ Q' (F.obj K) (F.obj M)) =
      ((δ (Q.obj K₀) (Q.obj M₀)).hom ≫
          (α.app K₀ ⊗ₘ α.app M₀) ≫
            Functor.LaxMonoidal.μ Q' (F.obj K₀) (F.obj M₀)) ≫
        Q'.map (F.map a ⊗ₘ F.map b) := by
    have ha : L.map (Q.map a) ≫ α.app K =
        α.app K₀ ≫ Q'.map (F.map a) := α.naturality a
    have hb : L.map (Q.map b) ≫ α.app M =
        α.app M₀ ≫ Q'.map (F.map b) := α.naturality b
    have hδ := congrArg
      (fun t => t ≫ (α.app K ⊗ₘ α.app M) ≫
        Functor.LaxMonoidal.μ Q' (F.obj K) (F.obj M))
      (hnat _ _ _ _ (Q.map a) (Q.map b))
    have hmid :
        (L.map (Q.map a) ⊗ₘ L.map (Q.map b)) ≫
            (α.app K ⊗ₘ α.app M) =
          (α.app K₀ ⊗ₘ α.app M₀) ≫
            (Q'.map (F.map a) ⊗ₘ Q'.map (F.map b)) :=
      (tensorHom_comp_tensorHom _ _ _ _).trans
        ((congrArg₂ (fun x y => MonoidalCategory.tensorHom x y) ha hb).trans
          (tensorHom_comp_tensorHom _ _ _ _).symm)
    have hα := congrArg
      (fun t => (δ (Q.obj K₀) (Q.obj M₀)).hom ≫ t ≫
        Functor.LaxMonoidal.μ Q' (F.obj K) (F.obj M)) hmid
    simp only [Category.assoc] at hα
    have hμ := congrArg
      (fun t => (δ (Q.obj K₀) (Q.obj M₀)).hom ≫
        (α.app K₀ ⊗ₘ α.app M₀) ≫ t)
      (Functor.LaxMonoidal.μ_natural Q' (F.map a) (F.map b))
    simp only [Category.assoc] at hδ hμ
    have ht := hδ.trans (hα.trans hμ)
    simpa only [Category.assoc] using ht
  exact ⟨hleft, hright⟩

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance globalTensorCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalTensorMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalTensorSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance globalTensorColimits :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance globalTensorPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalTensorClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
local instance globalTensorFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X

-- Keep matching reducible while elaborating the naturality calculation.
set_option backward.isDefEq.respectTransparency true in
/-- The full global tensor comparison polygon, for all integer complexes,
not just flat or bounded ones. P, L, α and δ are the pullback data and the
canonical tensor isomorphism of the global tensor theorem. Normalization on
K-flat pairs fixes δ to that canonical isomorphism; naturality alone would not
suffice. The conclusion is precisely the two composites of Stacks Tag 0FP0,
with the two left downward arrows composed as α_K tensor α_M and with the
bottom arrow the lax localization comparison. The right downward arrows are
α at the total tensor, followed by the inverse ordinary tensor constraint.
Source: Stacks, Tag 0FP0, Lemma 20.27.5.
(blueprint: lem-sc-module-cup-global-tensor-comparison)
Proof: choose K-flat resolutions K0 → K and M0 → M. Their total tensor is
K-flat. The ordinary tensor-pullback comparison is natural, so the rectangle
from p*Tot(K0 tensor M0) to p*Tot(K tensor M), followed by the ordinary
inverse tensor constraint, commutes with the tensor of the two resolution
maps. Naturality of α and the lax comparison of Qh identifies the top/right
path with the left path computed on K0,M0 followed by the bottom tensor maps.
By normalization δ on K0,M0 gives that left path. Naturality of δ identifies
its transport with δ on K,M. Localized resolution maps are isomorphisms and
remain so under L and tensor; cancel their tensor composite to obtain the
polygon for K,M. Every homotopy-category object has a complex representative,
so this proves the equation as stated. This uses no assertion that p is flat,
no preservation of arbitrary quasi-isomorphisms by p*, and no condition on X. -/
theorem globalRingedSpace_tensor_comparison_diagram
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (L : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (δ : ∀ A B, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B)
    (hnat : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      L.map (f ⊗ₘ g) ≫ (δ A' B').hom = (δ A B).hom ≫ (L.map f ⊗ₘ L.map g))
    (hflat : ∀ K M : CochainComplex
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℤ,
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).kFlat M →
        moduleCup_globalTensorDiagram X P L α δ
          ((HomotopyCategory.quotient _ _).obj K)
          ((HomotopyCategory.quotient _ _).obj M))
    (K M : HomotopyCategory
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (ComplexShape.up ℤ)) :
    moduleCup_globalTensorDiagram X P L α δ K M := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  let q := HomotopyCategory.quotient
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (ComplexShape.up ℤ)
  let F := P.mapHomotopyCategory (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh
    (C := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
  -- Use the generic derived tensor structure of the comparison definition.
  let : MonoidalCategory
      (DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
    DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory _
  let Q' := DerivedCategory.Qh.{u}
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  -- Resolve both arguments in the K-flat left derivability structure.
  obtain ⟨R⟩ := (inferInstance : Nonempty ((HomotopyCategory.quasiIso
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        (ComplexShape.up ℤ)).localizerMorphismKFlat.LeftResolution (q.obj K)))
  obtain ⟨S⟩ := (inferInstance : Nonempty ((HomotopyCategory.quasiIso
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        (ComplexShape.up ℤ)).localizerMorphismKFlat.LeftResolution (q.obj M)))
  let K₀ := R.X₁.obj.as
  let M₀ := S.X₁.obj.as
  have hK₀ := (HomotopyCategory.kFlat_quotient_obj_iff K₀).1 R.X₁.property
  have hM₀ := (HomotopyCategory.kFlat_quotient_obj_iff M₀).1 S.X₁.property
  let a : q.obj K₀ ⟶ q.obj K := R.w
  let b : q.obj M₀ ⟶ q.obj M := S.w
  let c := Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (ComplexShape.up ℤ) P
  obtain ⟨hleft, hright⟩ :=
    tensorComparison_paths_natural Q Q' F L α δ hnat c a b
  have : IsIso (Q.map a) := Localization.inverts Q _ _ R.hw
  have : IsIso (Q.map b) := Localization.inverts Q _ _ S.hw
  -- Localized resolution maps and their tensor are isomorphisms.
  apply (cancel_epi (L.map (Q.map a ⊗ₘ Q.map b))).1
  have h₀ :
      L.map (Functor.LaxMonoidal.μ Q (q.obj K₀) (q.obj M₀)) ≫
          α.app (q.obj K₀ ⊗ q.obj M₀) ≫
            Q'.map ((c.app (q.obj K₀)).app (q.obj M₀)) =
        (δ (Q.obj (q.obj K₀)) (Q.obj (q.obj M₀))).hom ≫
          (α.app (q.obj K₀) ⊗ₘ α.app (q.obj M₀)) ≫
            Functor.LaxMonoidal.μ Q' (F.obj (q.obj K₀)) (F.obj (q.obj M₀)) := by
    set_option backward.isDefEq.respectTransparency false in
    exact hflat K₀ M₀ hK₀ hM₀
  set_option backward.isDefEq.respectTransparency false in
  exact hleft.trans ((congrArg (fun t => t ≫ Q'.map (F.map a ⊗ₘ F.map b))
    h₀).trans hright.symm)

end
end AlgebraicGeometry.Scheme.Modules
