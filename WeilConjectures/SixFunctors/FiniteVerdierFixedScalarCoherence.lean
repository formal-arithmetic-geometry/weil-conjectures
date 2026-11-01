/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData
import WeilConjectures.SixFunctors.NormalizedSiteScalarTensor.NormalizedSiteScalarTensorComposition
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax

/-! # Monoidality of the fixed scalar units and compositors -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

private theorem derived_comp_unit
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : D ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    (e : F ≅ 𝟭 D) (c₀ : F ⋙ F ≅ F)
    (hc : c₀ = Functor.isoWhiskerRight e F ≪≫ F.leftUnitor) :
    (Functor.mapDerivedCategoryCompIso F F).symm ≪≫
        Functor.mapDerivedCategoryNatIso c₀ =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D)
        F.mapDerivedCategory ≪≫ F.mapDerivedCategory.leftUnitor := by
  subst c₀
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [Functor.mapDerivedCategoryNatIso_trans]
  have hu : (Functor.mapDerivedCategoryNatIso F.leftUnitor).hom = 𝟙 _ := by
    exact Functor.mapDerivedCategoryNatIso_refl
  rw [hu, Category.comp_id]
  apply (cancel_mono (Functor.mapDerivedCategoryCompIso (𝟭 D) F).hom).mp
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_comp, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_isoWhiskerRight,
    Iso.inv_hom_id_assoc]
  have h := Functor.mapDerivedCategoryCompIso_id_comp F
  have hh : (Functor.mapDerivedCategoryCompIso (𝟭 D) F).inv =
      Functor.whiskerRight (Functor.mapDerivedCategoryIdIso D).hom
        F.mapDerivedCategory := by
    apply (cancel_epi (Functor.mapDerivedCategoryCompIso (𝟭 D) F).hom).mp
    rw [Iso.hom_inv_id, h]
    rfl
  rw [← hh]
  have hu' : F.mapDerivedCategory.leftUnitor.hom = 𝟙 F.mapDerivedCategory := by rfl
  rw [hu']
  erw [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem scalar_comp_unit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A) (hc : φ = φ.comp φ) :
    pbcFixedScalarExtensionComp J φ φ φ hc =
      Functor.isoWhiskerLeft (pbcFixedScalarExtension J φ)
        (normalizedOriginScalarUnit J φ hφ) ≪≫
      (pbcFixedScalarExtension J φ).rightUnitor := by
  subst φ
  apply Adjunction.leftAdjointCompIso_comp_id
  exact derived_comp_unit _ _ _ (by
    apply Iso.ext
    ext M U x
    rfl)

private theorem tensor_identity_from_comp
    {D : Type*} [Category D] (T : D × D ⥤ D) (F : D ⥤ D)
    (δ : T ⋙ F ≅ F.prod F ⋙ T) (z : F ≅ 𝟭 D)
    (h : ∀ U V,
      z.hom.app (F.obj (T.obj (U, V))) ≫ δ.hom.app (U, V) =
        F.map (δ.hom.app (U, V)) ≫ δ.hom.app (F.obj U, F.obj V) ≫
          T.map (Prod.mkHom (z.hom.app (F.obj U)) (z.hom.app (F.obj V))))
    (U V : D) :
    δ.hom.app (U, V) ≫ T.map (Prod.mkHom (z.hom.app U) (z.hom.app V)) =
      z.hom.app (T.obj (U, V)) := by
  let : F.Faithful := Functor.Faithful.of_iso z.symm
  have hz (W : D) : z.hom.app (F.obj W) = F.map (z.hom.app W) := by
    apply (cancel_mono (z.hom.app W)).mp
    exact (z.hom.naturality (z.hom.app W)).symm
  have hn := δ.hom.naturality (Prod.mkHom (z.hom.app U) (z.hom.app V))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  have hc := h U V
  rw [hz, hz, hz] at hc
  rw [← hn, ← F.map_comp_assoc] at hc
  exact F.map_injective ((cancel_mono (δ.hom.app (U, V))).mp hc).symm

/-- The fixed scalar unit and compositor respect every representative-normalized
strong tensor structure on a coefficient tower, on either site.

Source: blueprint cor-coef-finite-verdier.proof.md, quotient cocycle sentence;
Stacks 07A4 and 0D6D, scalar balancing on flat K-flat representatives.
(blueprint: lem-coef-verdier-fixed-scalar-coherence).

Proof: on ordinary sections the scalar compositor sends ((x tensor b) tensor c)
to x tensor psi(b)c. Its tensor square and the ordinary balanced tensor square
both send ((x tensor y) tensor b) tensor c to
(x tensor psi(b)c) tensor (y tensor 1). Sheafify, pass through the signed total
complex, and paste the representative equations for the fixed scalar mates and
for each normalized tensorator. On flat-term K-flat representatives all counit
and tensor comparison maps are invertible; cancel them to obtain the compositor
square. Transport along representative isomorphisms to arbitrary derived objects.
The unit square follows by substituting identity maps in this composition square:
the fixed identity compositor is the whiskered fixed scalar unit, and naturality
and cancellation give its tensor square. For strong monoidal functors an invertible
tensor-compatible transformation preserves the unit by the left unit axioms.
Thus both fixed natural isomorphisms are monoidal. This argument uses no flatness
of the quotient ring itself. -/
theorem finiteVerdier_fixedScalar_coherence
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    (R : ℕ → Type (u + 1)) [∀ n, CommRing (R n)]
    (φ : ∀ {n m : ℕ}, m ≤ n → R n →+* R m)
    (φId : ∀ n, φ (le_refl n) = RingHom.id (R n))
    (φComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      φ (g.trans h) = (φ g).comp (φ h))
    (c : ∀ {n m : ℕ} (h : m ≤ n), (pbcFixedScalarExtension J (φ h)).CoreMonoidal)
    (μ : ∀ {n m : ℕ} (h : m ≤ n),
      tensor (C := DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n)))) ⋙
          pbcFixedScalarExtension J (φ h) ≅
        (pbcFixedScalarExtension J (φ h)).prod (pbcFixedScalarExtension J (φ h)) ⋙
          tensor (C := DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R m)))))
    (hμ : ∀ {n m : ℕ} (h : m ≤ n) K L, (μ h).app (K, L) = ((c h).μIso K L).symm)
    (hn : ∀ {n m : ℕ} (h : m ≤ n),
      letI := (finiteVerdierOrdinaryAdjunction J (φ h)).isLeftAdjoint
      Etale.ExceptionalCoefficients.TensorNormalizationAux
        (finiteVerdierOrdinaryExtension J (φ h)) (pbcFixedScalarExtension J (φ h))
        (finiteVerdierScalarRepresentative J (φ h)) (μ h)) :
    (∀ n,
      letI := (c (le_refl n)).toMonoidal
      NatTrans.IsMonoidal (normalizedOriginScalarUnit J (φ (le_refl n)) (φId n)).hom) ∧
    (∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      letI := (c h).toMonoidal
      letI := (c g).toMonoidal
      letI := (c (g.trans h)).toMonoidal
      NatTrans.IsMonoidal (pbcFixedScalarExtensionComp J (φ h) (φ g) (φ (g.trans h))
        (φComp h g)).hom) := by
  have hδ {n m : ℕ} (h : m ≤ n) K L :
      (μ h).hom.app (K, L) = ((c h).μIso K L).inv :=
    congrArg Iso.hom (hμ h K L)
  constructor
  · intro n
    let h₀ : n ≤ n := le_refl n
    let F := pbcFixedScalarExtension J (φ h₀)
    let z := normalizedOriginScalarUnit J (φ h₀) (φId n)
    let := (c h₀).toMonoidal
    apply NatTrans.IsMonoidal.of_isIso_of_δ z.hom
    intro K L
    have hcomp' : ∀ U V,
        z.hom.app (F.obj (U ⊗ V)) ≫ (μ h₀).hom.app (U, V) =
          F.map ((μ h₀).hom.app (U, V)) ≫ (μ h₀).hom.app (F.obj U, F.obj V) ≫
            (Functor.uncurry.obj (curriedTensor
              (DerivedCategory (Sheaf J (ModuleCat (R n)))))).map
              (Prod.mkHom (z.hom.app (F.obj U)) (z.hom.app (F.obj V))) := by
      intro U V
      have hh := NormalizedSiteScalarTensor.scalar_tensor_comp
        J (φ h₀) (φ h₀) (φ h₀) (by
          rw [φId n]
          simp)
        (μ h₀) (μ h₀) (μ h₀) (hn h₀) (hn h₀) (hn h₀) U V
      rw [scalar_comp_unit J (R n) (φ h₀) (φId n)] at hh
      simpa only [F, z, Functor.uncurry, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
        Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
        Category.comp_id] using hh
    change z.hom.app (K ⊗ L) ≫ 𝟙 _ =
      ((c h₀).μIso K L).inv ≫ (z.hom.app K ⊗ₘ z.hom.app L)
    simpa only [Functor.OplaxMonoidal.comp_δ, Functor.OplaxMonoidal.id_δ,
      Functor.prod_obj, Functor.comp_obj, Functor.id_obj, Functor.id_map,
      Functor.uncurry_obj_obj, Functor.uncurry_obj_map, curriedTensor_obj_obj,
      curriedTensor_map_app, curriedTensor_obj_map, hδ, Category.assoc,
      Category.id_comp, Category.comp_id, MonoidalCategory.tensorHom_def] using
      (tensor_identity_from_comp
      (Functor.uncurry.obj (curriedTensor
        (DerivedCategory (Sheaf J (ModuleCat (R n)))))) F (μ h₀) z hcomp' K L).symm
  · intro n m r h g
    let χ := φ (g.trans h)
    let a := pbcFixedScalarExtensionComp J (φ h) (φ g) χ (φComp h g)
    let := (c h).toMonoidal
    let := (c g).toMonoidal
    let := (c (g.trans h)).toMonoidal
    apply NatTrans.IsMonoidal.of_isIso_of_δ a.hom
    intro K L
    change a.hom.app (K ⊗ L) ≫ ((c (g.trans h)).μIso K L).inv =
      ((pbcFixedScalarExtension J (φ g)).map (((c h).μIso K L).inv) ≫
        ((c g).μIso ((pbcFixedScalarExtension J (φ h)).obj K)
          ((pbcFixedScalarExtension J (φ h)).obj L)).inv) ≫
        (a.hom.app K ⊗ₘ a.hom.app L)
    have hh := WeilConjectures.NormalizedSiteScalarTensor.scalar_tensor_comp
      J (φ h) (φ g) χ (φComp h g) (μ h) (μ g) (μ (g.trans h))
      (hn h) (hn g) (hn (g.trans h)) K L
    simpa only [a, Functor.uncurry, Iso.trans_hom, Functor.OplaxMonoidal.comp_δ,
      NatTrans.comp_app, Functor.comp_obj, Functor.prod_obj,
      Functor.uncurry_obj_obj, Functor.uncurry_obj_map,
      curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
      MonoidalCategory.tensorHom_def, hδ, Category.assoc] using hh

end WeilConjectures
