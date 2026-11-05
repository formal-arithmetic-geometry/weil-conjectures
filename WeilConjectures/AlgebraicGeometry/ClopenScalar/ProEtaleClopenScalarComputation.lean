/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData

/-! # Calculus of the canonical scalar-extension computation

The canonical computation morphism `computation p P` of a recorded presentation is natural in
the cochain complex `P`, commutes with equality transports along equal coefficient maps, and
represents the normalized derived compositor on flat-term K-flat complexes.

Source: Stacks Project, Tags 06YY and 0D6D (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] ClopenLocalization.sheafify ClopenLocalization.locallyBijective

/-- The canonical computation morphism is natural in the cochain complex.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
theorem computation_naturality {Z : Scheme.{t}}
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} {a : R ⟶ S}
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation.{t + 1, t,
      max u (t + 1), max (u + 1) (t + 2)} a)
    {P P' : CochainComplex (Mods.{t, u} R) ℤ} (φ : P ⟶ P') :
    (extD p).map (DerivedCategory.Q.map φ) ≫ computation p P' =
      computation p P ≫
        DerivedCategory.Q.map ((p.ordinary.mapHomologicalComplex (.up ℤ)).map φ) := by
  have h₁ := (DerivedCategory.quotientCompQhIso (Mods.{t, u} R)).inv.naturality φ
  have h₂ := p.counit.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map φ)
  have h₃ := (p.ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.naturality φ
  have h₄ := (DerivedCategory.quotientCompQhIso (Mods.{t, u} S)).hom.naturality
    ((p.ordinary.mapHomologicalComplex (.up ℤ)).map φ)
  simp only [Functor.comp_map] at h₁ h₂ h₃ h₄
  unfold computation
  simp only [← Category.assoc, ← Functor.map_comp, h₁]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₂, ← Functor.map_comp_assoc, h₃, Functor.map_comp_assoc, h₄]

/-- Transporting the derived extension and its canonical computation along an equality of
coefficient maps only transports the termwise extended complex.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
theorem eqToHom_comp_extD_map_comp_computation {Z : Scheme.{t}} (q : Presentations.{t, u} Z)
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} {f g : R ⟶ S} (h : f = g)
    {K : DerivedCategory (Mods.{t, u} R)} (P : CochainComplex (Mods.{t, u} R) ℤ)
    (φ : K ⟶ DerivedCategory.Q.obj P) :
    eqToHom (congrArg (fun f ↦ (extD.{t, u} (Z := Z) (q f)).obj K) h) ≫ (extD (q g)).map φ ≫
        computation (q g) P =
      (extD (q f)).map φ ≫ computation (q f) P ≫ DerivedCategory.Q.map (eqToHom (congrArg
        (fun f ↦ ((ext.{t, u} (Z := Z) (q f)).mapHomologicalComplex (.up ℤ)).obj P) h)) := by
  subst h
  simp

/-- On a flat-term K-flat complex, the normalized derived compositor is represented through the
canonical computations by the termwise ordinary compositor.
Source: Stacks 06YY, 0D6D (auxiliary; not a blueprint node). -/
theorem normalization_derived_hom_app_comp_computation {Z : Scheme.{t}}
    {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    {R S T : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Mods.{t, u} R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R := R) P)
    (hf : ∀ k : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology Z)
      (R := R) (P.X k)) :
    (n.derived a b).hom.app (DerivedCategory.Q.obj P) ≫ computation (p (a ≫ b)) P =
      (extD (p b)).map (computation (p a) P) ≫
        computation (p b) (((ext (p a)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (n.ordinary a b) (.up ℤ)).hom.app P) := by
  have h₂ := n.representative a b P hP hf
  have h₃ := (p b).counit.naturality
    (((p a).ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.app P)
  have h₄ := (DerivedCategory.quotientCompQhIso (Mods.{t, u} T)).hom.naturality
    ((Functor.mapHomologicalComplexCompIso (n.ordinary a b) (.up ℤ)).hom.app P)
  have h₅ : (extD (p b)).map ((DerivedCategory.quotientCompQhIso (Mods.{t, u} S)).hom.app
      (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (p b).derived.map ((DerivedCategory.quotientCompQhIso (Mods.{t, u} S)).inv.app
      (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp only [Functor.comp_map, Functor.comp_obj] at h₃ h₄
  unfold computation
  rw [← NatTrans.naturality_assoc]
  erw [reassoc_of% h₂]
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.comp_map]
  congr 1
  congr 1
  rw [← h₄, reassoc_of% h₅]
  erw [reassoc_of% h₃]
  congr 1
  simp only [← Functor.map_comp_assoc]
  congr 2
  change (HomotopyCategory.quotient _ _).map
      ((Functor.mapHomologicalComplexCompIso (n.ordinary a b) (.up ℤ)).hom.app P) ≫ _ = _
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
