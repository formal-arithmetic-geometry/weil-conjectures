module
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
@[expose] public section
set_option autoImplicit false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat
-- A sign change preserves invertibility, but it does not preserve a nonzero counit.
private theorem sign_obstruction {C : Type*} [Category C] [Preadditive C]
    {X Y Z : C} (a : X ≅ Y) (f : Y ⟶ Z) (g : X ⟶ Z) (hne : -g ≠ g) :
    ¬ ∀ b : X ≅ Y, b.hom ≫ f = g := by
  intro h
  let b : X ≅ Y :=
    { hom := -a.hom
      inv := -a.inv
      hom_inv_id := by simp
      inv_hom_id := by simp }
  have ha := h a
  have hb := h b
  change (-a.hom) ≫ f = g at hb
  rw [Preadditive.neg_comp, ha] at hb
  exact hne hb

private theorem natural_iso_sign_obstruction {C D : Type*} [Category C] [Category D]
    [Preadditive D] (F G : C ⥤ D) (a : F ≅ G) (K : C) {Z : D}
    (f : G.obj K ⟶ Z) (g : F.obj K ⟶ Z) (hne : -g ≠ g) :
    ¬ ∀ b : F ≅ G, b.hom.app K ≫ f = g := by
  intro h
  let b : F ≅ G :=
    { hom := -a.hom
      inv := -a.inv
      hom_inv_id := by simp
      inv_hom_id := by simp }
  have ha := h a
  have hb := h b
  change (-a.hom.app K) ≫ f = g at hb
  rw [Preadditive.neg_comp, ha] at hb
  exact hne hb

private theorem sign_obstruction_over_integers :
    ¬ ∀ b : ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ ℤ,
      b.hom ≫ 𝟙 (ModuleCat.of ℤ ℤ) = 𝟙 (ModuleCat.of ℤ ℤ) := by
  apply sign_obstruction (Iso.refl _) (𝟙 _) (𝟙 _)
  intro h
  have hh := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ ↦ f (1 : ℤ)) h
  norm_num at hh

-- STATEMENT-DISPUTED: `a` is arbitrary; composing it with minus identity preserves
-- its isomorphism type and reverses the left side, with the right side unchanged.
-- For identity ring equivalences over ℤ and K = ℤ[0], the canonical counit is
-- invertible, and degree-zero cohomology distinguishes identity from minus identity.
-- Only the canonical counit-compatible transport isomorphism satisfies this equation.

/-- Counit compatibility for a chosen transported derived-functor isomorphism.
Source: Stacks Project, Tag 06Y6.
The proof is the naturality calculation for the transported counits; it is deferred.
(blueprint: lem-pc-derived-extension-ring-equiv-raw-counit-equation). -/
theorem raw_transport_counit_equation
    {R₀ B₀ R B : Type u}
    [CommRing R₀] [CommRing B₀] [CommRing R] [CommRing B]
    [Algebra R₀ B₀] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (L₀ : DerivedCategory (ModuleCat.{u} R₀) ⥤ DerivedCategory (ModuleCat.{u} B₀))
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶
      (extendScalars (algebraMap R₀ B₀)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h₀ : L₀.IsLeftDerivedFunctor ε₀ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (eR : R₀ ≃+* R) (eB : B₀ ≃+* B)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom) :
    ∀ (E : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B₀))
      (q : (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ E ≅
        (restrictScalars.{u} eB.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
          (HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh))
      (t : (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
        (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ) ≅
        (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ) ⋙
          (restrictScalars.{u} eB.toRingHom).mapHomologicalComplex (.up ℤ))
      (a : (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
        HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L₀ ≅
        HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L ⋙ E),
      ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
          a.hom.app K ≫ E.map (ε.app
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj K)) ≫
            q.hom.app (((extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj K) =
          ε₀.app ((HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ)).obj
            (((restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ)).obj K)) ≫
            ((HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh).map
              (t.hom.app K))  := by sorry
end ModuleCat
