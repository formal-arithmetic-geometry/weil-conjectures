/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Presentation of derived open-extension mates on complexes

Source: Stacks Project, Tags 08BT and 08BW.
-/

@[expose] public section

universe w vA vB vC uA uB uC

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory.Adjunction

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  {L : B ⥤ A} {R : A ⥤ B} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- Localize the termwise adjunction of exact functors. -/
def onDerivedCategory (adj : L ⊣ R) : L.mapDerivedCategory ⊣ R.mapDerivedCategory := by
  letI : CatCommSq (L.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q L.mapDerivedCategory :=
    ⟨L.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (R.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q R.mapDerivedCategory :=
    ⟨R.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

/-- Compare a chosen left adjoint with the termwise model on a representative complex. -/
def derivedPresentation (adj : L ⊣ R)
    {LD : DerivedCategory B ⥤ DerivedCategory A} (d : LD ⊣ R.mapDerivedCategory)
    (K : CochainComplex A ℤ) {E : DerivedCategory A} (e : DerivedCategory.Q.obj K ≅ E) :
    LD.obj (R.mapDerivedCategory.obj E) ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  (d.leftAdjointUniq adj.onDerivedCategory).app _ ≪≫
    L.mapDerivedCategory.mapIso
      (R.mapDerivedCategory.mapIso e.symm ≪≫ R.mapDerivedCategoryFactors.app K) ≪≫
    L.mapDerivedCategoryFactors.app _

/-- The presentation carries the chosen counit to the termwise counit. -/
theorem derivedPresentation_counit (adj : L ⊣ R)
    {LD : DerivedCategory B ⥤ DerivedCategory A} (d : LD ⊣ R.mapDerivedCategory)
    (K : CochainComplex A ℤ) {E : DerivedCategory A} (e : DerivedCategory.Q.obj K ≅ E) :
    (adj.derivedPresentation d K e).hom ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K) ≫
        e.hom = d.counit.app E := by
  have hc : adj.onDerivedCategory.counit.app (DerivedCategory.Q.obj K) =
      L.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K) := by
    simp only [onDerivedCategory, localization_counit_app]
    rfl
  dsimp only [derivedPresentation, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  have hn := adj.onDerivedCategory.counit.naturality e.inv
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← reassoc_of% hc, reassoc_of% hn]
  simp

/-- Exact localization carries a nested adjunction mate to its derived mate.

Source: Stacks Project, Tags 08BT and 08BW; compatibility with localization of the
unit and counit (Mathlib `Adjunction.localization_unit_app` and
`Adjunction.localization_counit_app`).
(blueprint: lem-sc-localization-nested-adjunction-mate).

Proof: Use the adjunction induced termwise on complexes, whose unit and counit in
each degree are those of the original adjunction. The degreewise hypothesis is
therefore equality of complex morphisms, by extensionality. Localize that equality.
Expand the localized unit and counit on Q K using the localization formulas. The
factorization isomorphisms for composition and for the comparison c identify the
localized comparison with cD. Cancel inverse factorization isomorphisms to obtain
the assertion for the localized adjunctions and E = Q K. Naturality transports this
identity along e. Finally the unique isomorphisms from the chosen derived left
adjoints to the localized ones carry their units and counits to each other; the
unit and counit identities for `leftAdjointUniq` give the displayed formula for
arbitrary d1 and d2. This is an equality for a single nested restriction: no cover,
short exact sequence, or distinguished triangle is assumed or asserted. -/
theorem derivedPresentation_mate
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]
    {L2 : C ⥤ A} {R2 : A ⥤ C} {T : B ⥤ C}
    [L2.Additive] [R2.Additive] [T.Additive]
    [PreservesFiniteLimits L2] [PreservesFiniteColimits L2]
    [PreservesFiniteLimits R2] [PreservesFiniteColimits R2]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a1 : L ⊣ R) (a2 : L2 ⊣ R2) (c : R ⋙ T ≅ R2)
    {LD1 : DerivedCategory B ⥤ DerivedCategory A}
    {LD2 : DerivedCategory C ⥤ DerivedCategory A}
    (d1 : LD1 ⊣ R.mapDerivedCategory) (d2 : LD2 ⊣ R2.mapDerivedCategory)
    (K : CochainComplex A ℤ) {E : DerivedCategory A} (e : DerivedCategory.Q.obj K ≅ E)
    (f : (L2.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((R2.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hf : ∀ n, f.f n = (a2.homEquiv _ _).symm
      (c.inv.app (K.X n) ≫ T.map (a1.unit.app (R.obj (K.X n))) ≫
        c.hom.app (L.obj (R.obj (K.X n))))) :
    letI : PreservesFiniteLimits (R ⋙ T) := comp_preservesFiniteLimits R T
    letI : PreservesFiniteColimits (R ⋙ T) := comp_preservesFiniteColimits R T
    let cD := (Functor.mapDerivedCategoryCompIso R T).symm ≪≫
      Functor.mapDerivedCategoryNatIso c
    let κ := (d2.homEquiv _ _).symm
      (cD.inv.app E ≫ T.mapDerivedCategory.map
        (d1.unit.app (R.mapDerivedCategory.obj E)) ≫
        cD.hom.app (LD1.obj (R.mapDerivedCategory.obj E)))
    (a2.derivedPresentation d2 K e).hom ≫ DerivedCategory.Q.map f =
      κ ≫ (a1.derivedPresentation d1 K e).hom := by sorry

end CategoryTheory.Adjunction

end
