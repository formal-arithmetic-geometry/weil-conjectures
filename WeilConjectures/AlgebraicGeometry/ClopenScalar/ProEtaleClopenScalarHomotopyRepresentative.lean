/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData

/-! # The homotopy form of the scalar representative square

Source: Stacks Project, sites-cohomology.tex, Tag 06YY.
(blueprint: lem-pur-clopen-scalar-homotopy-representative)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors HasDerivedCategory.standard DerivedCategory.Qh
  DerivedCategory.quotientCompQhIso Functor.mapDerivedCategoryFactorsh
  Functor.mapHomotopyCategoryFactors SheafOfModules.monoidalCategory
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar

section QuotientFormulas

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
private theorem homotopyFactors_hom (F : A ⥤ B) [F.Additive]
    (P : CochainComplex A ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := by
  unfold Functor.mapHomotopyCategoryFactors
  rfl

omit [HasDerivedCategory A] [HasDerivedCategory B] in
private theorem homotopyFactors_inv (F : A ⥤ B) [F.Additive]
    (P : CochainComplex A ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := by
  unfold Functor.mapHomotopyCategoryFactors
  rfl

private theorem factorsh_quotient (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app P) ≫
        F.mapDerivedCategoryFactors.hom.app P ≫
        (DerivedCategory.quotientCompQhIso B).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [F.mapDerivedCategoryFactorsh_hom_app, homotopyFactors_inv]
  dsimp only [Functor.comp_obj, Functor.mapHomotopyCategory_obj,
    HomotopyCategory.quotient_obj_as]
  rw [DerivedCategory.Qh.map_id, Category.comp_id]

end QuotientFormulas

private theorem computation_eq {X : Scheme.{t}}
    {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} {a : R ⟶ S}
    (p : Presentation.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)} a)
    (P : CochainComplex (Mods.{t, u} R) ℤ) :
    ClopenScalar.computation p P =
      p.derived.map ((DerivedCategory.quotientCompQhIso (Mods R)).inv.app P) ≫
        p.counit.app ((HomotopyCategory.quotient _ _).obj P) ≫
        (DerivedCategory.quotientCompQhIso (Mods S)).hom.app
          ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [ClopenScalar.computation, homotopyFactors_hom]
  dsimp only [Functor.comp_obj, Functor.mapHomotopyCategory_obj,
    HomotopyCategory.quotient_obj_as]
  rw [DerivedCategory.Qh.map_id, Category.id_comp]

attribute [local irreducible] computation

set_option maxHeartbeats 800000 in
-- The quotient square has several dependent localization and coefficient functor types.
/-- Translate the cochain representative square to the canonical homotopy quotient square.
Source: Stacks Project, sites-cohomology.tex, Tag 06YY
(blueprint: lem-pur-clopen-scalar-homotopy-representative).

Proof: the degree formula identifies the chain comparison with the degreewise ordinary
comparison. Expand the quotient factorization isomorphisms and the computation counits.
Precompose by the derived image of the inverse quotient comparison and postcompose by
the target quotient comparison. Naturality identifies the resulting equation with the
cochain representative square. Both added maps are isomorphisms, so cancellation gives
the homotopy square. This argument uses no additional flatness or nonzero assumptions. -/
theorem clopen_scalar_homotopy_representative
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (p : Presentations.{t, u} X) (q : Presentations.{t, u} Y)
    (d : Comparison.{t, u} j p q) (hd : d.degree) (hr : d.representative)
    {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
        (P : CochainComplex (Mods.{t, u} R) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P)
        (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := topology X) (R := R) (P.X n)) :
        (resD.{t, u} j S).map
            ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          (res.{t, u} j S).mapDerivedCategoryFactorsh.hom.app
            (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj P)) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (d.ordinary a) (.up ℤ) ≪≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm).hom.app
              ((HomotopyCategory.quotient _ _).obj P)) =
        (d.derived a).hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
          (q ((rings.{t, u} j).map a)).derived.map
            ((res.{t, u} j R).mapDerivedCategoryFactorsh.hom.app
              ((HomotopyCategory.quotient _ _).obj P)) ≫
          (q ((rings.{t, u} j).map a)).counit.app
            (((res.{t, u} j R).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj P)) := by
  have h := hr a P hP hf
  have hchain : d.chain a =
      NatIso.mapHomologicalComplex (d.ordinary a) (.up ℤ) := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply HomologicalComplex.Hom.ext
    funext n
    exact hd a K n
  have hh : (Functor.mapHomotopyCategoryCompIso (d.ordinary a) (.up ℤ) ≪≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm).hom.app
      ((HomotopyCategory.quotient _ _).obj P) =
      (HomotopyCategory.quotient _ _).map ((d.chain a).hom.app P) := by
    rw [hchain]
    rfl
  rw [hh]
  erw [factorsh_quotient (res j S)
    (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P),
    factorsh_quotient (res j R) P]
  apply (cancel_epi ((resD j S).map ((p a).derived.map
    ((DerivedCategory.quotientCompQhIso (Mods R)).inv.app P)))).1
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso
    (Mods ((rings j).obj S))).hom.app
      (((q ((rings j).map a)).ordinary.mapHomologicalComplex (.up ℤ)).obj
        (((res j R).mapHomologicalComplex (.up ℤ)).obj P)))).1
  have hn := (d.derived a).hom.naturality
    ((DerivedCategory.quotientCompQhIso (Mods R)).inv.app P)
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  erw [DerivedCategory.quotientCompQhIso_hom_naturality ((d.chain a).hom.app P)]
  erw [Iso.inv_hom_id_app_assoc]
  have hcancel := ((q ((rings j).map a)).derived.mapIso
    ((resD j R).mapIso ((DerivedCategory.quotientCompQhIso (Mods R)).app P))).inv_hom_id
  erw [reassoc_of% hcancel]
  simp only [computation_eq, Functor.map_comp, Category.assoc] at h
  exact h.symm

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
