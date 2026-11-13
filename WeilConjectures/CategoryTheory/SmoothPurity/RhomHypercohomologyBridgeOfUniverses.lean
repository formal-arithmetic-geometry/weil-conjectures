/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.CategoryTheory.Functor.Currying
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
import WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
import WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses

/-!
# Hypercohomology of the sheaf Hom complex and the homotopy category

Source: Stacks Project, Tags 0A8Z and 08JA.
(blueprint: lem-pur-hom-complex-hypercohomology)

This is the independent-universe comparison used by the global-sections theorem.  Its
proof applies zeroth homology to the recorded full derived-sections comparison and
composes with the ordinary global Hom-complex calculation.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory Opposite

namespace CategoryTheory

set_option profiler true in
set_option maxHeartbeats 800000 in
-- The comparison expands several derived-functor and full-subcategory composites.
set_option backward.isDefEq.respectTransparency false in
/-- Zeroth hypercohomology of the Hom complex is the homotopy-category Hom bifunctor.

Proof: lift the target functor I to the full subcategory of K-injective complexes.
The first two comparisons of derived_internalHom_sections_model identify derived
sections of the sheaf Hom complex with its ordinary sections complex after localization.
Apply zeroth derived homology and homologyFunctorFactors, then compose with the ordinary
global Hom-complex calculation. Whiskering retains naturality in both variables.
No K-flatness of the source is required; zero complexes and the empty site are included.

Source: Stacks Project, Equation 0A8Z and Lemma 08JA.
(blueprint: lem-pur-hom-complex-hypercohomology). -/
theorem rhom_hypercohomology_bridgeOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max c v r})
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (I : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hI : ∀ M, (I.obj M).IsKInjective) :
    Nonempty (((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        DerivedCategory.Q ⋙ ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R) ≅
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).op).prod
          (I ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ)) ⋙
        Functor.uncurry.obj preadditiveCoyoneda) := by
  classical
  let A := SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let := HasDerivedCategory.standard AddCommGrpCat.{max c v r}
  let Γ : A ⥤ AddCommGrpCat.{max c v r} := preadditiveCoyoneda.obj
    (op (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
  let P := (𝟭 (CochainComplex A ℤ)ᵒᵖ).prod
    (ObjectProperty.lift (DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R) I hI)
  obtain ⟨a⟩ := (DerivedInternalHomSectionsModel.derived_internalHom_sections_model.{c, v, r, w, _}
    (R := R)).1
  obtain ⟨b⟩ := (DerivedInternalHomSectionsModel.derived_internalHom_sections_model.{c, v, r, w, _}
    (R := R)).2.1
  let Hd := DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0
  let d := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight a.symm
      (DerivedInternalHomSectionsModel.derivedSections.{c, v, r, w, _} R) ≪≫ b) Hd
  let d' := Functor.isoWhiskerLeft P d
  obtain ⟨e⟩ := homComplex_global_homotopyOfUniverses.{c, v, r} J R
  let F := (𝟭 (CochainComplex A ℤ)ᵒᵖ).prod I ⋙
    Functor.uncurry.obj (homComplexFunctor (R := R))
  let z : F ⋙ DerivedCategory.Q ⋙
      ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R ≅
      F ⋙ Γ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v r} (ComplexShape.up ℤ) 0 :=
    d' ≪≫ Functor.isoWhiskerLeft
      (F ⋙ Γ.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v r} 0)
  exact ⟨z ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((𝟭 (CochainComplex A ℤ)ᵒᵖ).prod I) e⟩

end CategoryTheory
