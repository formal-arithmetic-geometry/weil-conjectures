/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOfFiniteStalks
import WeilConjectures.AlgebraicGeometry.ConstructibleUnderlyingSetsOfFiniteStalks
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets

/-!
# Finite direct image of constructible module sheaves with finite stalks

## References

* Stacks Project, Tag 095R.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Finite direct image preserves constructibility for module sheaves with finite stalks. -/
theorem isConstructibleSheaf_lowerStar_of_finite_stalks
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsFinite f]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf F)
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite ((((pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F)) :
    IsConstructibleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType f
  let I : Ideal Λ := ⨅ U : Y.Etaleᵒᵖ, Module.annihilator Λ (F.obj.obj U)
  have hI : Finite (Λ ⧸ I) :=
    finite_quotient_section_annihilator_of_finite_stalks Λ F hF hfin
  have hsets := isConstructibleEtaleSheafOfSets_of_finite_module_stalks Λ F hF hfin
  let E := (sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  have hpush := isConstructibleEtaleSheafOfSets_lowerStar_of_isNoetherian f E hsets
  refine isConstructibleSheaf_of_finite_coefficient_underlying_sets Λ _ ?_ I hI ?_
  · exact hpush
  · intro U r hr m
    exact Module.mem_annihilator.mp
      (Ideal.mem_iInf.mp hr ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj U)) m

end AlgebraicGeometry.Scheme
