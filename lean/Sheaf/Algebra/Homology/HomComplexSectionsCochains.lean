/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Sheaf.Algebra.Homology.HomComplex

/-!
# Degreewise sections of the sheaf Hom complex

Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(blueprint: lem-pur-hom-complex-sections-cochains)
-/

@[expose] public section

universe u v
open CategoryTheory Opposite
namespace CategoryTheory

/-- Product projections identify degreewise sections with all localized cochains.
Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(blueprint: lem-pur-hom-complex-sections-cochains)

Proof: the product cone specified by homComplex_exists remains a product after
forgetting module sheaves, evaluating at U, and forgetting to abelian groups.
Its factors are localized presheaf-module morphisms by the construction of
internal Hom. The fully faithful forgetful functor from localized module sheaves
to presheaf modules identifies each factor with localized sheaf-module morphisms.
A degree-n external cochain is exactly a family of these morphisms indexed by p,
with target degree p+n. The product universal property supplies the forward map
and inverse; the projection formulas prove both inverse laws. Each projection and
the inverse preserve addition, so this is an additive equivalence. Reindexing q
along p+n=q gives the displayed formula. No finite support or boundedness is
required. If either complex is zero every factor and the product are zero, and
for n=0 the same construction gives arbitrary degree-preserving families. -/
theorem homComplex_sections_cochains
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex
      (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero R₀ U
    let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let S := E.obj (homComplex (R := R) L I)
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    ∃ e : ∀ n : ℤ, S.X n ≃+
        CochainComplex.HomComplex.Cochain (res.obj L) (res.obj I) n,
      ∀ (n : ℤ) (x : S.X n) (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ),
        ((e n x).v p q hpq).val.app W =
          (((π L I n p q hpq).val.app (op U)) x).app W := by sorry

end CategoryTheory
