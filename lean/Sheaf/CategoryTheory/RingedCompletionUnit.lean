/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.RingedExtendedCech
public import Sheaf.CategoryTheory.RingedDerivedRestriction
public import Sheaf.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import Sheaf.Algebra.Homology.HomComplexUnitEvaluationComm

/-!
# The canonical internal-Hom completion unit

Source: Stacks Project, algebraization.tex, Tag 099F, and sites-cohomology.tex, Section 08J7
(blueprint: def-weil-pbc-ringed-completion-unit).

The unit uses evaluation at one, the functorial K-injective resolution, and the specified
localization factorization of derived internal Hom. No arbitrary isomorphism from Hom of
the ring sheaf is chosen.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- Evaluation at one gives the canonical chain isomorphism from Hom of the ring complex.
Source: Stacks Project, sites-cohomology.tex, Section 08J7
(blueprint: def-weil-pbc-ringed-completion-unit). -/
def ringedHomUnitEvaluationIso (M : ringedSiteComplex O) :
    homComplex (R := O) (ringedSiteRingComplex O) M ≅ M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ @asIso _ _ _ _ (homComplexUnitEvaluation J O M n)
      (homComplex_unit_evaluation_isIso J O M n))
    (fun n m h ↦ homComplex_unit_evaluation_comm J O M n m h)

/-- The canonical map `E → RHom(O[0], E)`, obtained by evaluation at one and the
localization factorization of the actual internal-Hom construction.
Source: Stacks Project, algebraization.tex, Tag 099F, and sites-cohomology.tex, Section 08J7
(blueprint: def-weil-pbc-ringed-completion-unit). -/
def ringedDerivedHomUnit (E : ringedSiteDerived O) :
    E ⟶ (derivedInternalHom J O).obj
      (op (DerivedCategory.Q.obj (ringedSiteRingComplex O)), E) :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  let η := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  let c := Localization.fac
    ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := O)) ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts J O I η (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)
  let M := DerivedCategory.Q.objPreimage E
  let e := DerivedCategory.Q.objObjPreimageIso E
  e.inv ≫ DerivedCategory.Q.map (η.app M) ≫
    (DerivedCategory.Q.mapIso (ringedHomUnitEvaluationIso O (I.obj M))).inv ≫
      (c.app (op (ringedSiteRingComplex O), M)).inv ≫
        (derivedInternalHom J O).map (𝟙 _, e.hom)

/-- Internal Hom out of a fixed complex, as a functor of its second variable.
Source: Stacks Project, algebraization.tex, Tag 099F
(blueprint: def-weil-pbc-ringed-completion-unit). -/
def ringedCechCompletionFunctor (K : ringedSiteComplex O) :
    ringedSiteDerived O ⥤ ringedSiteDerived O :=
  (Functor.curry.obj (derivedInternalHom J O)).obj (op (DerivedCategory.Q.obj K))

/-- The canonical completion unit induced by the augmentation, contravariantly in the
first argument of derived internal Hom.
Source: Stacks Project, algebraization.tex, Tag 099F
(blueprint: def-weil-pbc-ringed-completion-unit). -/
def ringedCechCompletionUnit (K : ringedSiteComplex O)
    (ε : K ⟶ ringedSiteRingComplex O) (E : ringedSiteDerived O) :
    E ⟶ (ringedCechCompletionFunctor O K).obj E :=
  ringedDerivedHomUnit O E ≫
    (derivedInternalHom J O).map ((DerivedCategory.Q.map ε).op, 𝟙 E)

end CategoryTheory
