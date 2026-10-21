/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Sheaf.Paper.CondensedFpHomStage
import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Finite coefficient stages for homomorphisms of finitely presented internal modules

Source: archived `TwoColimit.lean`, finite-stage Hom descent.
(blueprint: lem-weil-pbc-condensed-coefficient-hom-stage).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Homomorphisms into the algebraic-closure extension descend to finite coefficients.

Source: archived `TwoColimit.lean`, finite-stage Hom descent.
(blueprint: lem-weil-pbc-condensed-coefficient-hom-stage).

Proof: restrict the coefficient diagram to fields containing E. The forgetful functor
from the under-category is final, and that category is filtered. Apply the coefficient
colimit theorem to the complex supported in degree zero at Q, then evaluate at zero.
The finite-presentation Hom factorization theorem gives the desired stage and map.
No finiteness condition on Q is needed. The argument also covers zero modules and
the empty scheme; a filtered category always supplies a stage.
-/
theorem condensed_coefficient_hom_stage
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (P Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E))
    (hP : Mod.IsFinitelyPresented (padicSubfieldRingObj Y ℓ E) P)
    (a : P ⟶ (Mod.comap (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj
      ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj Q)) :
    ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (hEF : E ≤ F)
      (b : P ⟶ (Mod.comap (padicSubfieldRingObjMap Y ℓ hEF)).obj
        ((Mod.extendScalars (padicSubfieldRingObjMap Y ℓ hEF)).obj Q)),
      b ≫ Mod.mixedScalarMap
        (padicSubfieldRingObjMap Y ℓ hEF) (padicSubfieldRingObjToPadicAlgCl Y ℓ E)
        (padicSubfieldRingObjMap Y ℓ hEF) (padicSubfieldRingObjToPadicAlgCl Y ℓ E)
        (padicSubfieldRingObjToPadicAlgCl Y ℓ F)
        (padicSubfieldRingObjMap_comp_toPadicAlgCl Y ℓ hEF)
        (padicSubfieldRingObjMap_comp_toPadicAlgCl Y ℓ hEF) Q = a := by
  let C := (HomologicalComplex.single _ (.up ℤ) 0).obj Q
  let I := AsSmall.{u + 1} (Under E)
  let H : I ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
    (AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E
  let : H.Final := by dsimp only [H]; infer_instance
  let he (i : I) : E ≤ H.obj i := leOfHom (ULift.down i).hom
  let : HasColimitsOfShape I
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E)) :=
    inferInstance
  let c := (HomologicalComplex.eval _ (.up ℤ) 0).mapCocone
    (coefficientComplexCocone Y ℓ (E := E) (F := E) C H he he)
  have hc : IsColimit c := isColimitOfPreserves _
    (Classical.choice (nonempty_isColimit_coefficientComplexCocone Y ℓ (E := E) (F := E) C H he he))
  obtain ⟨i, b, hb⟩ := condensed_fp_hom_stage (padicSubfieldRingObj Y ℓ E) c hc P hP a
  exact ⟨H.obj i, he i, b, hb⟩

end AlgebraicGeometry.ProEtale
