/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
import WeilConjectures.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality

/-!
# Comparing tensor-pullback sections with the presheaf of module homomorphisms

## References

* Stacks Project, Tags 03DT and 03DR
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false


private theorem evaluation_bijective {X : Scheme.{u}} (F : X.Modules) (U : X.Etale) :
    Function.Bijective (etaleTensorHomEvaluation F U) := by
  constructor
  · intro φ ψ h
    have h' : (pullbackObjUnitIso U.hom).inv ≫ φ ≫
        (tensorSectionsPullbackComparison U.hom).inv.app F =
        (pullbackObjUnitIso U.hom).inv ≫ ψ ≫ (tensorSectionsPullbackComparison U.hom).inv.app F :=
      unit_hom_ext h
    simpa using h'
  · intro s
    refine ⟨(pullbackObjUnitIso U.hom).hom ≫
      homOfGlobalSection ((tensorPullback U.hom).obj F) s ≫
      (tensorSectionsPullbackComparison U.hom).hom.app F, ?_⟩
    dsimp only [etaleTensorHomEvaluation]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      Iso.inv_hom_id_assoc]
    rw [homOfGlobalSection_app_one, presheaf_map_id_apply]

/-- Sections of tensor pullbacks and homomorphisms from the pulled-back structure sheaf
are naturally isomorphic as presheaves of sets (Stacks, Tags 03DT, 03DR). -/
theorem nonempty_etaleTensorSectionsHomIso {X : Scheme.{u}} (F : X.Modules) :
    Nonempty ((etaleTensorSectionsPresheaf F ⋙ CategoryTheory.forget AddCommGrpCat) ≅
      etaleHom (unitObj X) F) := by
  classical
  let e : etaleHom (unitObj X) F ≅
      etaleTensorSectionsPresheaf F ⋙ CategoryTheory.forget AddCommGrpCat :=
    NatIso.ofComponents
      (fun U ↦ (Equiv.ofBijective (etaleTensorHomEvaluation F U.unop)
        (evaluation_bijective F U.unop)).toIso)
      (fun g ↦ etaleTensorHomEvaluation_naturality F g)
  exact ⟨e.symm⟩

end AlgebraicGeometry.Scheme.Modules
