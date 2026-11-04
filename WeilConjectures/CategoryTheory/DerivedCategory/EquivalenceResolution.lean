/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Transporting resolutions along an equivalence of abelian categories

If `e : A ≌ B` is an additive equivalence of abelian categories and `s : K' ⟶ e(G)` is a
quasi-isomorphism of cochain complexes in `B`, then the complex `e⁻¹(K')` represents `G` in the
derived category of `A` and is sent by `e` to a complex isomorphic to `K'`.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Equivalence

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive]

/-- The image of a complex under `e⁻¹ ⋙ e` is isomorphic to the complex. -/
def mapHomologicalComplexCounitIso (K : CochainComplex B ℤ) :
    (e.functor.mapHomologicalComplex (.up ℤ)).obj
      ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ e.counitIso.app (K.X n))
    (fun _ _ _ ↦ (e.counitIso.hom.naturality _).symm)

/-- A quasi-isomorphism into `e(G)` gives a representative of `G` after applying `e⁻¹`. -/
lemma nonempty_Q_obj_inverse_iso (G : CochainComplex A ℤ) {K : CochainComplex B ℤ}
    (s : K ⟶ (e.functor.mapHomologicalComplex (.up ℤ)).obj G) [QuasiIso s] :
    Nonempty (DerivedCategory.Q.obj ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K) ≅
      DerivedCategory.Q.obj G) := by
  have : QuasiIso ((e.inverse.mapHomologicalComplex (.up ℤ)).map s) := inferInstance
  have : IsIso (DerivedCategory.Q.map ((e.inverse.mapHomologicalComplex (.up ℤ)).map s)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  refine ⟨asIso (DerivedCategory.Q.map ((e.inverse.mapHomologicalComplex (.up ℤ)).map s)) ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (e.unitIso.app (G.X n)).symm) (fun _ _ _ ↦ ?_))⟩
  exact (e.unitIso.inv.naturality _).symm

end CategoryTheory.Equivalence
