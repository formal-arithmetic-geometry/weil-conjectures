/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-! # Module geometric stalks compute and detect unbounded cohomology

Constant-coefficient modules use the project's module-valued sheaf encoding.
`pointSmallEtale t |>.sheafFiber` is the pointed-neighbourhood colimit, computed
in modules, so its scalar action and maps are the induced A-linear ones.
The derived functor below is the existing exact-functor localization, on the full
unbounded derived categories. All comparisons are natural isomorphisms.

## References

* Stacks Project, Tags 03PT, 03PU, 03DA, 04EQ, 0DJJ and 015F
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] CategoryTheory.GrothendieckTopology.Point.sheafFiber_additive

namespace AlgebraicGeometry.Etale

/-- Vanishing of each cohomology sheaf is detected by all derived geometric stalks
(Stacks, Tags 03PU and 0DJJ). -/
theorem etaleModuleStalk_cohomology_test
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (E : DerivedCategoryModule A T) (i : ℤ) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj E) ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).obj
          (((pointSmallEtale t).sheafFiber
            (A := ModuleCat.{u + 1} A)).mapDerivedCategory.obj E)) := by
  constructor
  · intro h Ω _ _ t
    let e := ((pointSmallEtale t).sheafFiber
      (A := ModuleCat.{u + 1} A)).mapDerivedCategoryHomologyFunctorIso i
    exact (Functor.map_isZero ((pointSmallEtale t).sheafFiber) h).of_iso (e.app E).symm
  · intro h
    apply (IsZero.iff_id_eq_zero _).2
    apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro s
    let e := ((pointSmallEtale (T.algClosurePoint s)).sheafFiber
      (A := ModuleCat.{u + 1} A)).mapDerivedCategoryHomologyFunctorIso i
    have hz := (h _ (T.algClosurePoint s)).of_iso (e.app E)
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 hz

end AlgebraicGeometry.Etale
