/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Affine evaluation of quasi-coherent module colimits

Source: Stacks Project, Schemes, Lemma 01ID and Section 26.24, item (4).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Evaluation on an affine open sends a quasi-coherent module colimit cocone to
an actual colimit cocone of modules. No filteredness is needed.
Source: Stacks Project, Schemes, Lemma 01ID and Lemma 01I7
(blueprint: lem-weil-pbc-quasi-coherent-module-colimit-evaluation).

Proof: Put R = Γ(X, U) and restrict the diagram and cocone along the open immersion
Spec R → X furnished by the affine open U. Restriction preserves colimits since it
is left adjoint to pushforward, and preserves quasi-coherence. The tilde-Gamma counit
identifies every restricted stage with the tilde of its global sections, naturally in
stage maps. The assumption that c.pt is quasi-coherent also lets one compute the
affine colimit in the full subcategory of quasi-coherent modules using tildeEquiv.
Form the colimit M of the section modules. The tilde functor is a left
adjoint, so tilde M is the colimit of the tilde stage modules. Uniqueness of colimits
gives an isomorphism tilde M ≅ c.pt restricted to Spec R, intertwining the legs.
Taking global sections and composing with the tilde-Gamma unit (an isomorphism)
gives M ≅ Γ(c.pt, U). Naturality of the unit and the triangle identity show that the
transported legs are precisely the original evaluated c.ι. Transport the module
colimit along this isomorphism. This works also for an empty indexing category,
where M is zero, and for the empty affine open, where every module is zero. -/
theorem quasiCoherentModuleColimitEvaluation
    (X : Scheme.{u}) (I : Type u) [Category.{u} I]
    (F : I ⥤ X.Modules) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i : I, (F.obj i).IsQuasicoherent) (hq : c.pt.IsQuasicoherent)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Nonempty (IsColimit
      ((SheafOfModules.evaluation (R := X.ringCatSheaf) (Opposite.op U)).mapCocone c)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
