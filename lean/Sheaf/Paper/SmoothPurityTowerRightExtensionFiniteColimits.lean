/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z5
-/
module

public import Sheaf.Paper.SmoothPurityTowerRightExtension
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
/-!
# Finite colimits of the normalized right extensions

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-levels,
`sk-lem-sp-tower-levels-adjoint.proof.md`
(blueprint: lem-sp-tower-right-extension-finite-colimits).

Index n represents the positive coefficient exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

-- Elaborate with the existing transport to the full coefficient universe.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

private theorem strict_hom_ext
    {M N : StrictRingSystem.{t + 1, t, max u (t + 1)}
      (spCoefficientCommRings l E T)} (f g : M ⟶ N)
    (h : ∀ r : ℕ, f.app r = g.app r) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have he : f = g := funext h
      subst g
      rfl

private theorem strict_evaluations_conservative :
    JointlyReflectIsomorphisms
      (systemEvaluation.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T)) := by
  constructor
  intro M N f hf
  let (r : ℕ) : IsIso (f.app r) := hf r
  let g : N ⟶ M :=
    { app := fun r ↦ inv (f.app r)
      comm := fun {m r} h ↦ by
        apply (cancel_epi (f.app r)).mp
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm h]
        rw [Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id]
        rw [CategoryTheory.Functor.map_id, Category.comp_id] }
  refine ⟨g, ?_, ?_⟩
  · apply strict_hom_ext l E T
    intro r
    exact IsIso.hom_inv_id (f.app r)
  · apply strict_hom_ext l E T
    intro r
    exact IsIso.inv_hom_id (f.app r)

private theorem right_extension_level_colimits (A : SpCoefficientTowersAbelian l E T)
    (R : SpTowerRightAdjoints l E T A) (n r : ℕ) :
    PreservesFiniteColimits
      (R.right n ⋙ systemEvaluation (spCoefficientCommRings l E T) r) := by
  classical
  by_cases h : n ≤ r
  · have he : R.right n ⋙ systemEvaluation (spCoefficientCommRings l E T) r =
        systemRestriction (spCoefficientCommRings l E T) h :=
      Functor.hext (fun X ↦ R.above n r h X) (fun X Y f ↦ R.mapAbove n r h f)
    rw [he]
    exact systemScalarRestrictionColimits
      ((spCoefficientCommRings l E T).map (homOfLE h).op)
  · let F := R.right n ⋙ systemEvaluation (spCoefficientCommRings l E T) r
    have hz : IsZero F := F.isZero (fun X ↦ R.below n r (Nat.lt_of_not_ge h) X)
    exact ⟨fun I _ _ ↦ F.preservesColimitsOfShape_of_isZero hz I⟩

/-- The prescribed right extensions preserve finite colimits.
Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-levels,
`sk-lem-sp-tower-levels-adjoint.proof.md`, Exactness
(blueprint: lem-sp-tower-right-extension-finite-colimits).

Proof: the coefficient-tower abelian construction computes cokernels and finite
biproducts levelwise. At level r >= n the extension is scalar restriction along
the quotient map. Scalar restriction leaves the underlying abelian sheaf and
maps unchanged, so it preserves finite biproducts and cokernels: the latter are
the sheafifications of the same sectionwise cokernels. This is also the exact
scalar-restriction lemma in SystemLevelLeftExtension. At r < n the extension is
the zero functor, which preserves these colimits. The specified action on maps
identifies the induced cocones with these levelwise cocones. Their universal
maps commute with transitions by uniqueness, so they assemble to the cokernel
and finite-biproduct universal maps in strict systems. Transport through the
given equivalence preserves these universal properties. An additive functor
between abelian categories preserving finite biproducts and cokernels preserves
finite colimits, proving the claim. At n=0 only the scalar-restriction case occurs.
-/
theorem sp_tower_right_extension_finite_colimits (A : SpCoefficientTowersAbelian l E T)
    (R : SpTowerRightAdjoints l E T A) (n : ℕ) :
    PreservesFiniteColimits (R.right n ⋙ A.equivalence.inverse) := by
  let : PreservesFiniteColimits (R.right n) := by
    constructor
    intro I _ _
    constructor
    intro D
    constructor
    intro c hc
    refine ⟨(strict_evaluations_conservative l E T).jointlyReflectsColimit ?_⟩
    intro r
    let := right_extension_level_colimits l E T A R n r
    exact isColimitOfPreserves
      (R.right n ⋙ systemEvaluation (spCoefficientCommRings l E T) r) hc
  infer_instance

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
