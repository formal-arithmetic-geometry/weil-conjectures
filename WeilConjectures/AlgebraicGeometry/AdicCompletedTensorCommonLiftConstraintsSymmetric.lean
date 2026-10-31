/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletedTensorCommonLiftTensorUnit
public import WeilConjectures.AlgebraicGeometry.AdicCompletedTensorCommonComponent
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Symmetry equation for the common-stage completed tensor lift.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-symmetric).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
/- A natural invertible binary comparison need not preserve symmetry. -/
namespace TensoratorSymmetryNormalizationTest
private structure Line where
  degree : ℤ
private structure Hom (A B : Line) where
  degree_eq : A.degree = B.degree
  scalar : ℚ
private theorem hom_ext {A B : Line} (f g : Hom A B) (h : f.scalar = g.scalar) : f = g := by
  cases f
  cases g
  cases h
  rfl
private instance lineCategory : Category Line where
  Hom := Hom
  id _ := ⟨rfl, 1⟩
  comp f g := ⟨f.degree_eq.trans g.degree_eq, f.scalar * g.scalar⟩
  id_comp f := hom_ext _ _ (one_mul f.scalar)
  comp_id f := hom_ext _ _ (mul_one f.scalar)
  assoc f g h := hom_ext _ _ (mul_assoc f.scalar g.scalar h.scalar)
private def unitIso {A B : Line} (h : A.degree = B.degree) : A ≅ B where
  hom := ⟨h, 1⟩
  inv := ⟨h.symm, 1⟩
  hom_inv_id := hom_ext _ _ (one_mul 1)
  inv_hom_id := hom_ext _ _ (one_mul 1)
private instance lineMonoidal : MonoidalCategory Line where
  tensorObj A B := ⟨A.degree + B.degree⟩
  tensorHom f g := ⟨congrArg₂ (· + ·) f.degree_eq g.degree_eq, f.scalar * g.scalar⟩
  whiskerLeft A _ _ f := ⟨congrArg (A.degree + ·) f.degree_eq, f.scalar⟩
  whiskerRight f B := ⟨congrArg (· + B.degree) f.degree_eq, f.scalar⟩
  tensorUnit := ⟨0⟩
  associator A B C := unitIso (add_assoc A.degree B.degree C.degree)
  leftUnitor A := unitIso (zero_add A.degree)
  rightUnitor A := unitIso (add_zero A.degree)
  tensorHom_def _ _ := hom_ext _ _ rfl
  id_tensorHom_id _ _ := hom_ext _ _ (one_mul 1)
  tensorHom_comp_tensorHom f g h k := by
    apply hom_ext
    change (f.scalar * g.scalar) * (h.scalar * k.scalar) =
      (f.scalar * h.scalar) * (g.scalar * k.scalar)
    ring
  whiskerLeft_id _ _ := hom_ext _ _ rfl
  id_whiskerRight _ _ := hom_ext _ _ rfl
  associator_naturality f g h := by
    apply hom_ext
    change (f.scalar * g.scalar) * h.scalar * 1 = 1 * (f.scalar * (g.scalar * h.scalar))
    simp only [mul_one, one_mul, mul_assoc]
  leftUnitor_naturality f := hom_ext _ _ (mul_one f.scalar |>.trans (one_mul f.scalar).symm)
  rightUnitor_naturality f := hom_ext _ _ (mul_one f.scalar |>.trans (one_mul f.scalar).symm)
  pentagon _ _ _ _ := hom_ext _ _ (show (1 : ℚ) * (1 * 1) = 1 * 1 by norm_num)
  triangle _ _ := hom_ext _ _ (show (1 : ℚ) * 1 = 1 from one_mul 1)
private instance lineSymmetric : SymmetricCategory Line where
  braiding A B := unitIso (add_comm A.degree B.degree)
  braiding_naturality_right _ _ _ f :=
    hom_ext _ _ ((mul_one f.scalar).trans (one_mul f.scalar).symm)
  braiding_naturality_left f _ :=
    hom_ext _ _ ((mul_one f.scalar).trans (one_mul f.scalar).symm)
  hexagon_forward _ _ _ := hom_ext _ _
    (show (1 : ℚ) * (1 * 1) = 1 * (1 * 1) from rfl)
  hexagon_reverse _ _ _ := hom_ext _ _
    (show (1 : ℚ) * (1 * 1) = 1 * (1 * 1) from rfl)
  symmetry _ _ := hom_ext _ _ (show (1 : ℚ) * 1 = 1 from one_mul 1)
private def sign (P : Line × Line) : ℚ :=
  if P.1.degree = 1 ∧ P.2.degree = 0 then -1 else 1
private theorem sign_sq (P : Line × Line) : sign P * sign P = 1 := by
  unfold sign
  split <;> norm_num
private def tensorator : MonoidalCategory.tensor Line ≅ MonoidalCategory.tensor Line :=
  NatIso.ofComponents
    (fun P ↦ { hom := ⟨rfl, sign P⟩
               inv := ⟨rfl, sign P⟩
               hom_inv_id := hom_ext _ _ (sign_sq P)
               inv_hom_id := hom_ext _ _ (sign_sq P) })
    (by
      intro P Q f
      apply hom_ext
      change (f.1.scalar * f.2.scalar) * sign Q = sign P * (f.1.scalar * f.2.scalar)
      have hs : sign P = sign Q := by
        unfold sign
        rw [f.1.degree_eq, f.2.degree_eq]
      rw [hs, mul_comm])
/-- At degrees (1,0) the two symmetry paths have scalars -1 and 1.
This is a counterexample to the generic inference from naturality and invertibility,
not an instantiation of the entire scheme/realization context. -/
private theorem tensorator_not_symmetric :
    ¬ ∀ A B : Line,
      tensorator.hom.app (A, B) ≫ (β_ A B).hom =
        (β_ A B).hom ≫ tensorator.hom.app (B, A) := by
  intro h
  have hs := congrArg Hom.scalar (h ⟨1⟩ ⟨0⟩)
  change sign (⟨1⟩, ⟨0⟩) * 1 = 1 * sign (⟨0⟩, ⟨1⟩) at hs
  norm_num [sign] at hs
end TensoratorSymmetryNormalizationTest

namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)
  (symmetry : @SymmetricCategory _ _ closed.monoidal)

/-- Twisting the tensorator by an asymmetric natural automorphism preserves its
record type. Universal symmetry would force that automorphism to commute with the
native braiding. The explicit inequality is a hypothesis: no nonzero-object or
native automorphism existence assertion is hidden in this diagnostic. -/
private theorem symmetry_universal_obstruction
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry)
    (σ : ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
      ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor)
    (A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
    (hσ : σ.hom.app (A, B) ≫
        (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≠
      (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
        σ.hom.app (B, A)) :
    ¬ ∀ d : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry,
      d.tensor.hom.app (A, B) ≫
          (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
        (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
          d.tensor.hom.app (B, A) := by
  intro h
  let d : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry :=
    { data with tensor := σ ≪≫ data.tensor }
  have hp := h data
  have ht := h d
  change (σ.hom.app (A, B) ≫ data.tensor.hom.app (A, B)) ≫
      (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
    (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
      (σ.hom.app (B, A) ≫ data.tensor.hom.app (B, A)) at ht
  rw [Category.assoc, hp] at ht
  apply hσ
  apply (cancel_mono (data.tensor.hom.app (B, A))).1
  simpa only [Category.assoc] using ht

/- STATEMENT-DISPUTED (repaired): the former statement quantified over an arbitrary
natural tensor isomorphism. Naturality does not imply symmetry: the private graded-line
example above is a counterexample to that inference. The explicit component equation
below restricts the law to the constructed comparison, and its existing constructor
supplies this equation without assuming a coherence law. -/
/-- The symmetry component for the explicitly normalized common-stage tensorator.
Source: BS Remark 6.8.15; HRS Lemma 7.9.

Proof plan: replace the two tensorator components by their normalization equations.
Choose one finite field containing both input stages and express both components at
that field, using the component stage-transport equation. On integral good K-flat
representatives expand N.representative and N.balance_sections. Both paths send
s tensor (x tensor y) to the tensor of 1 tensor y and s tensor x, with the same
Koszul factor (-1)^(pq); the balancing relation moves the scalar between factors.
The native symmetry_model identifies this signed swap with the target braiding.
Use the normalized completion augmentation and coherent-reduction tensor comparison
to identify the source integral braiding with the same swap. Pass through the good
complex localization, rational localization and the prescribed common-stage braiding
representative. Cancel the endpoint isoToStage maps using naturality of the source
and target braidings. This yields the stated equality for the normalized components.
Zero objects, coincident fields and empty schemes use these same equations; no
nonzero coefficient object or choice-independent arbitrary tensorator is assumed.
The source coherent-reduction identification remains part of this named obligation.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-symmetric). -/
theorem completed_tensor_common_lift_constraints_symmetric
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry)
    (normalized : ∀ A B, data.tensor.hom.app (A, B) =
      (completedTensorCommonComponent l X R closed models N A B).hom) :
    ∀ A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      data.tensor.hom.app (A, B) ≫
          (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
        (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
          data.tensor.hom.app (B, A) := by
  sorry

end WeilConjectures.AdicQbarRealization
