/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.SectionBoundaryExact
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The square-zero formula for the canonical boundary of a tensor power

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, and Cohomology, Lemma 0B8S.
(blueprint: lem-sc-square-zero-tensor-power-boundary).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u wC wD

/-- The boundary of a section power is the corresponding multiple of its acted-on
first obstruction. This is a formula for the canonical connecting map, with no lifting
assertion. The additive comparison `b` transports the coefficient module on the closed
subscheme back to the kernel of the degree `n * (e + 1)` unit sequence.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, equation (30.17.5.1),
and Cohomology, Lemma 0B8S.
(blueprint: lem-sc-square-zero-tensor-power-boundary).
Proof:
1. Tensor the ideal sequence by each invertible tensor power of L. Its kernel is
I tensor L^d and its quotient is the pushforward of j^*L^d. Compare this kernel
with the categorical kernel of the canonical adjunction unit. Since I^2=0, the
kernel is annihilated by I and is the pushforward of its pullback.
2. The closed-immersion cohomology edge identifies H^1 of each kernel with H^1
on Z. Tensor-pullback and tensor-power comparisons, including the degree-zero unit
comparison, give a and identify the pulled-back kernel in degree n(e+1) with
F tensor ((j^*L)^n)^e. Their inverse on cohomology gives the additive map b.
3. Define xi as the transported degree-n boundary of s. Sum the ideal sequences
in all nonnegative degrees. Local frames identify the summed algebra with a
polynomial algebra; multiplication is commutative and the summed kernel has square
zero. The canonical boundary is a derivation by Lemma 0B8S.
4. Induct on k: the Leibniz rule gives delta(s^(k+1)) = s delta(s^k) +
s^k delta(s) = (k+1) s^k delta(s). Include and project the graded summands to
identify this with the individual degree-n(k+1) connecting map. Naturality of the
cohomology edge identifies the action with the displayed H^1 map. The canonical
boundary is independent of resolution choices, so this is the triangle boundary
in moduleSectionBoundary. Taking k=e yields the asserted formula. -/
theorem square_zero_tensor_power_boundary
    {X Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (s : (((tensorPullback j).obj L).tensorPow n).val.presheaf.obj
      (Opposite.op ⊤))
    (hshort : ∀ d : ℕ, (ShortComplex.kernelSequence
      ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (L.tensorPow d))).ShortExact) :
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    ∃ xi : (RingedSpace.moduleCohomology Z.toRingedSpace 1).obj F,
      ∀ e : ℕ,
        ∃ a : (tensorPullback j).obj (L.tensorPow (n * (e + 1))) ≅
            (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1),
          ∃ b : (RingedSpace.moduleCohomology Z.toRingedSpace 1).obj
              (show Z.Modules from
                F ⊗ (((tensorPullback j).obj L).tensorPow n).tensorPow e) →+
            (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
              (kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
                (L.tensorPow (n * (e + 1))))),
            RingedSpace.moduleSectionBoundary X.toRingedSpace
                (ShortComplex.kernelSequence
                  ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
                    (L.tensorPow (n * (e + 1))))) (hshort (n * (e + 1)))
                ((tensorPowSection (homOfGlobalSection
                    (((tensorPullback j).obj L).tensorPow n) s) (e + 1) ≫ a.inv).app
                  ⊤ (1 : Γ(Z, ⊤))) =
              (e + 1) • b ((RingedSpace.moduleCohomology Z.toRingedSpace 1).map
                ((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection
                  (((tensorPullback j).obj L).tensorPow n) s) e) xi) := by sorry

end AlgebraicGeometry.Scheme.Modules
