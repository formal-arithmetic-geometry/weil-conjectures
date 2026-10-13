/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Sheaf.AlgebraicGeometry.CompletionInternalHomQuotient
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentSheafHom
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Affine completed-Hom evaluation before tensor comparison

Source: Stacks Project, Tags 0882 and 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Affine quotient evaluation is detected by the linear map on adic completions.
The supplied map sends each ordinary linear map to its adic completion. There are no
scalar extension tensor products in this comparison.

Source: Stacks Project, Tag 0882, affine argument before applying flat base change for Hom;
Tag 087W, the equivalence of affine formal modules and complete modules.
(blueprint: lem-weil-pbc-completion-internal-hom-affine-completion-evaluation).

Proof:
1. Write A = O_X(U), J = I(U), N = G(U), M = F(U), H = Hom_A(N,M).
   Affine tilde/sections identifies the internal Hom sections with H. Coherence of
   internal Hom and the affine finite type criterion make H, N, M finite.
   Ideal products and quotient sections identify the three quotient systems with
   P/J^(n+1)P, including projections and transition maps, for P = H, N, M.
2. The inverse limit of the H quotient system is its adic completion. These
   identifications give rho. Finite-level quotient surjectivity and the internal-Hom
   quotient factorization force each e_n, by he, to be quotient evaluation.
3. Evaluating compatible quotient maps componentwise produces a completed-ring-linear
   map from the completion of H to Hom between the completions of N and M. It sends
   the image of h to AdicCompletion.map J h. It equals the supplied epsilon: the
   completion of finite H is generated over the completed ring by images of H
   (the completion-tensor comparison), so two linear maps agreeing there are equal.
4. Restrict t to U and pass to inverse limits to obtain v. The affine formal-module
   comparison identifies this map componentwise. Equality of maps of completed modules
   is equivalent to equality at every quotient level (all projections are jointly
   injective, and the N-limit projects onto each level by AdicCompletion.eval_surjective).
   Thus epsilon(rho(s)) = v
   is equivalent to the specified evaluation equations, in both directions.
   This argument does not use a flat base-change isomorphism for Hom. -/
theorem completion_internal_hom_affine_completion_evaluation {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F G : CoherentModules X)
    (e : ∀ n : ℕᵒᵖ,
      formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj) ⟶
        SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj))
    (he : ∀ n : ℕᵒᵖ,
        formalModuleQuotientπ I (n.unop + 1) (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
          e n ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) (formalModuleQuotientπ I (n.unop + 1) G.obj)
            (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj)) =
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj))
    (U : X.affineOpens) :
    let A := Γ(X, U.val)
    let B := AdicCompletion (I.ideal U) A
    let N := Γ(G.obj, U.val)
    let M := Γ(F.obj, U.val)
    ∀ ε : AdicCompletion (I.ideal U) (N →ₗ[A] M) →ₗ[B]
      (AdicCompletion (I.ideal U) N →ₗ[B] AdicCompletion (I.ideal U) M),
      (∀ h : N →ₗ[A] M, ε (AdicCompletion.of (I.ideal U) _ h) =
        AdicCompletion.map (I.ideal U) h) →
    ∃ ρ : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).val.obj (op U.val) //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            ((formalCompletionSystem I (SheafOfModules.homObj
              (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f).val.app (op U.val)
              (s a) = s b} ≃ AdicCompletion (I.ideal U) (N →ₗ[A] M),
      ∀ (t : ∀ n : ℕᵒᵖ, formalModuleQuotient I (n.unop + 1) G.obj ⟶
        formalModuleQuotient I (n.unop + 1) F.obj),
        (∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
          t a ≫ (formalCompletionSystem I F.obj).map f =
            (formalCompletionSystem I G.obj).map f ≫ t b) →
        ∃ v : AdicCompletion (I.ideal U) N →ₗ[B] AdicCompletion (I.ideal U) M, ∀ s,
          (∀ n : ℕᵒᵖ, (e n).val.app (op U.val) (s.val n) =
            ((SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
              (formalModuleQuotient I (n.unop + 1) G.obj)
              (formalModuleQuotient I (n.unop + 1) F.obj)).symm (t n)).val (op U.val)) ↔
            ε (ρ s) = v := by
  sorry

end AlgebraicGeometry
