/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.AlgebraicGeometry.FormalFunctionsAffineRestrictionDictionary
import Sheaf.AlgebraicGeometry.TheoremFormalFunctions
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Formal functions on an affine open of the base

Source: Stacks Project, Theorem 02OC, degree zero, and Lemma 088B.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option maxHeartbeats 600000 in
-- Scalar transport unfolds two section functors and the affine chart in quotient types.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport degree-zero formal functions to an arbitrary affine open of the base.
Source: Stacks Project, Theorem 02OC and Lemma 088B.
(blueprint: lem-weil-pbc-formal-functions-affine-pushforward-sections)

Proof: Write U as Spec A using its affine chart. Since Y is Noetherian, A is Noetherian.
Base change f along U -> Y; the resulting morphism to U is proper. Restrict F to the
inverse image of U, preserving coherence, and transport it along the affine chart.
The restricted ideal J is the ideal sheaf of I = J(U); its pullback is the restriction
of J.comap f. Restriction preserves ideal products, powers, and cokernels, so the
restricted quotient system is the quotient system in globalSections_formal_functions.
The identity Gamma(U,f_*F) = Gamma(f^(-1)U,F) supplies its module M, including the
A-action induced by f. Apply globalSections_formal_functions to obtain theta_n and
its canonical isomorphism. Pushforward on sections is evaluation on the inverse image,
and evaluation preserves limits. Transport the isomorphism and both projection equations
through these identifications. The quotient equation below is the transported theta_n
factorization; the last equation is the transported limit projection equation.
For J=0 this is the constant-section system; for J=1 its quotients and completion are
zero. F=0 and the empty open also give zero modules. No coherence assumption on f_*F
and no natural transformation kappa are needed for this transport step.
-/
theorem formalFunctions_affine_pushforward_sections {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f] (F : CoherentModules X)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    let R := Γ(Y, U)
    let I := J.ideal ⟨U, hU⟩
    let H := (Scheme.Modules.pushforward f).obj F.obj
    let M := Γ(H, U)
    let T := formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f
    let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
    ∃ θ : ∀ n : ℕ,
        (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) →ₗ[R] E.obj (T.obj (op n)),
      (∀ n : ℕ, ModuleCat.ofHom
        ((θ n).comp (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M)))) =
          E.map ((Scheme.Modules.pushforward f).map
            (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))) ∧
      ∃ e : ModuleCat.of R (AdicCompletion I M) ≅ E.obj (limit T),
        ∀ n : ℕ, e.hom ≫ E.map (limit.π T (op n)) =
          ModuleCat.ofHom ((θ n).comp (AdicCompletion.eval I M (n + 1))) := by
  sorry

end AlgebraicGeometry
