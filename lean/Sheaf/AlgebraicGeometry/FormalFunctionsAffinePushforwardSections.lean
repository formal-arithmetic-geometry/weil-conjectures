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
  let R := Γ(Y, U)
  let I := J.ideal ⟨U, hU⟩
  let V := f ⁻¹ᵁ U
  let Z := V.toScheme
  let g := (f ∣_ U) ≫ hU.isoSpec.hom
  let K := (J.comap f).comap V.ι
  let P := (Scheme.Modules.restrictFunctor V.ι).obj F.obj
  let G := RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
    ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
  let H := (Scheme.Modules.pushforward f).obj F.obj
  let T := formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨hg, hP, hK, a, b, hb⟩ :=
    formalFunctions_affine_restriction_dictionary J f F U hU
  let : IsProper g := hg
  obtain ⟨θ₀, hθ₀, _, e₀, he₀⟩ := globalSections_formal_functions I g K hK P hP
  let α := a.toLinearEquiv
  let θ : ∀ n : ℕ, (Γ(H, U) ⧸ (I ^ (n + 1) • (⊤ : Submodule R Γ(H, U)))) →ₗ[R]
      E.obj (T.obj (op n)) := fun n ↦ (b.hom.app (op n)).hom.comp
        ((θ₀ n).comp ((α.toLinearMap.reduceModIdeal (I ^ (n + 1))).restrictScalars R))
  have hθ (n : ℕ) : ModuleCat.ofHom
      ((θ n).comp (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R Γ(H, U))))) =
      E.map ((Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) := by
    ext x
    change (b.hom.app (op n)).hom
      (θ₀ n ((I ^ (n + 1) • (⊤ : Submodule R (G.obj P))).mkQ (α x))) = _
    have hh := LinearMap.congr_fun (hθ₀ n) (α x)
    change θ₀ n ((I ^ (n + 1) • (⊤ : Submodule R (G.obj P))).mkQ (α x)) =
      (G.map (formalModuleQuotientπ K (n + 1) P)).hom (α x) at hh
    rw [hh]
    exact ConcreteCategory.congr_hom (hb n) x
  let c := ((AdicCompletion.congr I α).restrictScalars R).toModuleIso
  let d := preservesLimitIso E T
  let e := c ≪≫ e₀ ≪≫ HasLimit.isoOfNatIso b ≪≫ d.symm
  refine ⟨θ, hθ, e, ?_⟩
  intro n
  dsimp only [e, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Category.assoc, Category.assoc, preservesLimitIso_inv_π,
    HasLimit.isoOfNatIso_hom_π, ← Category.assoc e₀.hom, he₀]
  apply ModuleCat.hom_ext
  ext x
  rfl

end AlgebraicGeometry
