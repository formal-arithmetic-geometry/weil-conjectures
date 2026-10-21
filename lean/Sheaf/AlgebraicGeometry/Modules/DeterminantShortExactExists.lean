/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.LocalSplittingFiniteFree
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeMorphism
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-!
# Construction of the determinant isomorphism

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-determinant-short-exact-exists).
-/

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorSheafPowerIso_hom_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorSheafPowerIso M n).hom.app U (exteriorSheafSection M n U a) =
      wedge (M := M) (r := n) (U := U) a := by
  rw [← exteriorSheafPowerIso_inv_wedge M n U a]
  exact inv_app_hom_app_apply_of_iso (exteriorSheafPowerIso M n).symm _

set_option backward.isDefEq.respectTransparency false in
/-- Existence, without uniqueness or invertibility assertions, of the determinant
isomorphism with its inverse characterized on wedges and arbitrary quotient lifts.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-determinant-short-exact-exists).

Proof: Use the local splitting of the short exact sequence and refine the cover to
trivialize the outside terms. On each chart identify the middle term with the direct
sum by the splitting. Apply `exteriorPower.existsUnique_topDirectSum` to the bases
of the outside terms, and transport its inverse to the middle term. This sends a
tensor of wedges to the wedge of the included first-term sections followed by the
chosen lifts of the quotient sections. Changing a lift changes it by an included
first-term section. Expand by multilinearity: every changed term contains `r₁ + 1`
first-term factors, hence vanishes in a free rank-`r₁` module by the exterior-power
basis theorem. Consequently the formula holds for every lift and is independent of
the splitting. On intersections the two inverse maps agree on tensors of wedges;
these generate locally. Therefore the local maps and their inverses agree and glue
as sheaf morphisms. The two composites are identities locally and hence globally.
The formula on an arbitrary open follows by restriction to these charts and
separatedness. Empty wedges treat either rank-zero case. -/
theorem determinant_shortExact_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₂.IsFiniteLocallyFreeOfRank r₂]
    [S.X₃.IsFiniteLocallyFreeOfRank r₃] :
    ∃ e : exteriorSheaf S.X₂ r₂ ≅ exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        e.inv.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) :=
  by
  obtain ⟨ψ, hψ⟩ := determinant_wedgeMorphism_exists S hS r₁ r₂ r₃ hr
  obtain ⟨ι, U, hU, hsplit⟩ := exists_openCover_split_shortExact S hS r₁ r₂ r₃
  let eA := tensorIso (C := X.Modules) (exteriorSheafPowerIso S.X₁ r₁)
    (exteriorSheafPowerIso S.X₃ r₃)
  let eB := exteriorSheafPowerIso S.X₂ r₂
  let φ := eA.hom ≫ ψ ≫ eB.inv
  have hφ : ∀ (V : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op V))
      (b : Fin r₃ → S.X₃.val.obj (op V)) (c : Fin r₃ → S.X₂.val.obj (op V)),
      (∀ i, S.g.val.app (op V) (c i) = b i) →
      φ.val.app (op V)
          (tmulSection (exteriorSheafSection S.X₁ r₁ V a)
            (exteriorSheafSection S.X₃ r₃ V b)) =
        exteriorSheafSection S.X₂ r₂ V
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op V) (a j)) c (Fin.cast hr i)) := by
    intro V a b c hc
    change (exteriorSheafPowerIso S.X₂ r₂).inv.app V
      (ψ.app V ((((exteriorSheafPowerIso S.X₁ r₁).hom ⊗ₘ
        (exteriorSheafPowerIso S.X₃ r₃).hom).app V)
          (tmulSection (exteriorSheafSection S.X₁ r₁ V a)
            (exteriorSheafSection S.X₃ r₃ V b)))) = _
    rw [tensorHom_app_tmulSection, exteriorSheafPowerIso_hom_wedge,
      exteriorSheafPowerIso_hom_wedge]
    exact (congrArg ((exteriorSheafPowerIso S.X₂ r₂).inv.app V) (hψ V a b c hc)).trans
      (exteriorSheafPowerIso_inv_wedge S.X₂ r₂ V _)
  have hψiso : IsIso ψ := by
    apply Hom.isIso_of_forall_bijective_app
    intro x
    have hx : x ∈ (⨆ i, U i) := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨e, hf, hg⟩ := hsplit i
    exact ⟨U i, hi,
      determinant_wedgeMorphism_bijective_of_split S r₁ r₂ r₃ hr ψ hψ (U i) e hf hg⟩
  have hφiso : IsIso φ := by
    have hfac : eA.hom ≫ ψ ≫ eB.inv = φ := rfl
    rw [← hfac]
    infer_instance
  exact ⟨(asIso φ).symm, hφ⟩

end AlgebraicGeometry.Scheme.Modules
