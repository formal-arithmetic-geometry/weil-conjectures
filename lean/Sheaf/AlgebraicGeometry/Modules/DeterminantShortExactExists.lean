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
import Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism
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
  obtain ⟨φ, hφ⟩ := determinant_wedgeMorphism_exists S hS r₁ r₂ r₃ hr
  obtain ⟨ι, U, hU, hsplit⟩ := exists_openCover_split_shortExact S hS r₁ r₂ r₃
  let eA := tensorIso (C := X.Modules) (exteriorSheafPowerIso S.X₁ r₁)
    (exteriorSheafPowerIso S.X₃ r₃)
  let eB := exteriorSheafPowerIso S.X₂ r₂
  let ψ := eA.inv ≫ φ ≫ eB.hom
  have hψ : ∀ (V : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op V))
      (b : Fin r₃ → S.X₃.val.obj (op V)) (c : Fin r₃ → S.X₂.val.obj (op V)),
      (∀ i, S.g.val.app (op V) (c i) = b i) →
      ψ.app V (tmulSection (wedge (M := S.X₁) (r := r₁) a)
        (wedge (M := S.X₃) (r := r₃) b)) =
        wedge (M := S.X₂) (r := r₂)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op V) (a j)) c (Fin.cast hr i)) := by
    intro V a b c hc
    have ht := tensorHom_app_tmulSection
      (M := exteriorPower S.X₁ r₁) (N := exteriorPower S.X₃ r₃)
      (M' := exteriorSheaf S.X₁ r₁) (N' := exteriorSheaf S.X₃ r₃) (U := V)
      (exteriorSheafPowerIso S.X₁ r₁).inv (exteriorSheafPowerIso S.X₃ r₃).inv
      (wedge (M := S.X₁) (r := r₁) a) (wedge (M := S.X₃) (r := r₃) b)
    rw [exteriorSheafPowerIso_inv_wedge, exteriorSheafPowerIso_inv_wedge] at ht
    change eB.hom.app V (φ.app V (eA.inv.app V _)) = _
    have hw := exteriorSheafPowerIso_inv_wedge S.X₂ r₂ V
      (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op V) (a j)) c (Fin.cast hr i))
    exact (congrArg (fun z ↦ eB.hom.app V (φ.app V z)) ht).trans
      ((congrArg (fun z ↦ eB.hom.app V z) (hφ V a b c hc)).trans
        ((congrArg (fun z ↦ eB.hom.app V z) hw.symm).trans
          (congrArg (fun k ↦ k.app V (wedge (M := S.X₂) (r := r₂)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op V) (a j)) c (Fin.cast hr i))))
            eB.inv_hom_id)))
  have hψiso : IsIso ψ := by
    apply Hom.isIso_of_forall_bijective_app
    intro x
    have hx : x ∈ (⨆ i, U i) := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨e, hf, hg⟩ := hsplit i
    exact ⟨U i, hi,
      determinant_wedgeMorphism_bijective_of_split S r₁ r₂ r₃ hr ψ hψ (U i) e hf hg⟩
  have hφiso : IsIso φ := by
    have hfac : eA.hom ≫ ψ ≫ eB.inv = φ := by simp [ψ]
    rw [← hfac]
    infer_instance
  exact ⟨(asIso φ).symm, hφ⟩

end AlgebraicGeometry.Scheme.Modules
