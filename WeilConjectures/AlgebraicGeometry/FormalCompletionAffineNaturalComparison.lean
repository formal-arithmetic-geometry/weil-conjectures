/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import WeilConjectures.AlgebraicGeometry.FormalCompletionAffineQuotients
import WeilConjectures.Algebra.Module.AdicCompletionStableRanges
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffine
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesIsoEquivalence
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Natural affine comparison for coherent completion

## References

* Stacks Project, Tags 087W and 0881
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine formal-module realization identifies completion with adic completion
of affine sections, naturally for every coherent module map. No exact sequence is assumed
(Stacks, Tags 087W and 0881). -/
theorem formalCompletion_affine_natural_comparison
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    (U : X.Opens) [IsNoetherian U.toScheme] (hU : IsAffineOpen U)
    (ρ : CoherentFormalModule X I ⥤ CoherentFormalModule U.toScheme (I.comap U.ι))
    (hρ : ρ ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι =
      (IsCoherentFormalModule I).ι ⋙
        (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
          (Scheme.Modules.restrictFunctor U.ι)) :
    ∃ F : CoherentFormalModule U.toScheme (I.comap U.ι) ⥤ ModuleCat.{u} Γ(X, U),
      F.PreservesZeroMorphisms ∧ ReflectsLimitsOfShape WalkingParallelPair F ∧
      ∃ e : ∀ G : CoherentModules X,
        F.obj (ρ.obj ((completion X I).obj G)) ≃ₗ[Γ(X, U)]
          AdicCompletion (I.ideal ⟨U, hU⟩) Γ(G.obj, U),
        ∀ (G H : CoherentModules X) (f : G ⟶ H) (x),
          e H ((F.map (ρ.map ((completion X I).map f))) x) =
            AdicCompletion.map (I.ideal ⟨U, hU⟩) (f.hom.val.app (op U)).hom (e G x) := by
  classical
  let T := formalAffineSectionTower X U (I.comap U.ι)
  let F := formalAffineSectionLimit X U (I.comap U.ι)
  let J : Ideal Γ(X, U) := I.ideal ⟨U, hU⟩
  obtain ⟨hfull, hfaithful⟩ := formalAffineSectionLimit_full_faithful
    X U hU (I.comap U.ι)
  let : F.Full := hfull
  let : F.Faithful := hfaithful
  have hzero : F.PreservesZeroMorphisms := by
    constructor
    intro G H
    apply limit.hom_ext
    intro n
    change lim.map (T.map (0 : G ⟶ H)) ≫ limit.π (T.obj H) n =
      (0 : limit (T.obj G) ⟶ limit (T.obj H)) ≫ limit.π (T.obj H) n
    have hz : (T.map (0 : G ⟶ H)).app n = 0 := rfl
    calc
      _ = limit.π (T.obj G) n ≫ (T.map (0 : G ⟶ H)).app n :=
        limMap_π (T.map (0 : G ⟶ H)) n
      _ = _ := by rw [hz, comp_zero, zero_comp]
  obtain ⟨θ, htrans, hnatural⟩ := formalCompletion_affine_quotients X I U hU ρ hρ
  let M (G : CoherentModules X) := T.obj (ρ.obj ((completion X I).obj G))
  let q (G : CoherentModules X) (n : ℕ) : Γ(G.obj, U) →ₗ[Γ(X, U)] (M G).obj (op n) :=
    (θ G n).toLinearMap.comp (Submodule.mkQ (J ^ (n + 1) • ⊤))
  have hker (G : CoherentModules X) (n : ℕ) :
      LinearMap.ker (q G (n + 0)) ≤ J ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(G.obj, U)) := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply (θ G n).injective
    change θ G n (Submodule.mkQ (J ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(G.obj, U))) x) = 0 at hx
    exact hx.trans (map_zero (θ G n)).symm
  have hrange (G : CoherentModules X) (n : ℕ) :
      Set.range ((M G).map (homOfLE (Nat.le_add_right n 0)).op).hom =
        Set.range (q G n) := by
    have hs : Function.Surjective (q G n) :=
      (θ G n).surjective.comp (Submodule.mkQ_surjective _)
    rw [Set.range_eq_univ.mpr hs]
    have hi : (homOfLE (Nat.le_add_right n 0)).op = 𝟙 (op n) := Subsingleton.elim _ _
    rw [hi]
    exact (congrArg (fun k ↦ Set.range k.hom) ((M G).map_id (op n))).trans
      (Set.range_eq_univ.mpr Function.surjective_id)
  have hv (G : CoherentModules X) := adicCompletion_iso_of_stable_ranges J
    (ModuleCat.of Γ(X, U) Γ(G.obj, U)) (M G) (q G)
    (fun n ↦ (θ G n).toLinearMap) (fun _ ↦ rfl) (htrans G) 0 (hker G) (hrange G)
  choose v hv using hv
  let e (G : CoherentModules X) :
      F.obj (ρ.obj ((completion X I).obj G)) ≃ₗ[Γ(X, U)] AdicCompletion J Γ(G.obj, U) :=
    (v G).symm.toLinearEquiv
  refine ⟨F, hzero, inferInstance, e, ?_⟩
  intro G H f x
  apply (v H).toLinearEquiv.injective
  apply Concrete.limit_ext (M H)
  intro j
  obtain ⟨n⟩ := j
  have hp (K : CoherentModules X) (z : AdicCompletion J Γ(K.obj, U)) :
      (limit.π (M K) (op n)) ((v K).hom z) =
        θ K n (AdicCompletion.eval J Γ(K.obj, U) (n + 1) z) :=
    ConcreteCategory.congr_hom (hv K n) z
  change (limit.π (M H) (op n)) ((v H).hom
      ((v H).inv ((F.map (ρ.map ((completion X I).map f))) x))) = _
  rw [Iso.inv_hom_id_apply]
  change (limit.π (M H) (op n)) ((F.map (ρ.map ((completion X I).map f))) x) =
    (limit.π (M H) (op n)) ((v H).hom
      (AdicCompletion.map J (f.hom.val.app (op U)).hom (e G x)))
  rw [hp H]
  have hm := ConcreteCategory.congr_hom
    (limMap_π (T.map (ρ.map ((completion X I).map f))) (op n)) x
  change (limit.π (M H) (op n)) ((F.map (ρ.map ((completion X I).map f))) x) =
    ((T.map (ρ.map ((completion X I).map f))).app (op n))
      ((limit.π (M G) (op n)) x) at hm
  rw [hm]
  have hx : (limit.π (M G) (op n)) x =
      θ G n (AdicCompletion.eval J Γ(G.obj, U) (n + 1) (e G x)) := by
    rw [← hp G]
    exact congrArg (limit.π (M G) (op n)) ((v G).inv_hom_id_apply x).symm
  rw [hx]
  exact LinearMap.congr_fun (hnatural G H f n)
    (AdicCompletion.eval J Γ(G.obj, U) (n + 1) (e G x))

end AlgebraicGeometry
