/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAbelian
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilated
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystem
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageRecoverLevels

/-!
# Grothendieck existence by devissage

## References

* [Stacks Project, Cohomology of Schemes, Tag 088A]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraizing a formal coherent module which is algebraizable on all thickenings
and differs from a completion by uniform ideal-power torsion. (Stacks, Lemma 088A) -/
theorem grothendieck_existence_devissage
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X)
    (α : M ⟶ completion X I |>.obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧
      ∃ k : KernelFork α, ∃ c : CokernelCofork α,
        Nonempty (IsLimit k) ∧ Nonempty (IsColimit c) ∧
        (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower K.toModulesι t).2 (k.pt.obj.obj (op n)))) ∧
        (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower K.toModulesι t).2 (c.pt.obj.obj (op n))))) :
    ∃ F : CoherentModules X, Nonempty ((completion X I).obj F ≅ M) := by
  obtain ⟨t, ht, k, c, hk, hc, hkt, hct⟩ := htorsion
  have hcomponent := ((coherentFormalModule_annihilated_iff X I K M
    ((completion X I).obj H) α).out 4 1 rfl rfl).mp
    ⟨k, c, hk, hc, t, ht, fun n ↦ ⟨hkt n, hct n⟩⟩
  obtain ⟨N, δ, σ, θ, hθ, hsquare, hδ⟩ :=
    grothendieckDevissage_secondAdicSystem I K M hthick H α hcomponent
  obtain ⟨F, a, β, hβ, ha, _⟩ :=
    grothendieckExistenceEasy_torsionTriple K H N δ hδ
  obtain ⟨φ, hφ⟩ := grothendieckDevissage_recoverLevels I K M H α hcomponent
    N δ σ θ hθ hsquare F a β hβ ha
  refine ⟨F, ⟨?_⟩⟩
  exact ObjectProperty.isoMk _ (NatIso.ofComponents φ (fun {_ _} f ↦ hφ _ _ f))

end AlgebraicGeometry
