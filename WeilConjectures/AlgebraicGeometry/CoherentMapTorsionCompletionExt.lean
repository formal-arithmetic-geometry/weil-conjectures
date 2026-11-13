/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentMapTorsionCompletionExtZero

/-! # Detecting maps using completion and a torsion-kernel comparison

Source: Stacks Project, Tag 0889, uniqueness argument, and Tag 088A, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Completion and composition with a map having power-torsion kernel detect maps.
Only the kernel of b needs a bound; its cokernel plays no role (Stacks, Tags 0889 and 088A). -/
theorem coherentMap_torsion_completion_ext
    {X : Scheme.{u}} [IsNoetherian X] (K : X.IdealSheafData)
    (P Q R : CoherentModules X) (b : Q ⟶ R)
    (hker : ∃ t : ℕ, 1 ≤ t ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel b.hom)))
    (f g : P ⟶ Q) (hcomp : f ≫ b = g ≫ b)
    (hcompletion : (completion X K).map f = (completion X K).map g) : f = g := by
  obtain ⟨n, hn⟩ := coherentMap_torsion_completion_ext_zero K Q R b hker
  let d : P.obj ⟶ Q.obj := f.hom - g.hom
  have hd : d ≫ b.hom = 0 := by
    dsimp [d]
    rw [Preadditive.sub_comp]
    have hc := congrArg (fun a => a.hom) hcomp
    exact sub_eq_zero.mpr hc
  let a : P.obj ⟶ kernel b.hom := kernel.lift b.hom d hd
  have hq : d ≫ formalModuleQuotientπ K (n + 1) Q.obj = 0 := by
    have hc := congrArg (fun a => a.hom.app (op n)) hcompletion
    change formalModuleQuotientMap K f.hom (Nat.le_refl (n + 1)) =
      formalModuleQuotientMap K g.hom (Nat.le_refl (n + 1)) at hc
    have he := congrArg (fun a => formalModuleQuotientπ K (n + 1) P.obj ≫ a) hc
    simp only [formalModuleQuotientMap, formalModuleQuotientπ,
      cokernel.π_desc] at he
    dsimp [d]
    rw [Preadditive.sub_comp]
    exact sub_eq_zero.mpr he
  have ha : a = 0 := by
    let := hn
    apply (cancel_mono (kernel.ι b.hom ≫ formalModuleQuotientπ K (n + 1) Q.obj)).mp
    simp only [zero_comp, ← Category.assoc]
    simpa [a] using hq
  have hd0 : d = 0 := by
    rw [← kernel.lift_ι b.hom d hd, ← show a = kernel.lift b.hom d hd from rfl,
      ha, zero_comp]
  apply InducedCategory.hom_ext
  exact sub_eq_zero.mp hd0

end AlgebraicGeometry
