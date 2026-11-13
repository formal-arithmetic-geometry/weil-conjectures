/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.IdealPowerQuotientLiftingSection

/-!
# Local lifting into ideal-power annihilator quotients

## References

* Stacks Project, Tag 01PQ
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Finite affine gluing gives eventual vanishing and lifting of sections for the
quotients by ideal-power annihilators. These are stagewise criteria, not statements
about a colimit or a choice of diagram.
(Stacks, Tags 01PQ and 01PM) -/
theorem ideal_power_quotient_local_lifting
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2)
    (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F)
    (hmono : ∀ n : ℕ, Mono (a n))
    (hqc : ∀ n : ℕ, (A n).IsQuasicoherent)
    (hann : ∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
      s ∈ Set.range ((a n).app W) ↔
        ∀ (W' : X.Opens) (h : W' ≤ W)
          (b : Γ((idealSheafPower ι n).1, W')),
          (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).asHom.hom
            (F.presheaf.map (homOfLE h).op s) = 0)
    (hquot : ∀ (n : ℕ) (W : X.Opens), W ≤ U →
      Function.Bijective ((cokernel.π (a n)).app W))
    (q : ∀ (n m : ℕ), n ≤ m → (cokernel (a n) ⟶ cokernel (a m)))
    (hq : ∀ (n m : ℕ) (h : n ≤ m),
      cokernel.π (a n) ≫ q n m h = cokernel.π (a m)) :
    (∀ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
      φ.app U (one n) = 0 →
      ∃ (m : ℕ) (h : n ≤ m), r n m h ≫ φ ≫ q n m h = 0) ∧
    (∀ s : Γ(F, U), ∃ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
      (cokernel.π (a n)).app U s = φ.app U (one n)) := by
  constructor
  · intro n φ hφ
    let : (A n).IsQuasicoherent := hqc n
    let : (cokernel (a n)).IsQuasicoherent := Modules.isQuasicoherent_cokernel (a n)
    obtain ⟨m, h, hm⟩ := ideal_power_evaluation_eventually_zero
      ι (cokernel (a n)) U one r hU hone hr n φ hφ
    refine ⟨m, h, ?_⟩
    rw [← Category.assoc, hm, zero_comp]
  · exact ideal_power_quotient_local_lifting_section
      ι F U one r hU hone hr A a hmono hqc hann hquot q hq

end AlgebraicGeometry.Scheme
