module

public import WeilConjectures.DeligneLaumon.AffineLine.RealPushforward

set_option maxHeartbeats 200000
@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
variable {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

example {ι : PadicAlgCl l →+* ℂ} {K : WeilSheaf k₀ l X}
    (hK : K.IsReal ι) (hvan : ∀ ν : ℕ, ν ≠ 1 → IsZero ((higherLowerShriek k₀ l f ν).obj K)) :
    ((higherLowerShriek k₀ l f 1).obj K).IsReal ι := by
  intro ξ n
  obtain ⟨X', _, g, _, _, _, _, hfib⟩ :=
    exists_fiber_expand_charpolyRev_stalk_higherLowerShriek (k₀ := k₀) (f := f) (l := l) ξ
  have h₁ := (hK.upperStar g).isReal_compactlySupportedCohomology_of_subsingleton 1 fun i hi ↦ by
    rcases lt_or_ge i 0 with h | h
    · exact subsingleton_globalSections_of_isZero
        (isZero_homologySheaf_derivedLowerShriek_of_neg ((upperStar g).obj K) h)
    · obtain ⟨ν, rfl⟩ := Int.eq_ofNat_of_zero_le h
      exact (hfib K ν).1 (hvan ν (by exact_mod_cast hi))
  have hd := Scheme.Hom.degreeOver_ne_zero (Y ↘ Spec (CommRingCat.of k₀)) ξ.2
  have := h₁ (n * (Y ↘ Spec (CommRingCat.of k₀)).degreeOver ξ.1)
  have hc := (hfib K 1).2
  rw [Nat.cast_one] at hc
  rwa [FrobeniusModule.localPolynomial, ← hc,
    Polynomial.coeff_expand_mul (Nat.pos_of_ne_zero hd)] at this

end AlgebraicGeometry.WeilSheaf
