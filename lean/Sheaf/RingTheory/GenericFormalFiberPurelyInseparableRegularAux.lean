module

public import Sheaf.RingTheory.GRing
public import Sheaf.RingTheory.CohenRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

@[expose] public section

universe u

/-- Regularity of the purely inseparable tensor product in the field-model case.
Source: Stacks Project, More on Algebra, Proposition 07PS, last two paragraphs.
This is the field-model branch of the generic formal fibre argument.
(blueprint: new-lem-generic-formal-fibre-purely-inseparable-regular-field) -/
theorem isRegular_genericFormalFiber_fieldModel
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    (k : Type u) [Field k] (d : ℕ)
    (e : Nonempty (A ≃+* MvPowerSeries (Fin d) k))
    (P : Ideal A) [P.IsPrime]
    (k' : Type (max u u)) [Field k']
    [Algebra ((⊥ : Ideal A).ResidueField) k']
    [Module.Finite ((⊥ : Ideal A).ResidueField) k']
    [IsPurelyInseparable ((⊥ : Ideal A).ResidueField) k'] :
    IsRegularRing
      (TensorProduct ((⊥ : Ideal A).ResidueField) k'
        ((⊥ : Ideal A).Fiber
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
            (Localization.AtPrime P)))) := by
  sorry

/-- Regularity of the purely inseparable tensor product in the Cohen-model case.
Source: Stacks Project, More on Algebra, Proposition 07PS, last two paragraphs.
This is the Cohen-model branch of the generic formal fibre argument.
(blueprint: new-lem-generic-formal-fibre-purely-inseparable-regular-cohen) -/
theorem isRegular_genericFormalFiber_cohenModel
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    (Λ : Type u) [CommRing Λ] (d p : ℕ)
    (hc : IsCohenRing p Λ)
    (e : Nonempty (A ≃+* MvPowerSeries (Fin d) Λ))
    (P : Ideal A) [P.IsPrime]
    (k' : Type (max u u)) [Field k']
    [Algebra ((⊥ : Ideal A).ResidueField) k']
    [Module.Finite ((⊥ : Ideal A).ResidueField) k']
    [IsPurelyInseparable ((⊥ : Ideal A).ResidueField) k'] :
    IsRegularRing
      (TensorProduct ((⊥ : Ideal A).ResidueField) k'
        ((⊥ : Ideal A).Fiber
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
            (Localization.AtPrime P)))) := by
  sorry

end
