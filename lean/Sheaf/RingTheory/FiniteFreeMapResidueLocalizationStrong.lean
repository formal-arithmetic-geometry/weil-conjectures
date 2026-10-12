module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

namespace Module

/-- A matrix minor argument gives a split localized map and a free cokernel, while an
isomorphism on the residue field gives an explicit inverse after localization. The proof is
Stacks Project, Algebra, Tag 00O0, parts (1) and (3): choose a nonvanishing maximal minor,
localize at its determinant, and use elementary row and column operations; in the square case
use the adjugate matrix. (blueprint: lem-pc-finite-free-map-residue-localization-strong) -/
theorem finiteFreeMap_residue_localization_strong
    {R : Type*} [CommRing R] (m n : ℕ)
    (u : (Fin m → R) →ₗ[R] (Fin n → R)) (p : Ideal R) [p.IsPrime] :
    (Function.Injective (u.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        (∃ v : TensorProduct R (Localization.Away f) (Fin n → R) →ₗ[Localization.Away f]
            TensorProduct R (Localization.Away f) (Fin m → R),
          v.comp (u.baseChange (Localization.Away f)) = LinearMap.id ∧
          Module.Finite (Localization.Away f)
            (TensorProduct R (Localization.Away f) (Fin n → R) ⧸
              LinearMap.range (u.baseChange (Localization.Away f))) ∧
          Module.Free (Localization.Away f)
            (TensorProduct R (Localization.Away f) (Fin n → R) ⧸
              LinearMap.range (u.baseChange (Localization.Away f))))) ∧
    (Function.Bijective (u.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        ∃ v : TensorProduct R (Localization.Away f) (Fin n → R) →ₗ[Localization.Away f]
            TensorProduct R (Localization.Away f) (Fin m → R),
          v.comp (u.baseChange (Localization.Away f)) = LinearMap.id ∧
          (u.baseChange (Localization.Away f)).comp v = LinearMap.id) := by
  sorry

end Module
