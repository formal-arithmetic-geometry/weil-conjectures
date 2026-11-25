/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Descent of the Japanese condition along a finite extension of domains

## Implementation details

For a finite extension `L` of the fraction field `K` of `A`, embed `L` into an algebraic closure
of the fraction field `E` of `B`; the compositum `M` of `L` and `E` is finite over `E`, and
`integralClosure A L` embeds as an `A`-submodule of the finite `A`-module `integralClosure B M`.

## References

* [Stacks, Tag 032K]
-/

@[expose] public section

universe uA uB uK uE

set_option autoImplicit false

/-- A Noetherian domain contained in a finite extension domain is Japanese if the larger
one is Japanese. -/
theorem isN2_of_finite_extension (A : Type uA) (B : Type uB)
    (K : Type uK) (E : Type uE) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra B E] [IsFractionRing B E]
    (hAB : Function.Injective (algebraMap A B)) (hB : IsN2 B E) : IsN2 A K := by
  classical
  let : Algebra A E := ((algebraMap B E).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  let i : K →ₐ[A] E := IsFractionRing.liftAlgHom
    (A := A) (g := Algebra.ofId A E)
    ((IsFractionRing.injective B E).comp hAB)
  let : Algebra K E := i.toRingHom.toAlgebra
  have : IsScalarTower A K E := IsScalarTower.of_algHom i
  -- The algebraic closure and its subfields stay in the universe of E.
  let Ω := AlgebraicClosure E
  intro L _ _ _ _ _
  let ψ : L →ₐ[K] Ω := IsAlgClosed.lift
  have : FiniteDimensional K ψ.fieldRange :=
    ψ.equivFieldRange.toLinearEquiv.finiteDimensional
  let M := IntermediateField.adjoin E (ψ.fieldRange : Set Ω)
  have : FiniteDimensional E M := Module.rank_lt_aleph0_iff.mp
    ((IntermediateField.adjoin_rank_le_of_isAlgebraic_right E ψ.fieldRange).trans_lt
      (Module.rank_lt_aleph0 K ψ.fieldRange))
  -- Use the inherited scalar actions on the intermediate field.
  have : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite B (integralClosure B M) := hB M
  have : Module.Finite A (integralClosure B M) := Module.Finite.trans B _
  let f : L →ₐ[A] M :=
    { toRingHom := ψ.toRingHom.codRestrict M.toSubring (fun x ↦
        IntermediateField.subset_adjoin E (ψ.fieldRange : Set Ω) ⟨x, rfl⟩)
      commutes' := fun a ↦ Subtype.ext (by
        change ψ (algebraMap A L a) =
          (algebraMap E Ω) ((algebraMap B E) (algebraMap A B a))
        rw [AlgHom.map_algebraMap ψ, IsScalarTower.algebraMap_apply A E Ω]
        rfl) }
  -- Integrality is preserved by f and by extending scalars from A to B.
  let g : integralClosure A L →ₗ[A] integralClosure B M :=
    { toFun := fun x ↦ ⟨f x, (x.property.map f).tower_top⟩
      map_add' := fun x y ↦ Subtype.ext (f.map_add x y)
      map_smul' := fun a x ↦ Subtype.ext (f.toLinearMap.map_smul a x) }
  exact Module.Finite.of_injective g (fun x y h ↦
    Subtype.ext (f.injective (congrArg Subtype.val h)))
