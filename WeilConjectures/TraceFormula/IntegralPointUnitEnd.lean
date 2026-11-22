/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersPadicIntBasis
public import WeilConjectures.PoincareDuality.Biduality.Integral
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral

/-!

# Scalars on the unit of bounded constructible `𝒪_E`-complexes on a point

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `s = Spec k`.
The scalars `𝒪_E` act on the unit `𝒪_E,s` of `Dᵇc(s)⟦𝒪_E⟧`
(`ProEtale.CondensedRing.PadicIntegersRingObj.integersUnitEndRingHom`), and for `k` separably
closed every endomorphism of the unit is a scalar
(`ProEtale.CondensedRing.PadicIntegersRingObj.surjective_integersUnitEndRingHom`). Every ring
homomorphism from `𝒪_E` to a field of characteristic zero is injective
(`ProEtale.CondensedRing.PadicIntegersRingObj.injective_of_ringHom_integers`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] (E : PadicAlgCl.FiniteIntermediateField ℓ)

section Scalars

variable [Fact (ringChar k ≠ ℓ)]

/-- The inclusion `Mod_{𝒪̲_E,s} ⥤ D(Mod_{𝒪̲_E,s})` of complexes concentrated in degree `0`. -/
noncomputable abbrev pointSingleFunctorIntegral :
    PointModIntegral ℓ k E ⥤ DerivedCategory (PointModIntegral ℓ k E) :=
  HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The endomorphisms of the unit of `D(Mod_{𝒪̲_E,s})` are those of the unit of the full
subcategory `Dᵇc(s)⟦𝒪_E⟧`. -/
noncomputable def unitEndRingEquivIntegral :
    End (𝟙_ (DerivedCategory (PointModIntegral ℓ k E))) ≃+*
      End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)) :=
  have hι : Function.Bijective ((ObjectProperty.ι _).mapEndRingHom (𝟙_
      (Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧))) :=
    ((ObjectProperty.fullyFaithfulι _).mulEquivEnd _).bijective
  have : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := PointModIntegral ℓ k E))) :=
    inferInstanceAs (IsIso (𝟙 _))
  (asIso (Functor.LaxMonoidal.ε
      (DerivedCategory.Qh (C := PointModIntegral ℓ k E)))).symm.conjRingEquiv.trans
    (RingEquiv.ofBijective _ hι).symm

/-- The scalars `𝒪_E →+* End (𝟙_ Dᵇc(Spec k)⟦𝒪_E⟧)`: a scalar `a` acts on the unit `𝒪_E,s` by
multiplication by the constant global section `a`, placed in degree `0`. -/
noncomputable def integersUnitEndRingHom :
    integers ℓ E.1 →+*
      End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)) :=
  (unitEndRingEquivIntegral ℓ k E).toRingHom.comp
    (((pointSingleFunctorIntegral ℓ k E).mapEndRingHom (Mod.regular
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left))).comp
        (pointIntegersUnitEndRingHom ℓ k E))

/-- For `k` separably closed, every endomorphism of the unit of `Dᵇc(Spec k)⟦𝒪_E⟧` is a scalar
of `𝒪_E`. -/
theorem surjective_integersUnitEndRingHom [IsSepClosed k] :
    Function.Surjective (integersUnitEndRingHom ℓ k E) := by
  let A := PointModIntegral ℓ k E
  have e := (DerivedCategory.singleFunctorIsoCompQ A 0).trans
    (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso A).symm)
  have : (pointSingleFunctorIntegral ℓ k E).Full := Functor.Full.of_iso e
  have : (pointSingleFunctorIntegral ℓ k E).Faithful := Functor.Faithful.of_iso e
  have hF : Function.Bijective ((pointSingleFunctorIntegral ℓ k E).mapEndRingHom
      (Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left))) :=
    ((Functor.FullyFaithful.ofFullyFaithful
      (pointSingleFunctorIntegral ℓ k E)).mulEquivEnd _).bijective
  rw [integersUnitEndRingHom, RingHom.coe_comp]
  exact (RingEquiv.surjective _).comp (hF.2.comp (surjective_pointIntegersUnitEndRingHom ℓ k E))


end Scalars
/-- Every ring homomorphism from `𝒪_E` to a field of characteristic zero is injective, since
every element of `E` becomes integral after multiplication by a power of `ℓ`. -/
lemma injective_of_ringHom_integers {L : Type*} [Field L] [CharZero L]
    (φ : integers ℓ E.1 →+* L) : Function.Injective φ := by
  refine (injective_iff_map_eq_zero φ).2 fun a ha ↦ ?_
  by_contra ha0
  have ha0' : (a : E.1) ≠ 0 := fun h ↦ ha0 (Subtype.ext h)
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_integers ℓ E.1 (a : E.1)⁻¹
  have hb : a * ⟨_, hn⟩ = (ℓ : integers ℓ E.1) ^ n := by
    apply Subtype.ext
    push_cast
    field_simp
  have := congrArg φ hb
  rw [map_mul, ha, zero_mul, map_pow, map_natCast] at this
  exact pow_ne_zero n (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero) this.symm

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
