/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.RationalTangentCoefficientDescent
import WeilConjectures.AlgebraicGeometry.RationalTangentCoefficientOperations

/-!
# Linear descent of tangent coefficients

## References

* [Stacks Project, Tag 0B2D](https://stacks.math.columbia.edu/tag/0B2D)
* [Stacks Project, Tag 0B2E](https://stacks.math.columbia.edu/tag/0B2E)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Extracting the epsilon coefficient gives a linear map to the cotangent dual. -/
theorem exists_rationalTangent_coefficient_linearMap
    (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (x : X) :
    let R := X.presheaf.stalk x
    let K := X.residueField x
    let s : k →+* R := (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x).hom
    let r : k →+* K :=
      (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x).hom
    Function.Bijective r →
    letI : Module k (schemeTangentSpace k X p x) :=
      Module.compHom (schemeTangentSpace k X p x) r
    letI : Module K (IsLocalRing.CotangentSpace R) :=
      inferInstanceAs (Module (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))
    letI : Module k (IsLocalRing.CotangentSpace R) :=
      Module.compHom (IsLocalRing.CotangentSpace R) r
    ∃ L : schemeTangentSpace k X p x →ₗ[k] (IsLocalRing.CotangentSpace R →ₗ[k] k),
      ∀ θ : schemeTangentSpace k X p x,
        ∃ hx : θ.val (IsLocalRing.closedPoint (DualNumber K)) = x,
          let sharp : R →+* DualNumber K :=
            (eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
              Scheme.stalkClosedPointTo θ.val).hom
          ∃ D : R →+ k,
            (∀ a : R, sharp a =
              TrivSqZeroExt.inl ((X.residue x).hom a) + TrivSqZeroExt.inr (r (D a))) ∧
            (∀ a : IsLocalRing.maximalIdeal R,
              L θ ((IsLocalRing.maximalIdeal R).toCotangent a) = D a) ∧
            (∀ c : k, D (s c) = 0) := by
  dsimp only
  intro hr
  let R := X.presheaf.stalk x
  let K := X.residueField x
  let r : k →+* K :=
    (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x).hom
  let : Module k (schemeTangentSpace k X p x) :=
    Module.compHom (schemeTangentSpace k X p x) r
  let : Module K (IsLocalRing.CotangentSpace R) :=
    inferInstanceAs (Module (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))
  let : Module k (IsLocalRing.CotangentSpace R) :=
    Module.compHom (IsLocalRing.CotangentSpace R) r
  obtain ⟨C, hC⟩ := exists_rationalTangent_coefficient_descent k X p x hr
  have hcoeff : ∀ θ : schemeTangentSpace k X p x,
      ∃ hx : θ.val (IsLocalRing.closedPoint (DualNumber K)) = x,
        ∀ a : IsLocalRing.maximalIdeal R,
          r (C θ ((IsLocalRing.maximalIdeal R).toCotangent a)) =
            ((eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
              Scheme.stalkClosedPointTo θ.val).hom a).snd := by
    intro θ
    obtain ⟨hx, D, hD, hDm, _⟩ := hC θ
    refine ⟨hx, ?_⟩
    intro a
    rw [hDm]
    have h := congrArg TrivSqZeroExt.snd (hD a)
    simpa only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add] using h.symm
  obtain ⟨hadd, hsmul⟩ := rationalTangent_coefficient_operation_compatibility k X p x hr C
    hcoeff
  let L : schemeTangentSpace k X p x →ₗ[k] (IsLocalRing.CotangentSpace R →ₗ[k] k) :=
    { toFun := C
      map_add' := hadd
      map_smul' := hsmul }
  exact ⟨L, hC⟩


end AlgebraicGeometry
