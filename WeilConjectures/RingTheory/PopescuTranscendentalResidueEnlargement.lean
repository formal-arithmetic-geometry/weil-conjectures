/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Defs

import WeilConjectures.RingTheory.PopescuTranscendentalImageStructure
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Algebraic.Basic


/-!
# Geometric residue-power capture in an Artinian local algebra

Let `A₀` be a Popescu-admissible subalgebra of an Artinian local `k`-algebra `B` and `x` a unit
of `B` whose residue `α` is transcendental over the residue field `F₀` of `A₀`. We enlarge `A₀`
to an admissible subalgebra containing `x` itself, with residue field `F₀(α)`.

## Implementation details

The enlargement is the image of the localization of `A₀[T]` at the preimage `m₀[T]` of the
maximal ideal of `B` under `T ↦ x`; see `popescu_transcendental_image_structure`. It is
essentially of finite type over `k` by the Artinian local residue criterion.

## References

* Stacks Project, Tags 07FH and 07FI (transcendental case)
-/

@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra

private theorem localizedPolynomialImage_residue_generated
    {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B] [IsLocalRing B]
    (A₀ : Subalgebra k B) [IsLocalRing A₀] (x : B)
    (hle : A₀ ≤ popescuLocalizedPolynomialImage A₀ x)
    [Algebra (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField (popescuLocalizedPolynomialImage A₀ x))]
    (hres : ∀ a₀ : A₀, algebraMap (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField (popescuLocalizedPolynomialImage A₀ x))
        (IsLocalRing.residue A₀ a₀) =
          IsLocalRing.residue _ (Subalgebra.inclusion hle a₀)) :
    IntermediateField.adjoin (IsLocalRing.ResidueField A₀)
      {IsLocalRing.residue _ (⟨x, mem_popescuLocalizedPolynomialImage A₀ x⟩ :
        popescuLocalizedPolynomialImage A₀ x)} = ⊤ := by
  let A := popescuLocalizedPolynomialImage A₀ x
  let D := Localization.AtPrime (popescuPolynomialPrime A₀ x)
  let g : D →ₐ[k] A := (popescuLocalizedPolynomialMap A₀ x).rangeRestrict
  let e : Polynomial A₀ →ₐ[k] A :=
    g.comp (IsScalarTower.toAlgHom k (Polynomial A₀) D)
  let a : A := ⟨x, mem_popescuLocalizedPolynomialImage A₀ x⟩
  let E := IntermediateField.adjoin (IsLocalRing.ResidueField A₀) {IsLocalRing.residue A a}
  have heC (c : A₀) : e (Polynomial.C c) = Subalgebra.inclusion hle c := by
    apply Subtype.ext
    exact (popescuLocalizedPolynomialMap_algebraMap A₀ x _).trans
      (Polynomial.aevalTower_C A₀.val x c)
  have heX : e Polynomial.X = a := by
    apply Subtype.ext
    exact (popescuLocalizedPolynomialMap_algebraMap A₀ x _).trans
      (Polynomial.aevalTower_X A₀.val x)
  have he (f : Polynomial A₀) : IsLocalRing.residue A (e f) ∈ E := by
    induction f using Polynomial.induction_on' with
    | add f q hf hq => simpa only [map_add] using E.add_mem hf hq
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow,
        heC, heX, ← hres]
      exact E.mul_mem (E.algebraMap_mem _) (E.toSubalgebra.pow_mem
        (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)) n)
  apply top_unique
  intro z _
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := A) z
  obtain ⟨d, hd⟩ := (popescuLocalizedPolynomialMap A₀ x).rangeRestrict_surjective b
  obtain ⟨⟨f, s⟩, hds⟩ := IsLocalization.surj (popescuPolynomialPrime A₀ x).primeCompl d
  have hsunit : IsUnit (e (s : Polynomial A₀)) :=
    (IsLocalization.map_units D s).map g
  have hsne : IsLocalRing.residue A (e (s : Polynomial A₀)) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hsunit
  have heq := congrArg (fun d ↦ IsLocalRing.residue A (g d)) hds
  rw [map_mul] at heq
  change IsLocalRing.residue A (g d * e (s : Polynomial A₀)) =
    IsLocalRing.residue A (e f) at heq
  change g d = b at hd
  rw [map_mul, hd] at heq
  rw [(eq_div_iff hsne).mpr heq]
  exact E.div_mem (he f) (he s)

/-- The transcendental branch of geometric enlargement, containing the unit itself: if
the residue of the unit `x` is transcendental over the residue field `F₀` of the admissible
`A₀`, there is an admissible local `A ⊇ A₀` containing `x` whose residue field is generated
over `F₀` by the (transcendental) residue of `x`, compatibly with the residue maps. -/
theorem exists_popescu_transcendental_residue_enlargement
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
    [IsArtinianRing B] [IsLocalRing B]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (A₀ : Subalgebra k B) [IsLocalRing A₀]
    (hA₀ : A₀.IsPopescuAdmissible (IsLocalRing.maximalIdeal B))
    (x : B) (hx : IsUnit x)
    [IsLocalHom A₀.val]
    [Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B)]
    [IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B)]
    (hmap : ∀ a₀ : A₀, algebraMap (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField B) (IsLocalRing.residue A₀ a₀) =
        IsLocalRing.residue B (a₀ : B))
    (hα : Transcendental (IsLocalRing.ResidueField A₀) (IsLocalRing.residue B x)) :
    ∃ (A : Subalgebra k B) (_ : IsLocalRing A), ∃ hle : A₀ ≤ A,
      A.IsPopescuAdmissible (IsLocalRing.maximalIdeal B) ∧
      ∃ a : A, (a : B) = x ∧
        ∃ (alg : Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A)),
          letI := alg
          IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A) ∧
          (∀ a₀ : A₀, algebraMap (IsLocalRing.ResidueField A₀)
            (IsLocalRing.ResidueField A) (IsLocalRing.residue A₀ a₀) =
              IsLocalRing.residue A (Subalgebra.inclusion hle a₀)) ∧
          Transcendental (IsLocalRing.ResidueField A₀) (IsLocalRing.residue A a) ∧
          IntermediateField.adjoin (IsLocalRing.ResidueField A₀)
            {IsLocalRing.residue A a} = ⊤ := by
  classical
  have _ := hp
  have _ := hx
  let A := popescuLocalizedPolynomialImage A₀ x
  have hstruct := popescu_transcendental_image_structure k B A₀ hA₀ x hmap hα
  have : IsArtinianRing A := hstruct.1
  have : EssFiniteType k A₀ := hA₀.2.1
  have hfinite : EssFiniteType k A := essFiniteType_popescuLocalizedPolynomialImage A₀ x
  have hA : A.IsPopescuAdmissible (IsLocalRing.maximalIdeal B) :=
    ⟨hstruct.1, hfinite, inferInstance, hstruct.2⟩
  let hle : A₀ ≤ A := le_popescuLocalizedPolynomialImage A₀ x
  let a : A := ⟨x, mem_popescuLocalizedPolynomialImage A₀ x⟩
  have : IsLocalHom A.val := ⟨fun b hb ↦ by
    by_contra hn
    have hnil : IsNilpotent b :=
      Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hn
    exact (hnil.map A.val.toRingHom).not_isUnit hb⟩
  have : IsLocalHom (Subalgebra.inclusion hle) :=
    ⟨fun c hc ↦ IsLocalHom.map_nonunit (f := A₀.val) c (hc.map A.val)⟩
  let f := IsLocalRing.ResidueField.mapAlgHom (Subalgebra.inclusion hle)
  let alg : Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A) :=
    f.toRingHom.toAlgebra
  let := alg
  have htower : IsScalarTower k (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField A) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hres : ∀ c : A₀, algebraMap (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField A) (IsLocalRing.residue A₀ c) =
        IsLocalRing.residue A (Subalgebra.inclusion hle c) := fun _ ↦ rfl
  let j := IsLocalRing.ResidueField.mapAlgHom A.val
  have hj : j.toRingHom.comp (algebraMap (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField A)) = algebraMap (IsLocalRing.ResidueField A₀)
        (IsLocalRing.ResidueField B) := by
    ext c
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective (R := A₀) c
    exact (hmap c).symm
  have htrans : Transcendental (IsLocalRing.ResidueField A₀)
      (IsLocalRing.residue A a) := by
    exact _root_.Transcendental.of_ringHom_of_comp_eq
      (f := RingHom.id (IsLocalRing.ResidueField A₀)) (g := j.toRingHom)
      hα Function.injective_id (by
        ext c
        exact congrArg (fun f : IsLocalRing.ResidueField A₀ →+*
          IsLocalRing.ResidueField B ↦ f c) hj.symm)
  exact ⟨A, inferInstance, hle, hA, a, rfl, alg, htower, hres, htrans,
    localizedPolynomialImage_residue_generated A₀ x hle hres⟩

end Algebra
