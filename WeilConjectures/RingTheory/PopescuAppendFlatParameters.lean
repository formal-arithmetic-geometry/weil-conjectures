/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.PopescuInitialFlatCoordinates
import WeilConjectures.RingTheory.FlatRegularFibreParameterSelection
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Appending parameters to a residue differential basis

For a geometrically regular algebra localized at `q`, appending suitable generators of the maximal
ideal to coordinates lifting a residue differential basis gives a flat map from a localized
polynomial ring.

## Implementation details

Tag 07E6 gives a flat map from the first polynomial localization with regular local closed fibre
`S`; a subset of the given generators forms a regular system of parameters of `S` (Nakayama and
Tag 00NQ). The fibre of the extended polynomial localization is regular local at the origin
(Tag 00OP), so the closed-fibre map is flat (Tag 07DY) and Tag 00MP gives flatness. The cases
`t = 0`, `r = 0` and a field closed fibre are included. No injectivity of the selected indexing
function is required.

## References

* [Stacks, Tag 07FH] (construction of property (1))
* [Stacks, Tag 07E6]
* [Stacks, Tag 00NQ]
* [Stacks, Tag 00OP]
* [Stacks, Tag 07DY]
* [Stacks, Tag 00MP]
-/

@[expose] public section

set_option autoImplicit false
universe u v w
namespace Algebra

/-- Appending selected maximal-ideal generators to fixed differential coordinates gives
flat polynomial coordinates. No admissible subalgebra or enlargement is constructed here. -/
theorem exists_popescu_append_flat_parameters
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (F : Type w) [Field F] [Algebra k F] [EssFiniteType k F]
    (ι : F →ₐ[k] q.ResidueField)
    (t r : ℕ) (xs : Fin t → Λ) (ys : Fin r → Λ) (a : Fin t → F)
    (ha : ∀ j, ι (a j) = IsLocalRing.residue (Localization.AtPrime q)
      (algebraMap Λ (Localization.AtPrime q) (xs j)))
    (b : Module.Basis (Fin t) F (KaehlerDifferential k F))
    (hb : ∀ j, b j = KaehlerDifferential.D k F (a j))
    (hyq : ∀ i, ys i ∈ q)
    (hys : Ideal.span (Set.range (fun i ↦ algebraMap Λ (Localization.AtPrime q) (ys i))) =
      q.map (algebraMap Λ (Localization.AtPrime q))) :
    ∃ (e : ℕ) (s : Fin e → Fin r),
      let φ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
        MvPolynomial.aeval (Fin.addCases xs (fun i ↦ ys (s i)))
      ∃ ψ : Localization.AtPrime (q.comap φ.toRingHom) →+* Localization.AtPrime q,
        ψ.comp (algebraMap (MvPolynomial (Fin (t + e)) k)
            (Localization.AtPrime (q.comap φ.toRingHom))) =
          (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom ∧
        q.map (algebraMap Λ (Localization.AtPrime q)) =
          (q.comap φ.toRingHom).map
            ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom) ∧
        ψ.Flat := by
  obtain ⟨hflat₀, hfibre₀⟩ :=
    popescu_initial_flat_coordinates k Λ p hp hreg q F ι t xs a ha b hb
  obtain ⟨e, s, hflat, hgen⟩ :=
    exists_flat_regular_fibre_parameter_selection k Λ q t r xs ys hyq hys hflat₀ hfibre₀
  let φ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
    MvPolynomial.aeval (Fin.addCases xs (fun i ↦ ys (s i)))
  let g := (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom
  let J := (q.comap φ.toRingHom).map g
  refine ⟨e, s, Localization.localRingHom (q.comap φ.toRingHom) q φ.toRingHom rfl,
    ?_, ?_, hflat⟩
  · apply RingHom.ext
    intro f
    exact Localization.localRingHom_to_map (q.comap φ.toRingHom) q φ.toRingHom rfl f
  · change q.map (algebraMap Λ (Localization.AtPrime q)) = J
    apply le_antisymm
    · rw [hgen]
      apply sup_le
      · apply Ideal.map_le_iff_le_comap.mpr
        intro f hf
        have heval : φ (MvPolynomial.rename (Fin.castAdd e) f) =
            MvPolynomial.aeval xs f := by
          simp [φ, MvPolynomial.aeval_rename, Function.comp_def]
        have hmem : MvPolynomial.rename (Fin.castAdd e) f ∈ q.comap φ.toRingHom := by
          change φ (MvPolynomial.rename (Fin.castAdd e) f) ∈ q
          rw [heval]
          exact hf
        have h := Ideal.mem_map_of_mem g hmem
        change (algebraMap Λ (Localization.AtPrime q))
          (φ (MvPolynomial.rename (Fin.castAdd e) f)) ∈ J at h
        rw [heval] at h
        exact h
      · apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        have heval : φ (MvPolynomial.X (Fin.natAdd t i)) = ys (s i) := by
          simp [φ]
        have hmem : MvPolynomial.X (Fin.natAdd t i) ∈ q.comap φ.toRingHom := by
          change φ (MvPolynomial.X (Fin.natAdd t i)) ∈ q
          rw [heval]
          exact hyq (s i)
        have h := Ideal.mem_map_of_mem g hmem
        change (algebraMap Λ (Localization.AtPrime q))
          (φ (MvPolynomial.X (Fin.natAdd t i))) ∈ J at h
        rw [heval] at h
        exact h
    · change (q.comap φ.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom) ≤ _
      rw [← Ideal.map_map]
      exact Ideal.map_mono Ideal.map_comap_le

end Algebra
