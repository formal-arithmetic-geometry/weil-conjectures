/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.Topology.KrullDimension

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Geometric-fibre hypotheses for coefficient comparison

Source: blueprint `sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`,
final coefficient-category reference; Stacks Tags 01T4, 01KU, 01T6 and 01OV;
Deligne, Weil II (1.1.7), pp. 150--151 and (1.1.14), p. 153
(blueprint: lem-fd-geometric-fibre-comparison-hypotheses).

The fibre and its structure morphism are the recorded `FiniteFieldDatum.geometricFiber`.
The stalk coefficient map is the canonical composite of `Scheme.ΓSpecIso.inv`,
the structure morphism on global sections, and the germ at the point. A unit whose
inverse is the image of the field inverse records both the unit and its specified inverse.
The two final equations identify the scheme inverse of geometric Frobenius explicitly.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- The geometric fibre is admissible for coefficient comparison, and arithmetic
Frobenius gives the inverse of its semilinear geometric Frobenius.

Source: blueprint `sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`,
final coefficient-category reference; Stacks Tags 01T4, 01KU, 01T6 and 01OV;
Deligne, Weil II (1.1.7), pp. 150--151 and (1.1.14), p. 153
(blueprint: lem-fd-geometric-fibre-comparison-hypotheses).

Proof:
1. The structure morphism is the base change of `X₀.hom` along `Spec(k) → Spec(k₀)`.
   Apply `lem-pod-separated-finite-type-base-change` to get separatedness, local finite
   type and quasi-compactness; the base morphism need not be finite.
2. The field `k` is Noetherian (`def-weil-pbc-noetherian-ring`), so its affine spectrum
   is locally Noetherian (`pqf-def-locnoeth`) and quasi-compact. Apply
   `lem-weil-pbc-finite-type-over-noetherian` to obtain `IsNoetherian` for the fibre.
3. Apply `lem-kun-dimension-finite-type` to this finite-type morphism over `k`.
   Its dimension bound uses `def-kun-dimension`. For the empty fibre the dimension
   is bottom and the bound can be zero; otherwise take a finite natural bound.
4. The cardinality and embedding in `def-weil-finite-field-fiber`, together with
   `def-weil-finite-field-q-elements`, give characteristic `p` for both fields.
   Since the primes `l` and `p` differ, `l` is nonzero in the field `k`.
   The canonical ring map to each stalk sends the field inverse to a two-sided
   inverse of the integer `l`. Package these elements as the stated unit.
   If the fibre is empty, this universal assertion has no points to check.
5. Use the two inverse identities of the automorphism `geometricFrobenius` from
   `def-weil-frobenius-detailed`. Its stored inverse acts by inverse geometric field
   Frobenius, which is arithmetic field Frobenius by cancellation of the two inverses.
   This requires no Cartesian-square theorem and no `k`-linearity.
-/
theorem geometric_fibre_comparison_hypotheses (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsSeparated (D.geometricFiber X₀).hom ∧
    LocallyOfFiniteType (D.geometricFiber X₀).hom ∧
    QuasiCompact (D.geometricFiber X₀).hom ∧
    IsNoetherian (D.geometricFiber X₀).left ∧
    (∃ d : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ (d : WithBot ℕ∞)) ∧
    (∀ x : (D.geometricFiber X₀).left,
      ∃ t : ((D.geometricFiber X₀).left.presheaf.stalk x)ˣ,
        (t : (D.geometricFiber X₀).left.presheaf.stalk x) = l ∧
        (↑(t⁻¹) : (D.geometricFiber X₀).left.presheaf.stalk x) =
          (((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
            (D.geometricFiber X₀).hom.appTop ≫
            (D.geometricFiber X₀).left.presheaf.Γgerm x).hom ((l : D.k)⁻¹))) ∧
    (D.geometricFrobenius X₀).hom ≫
        D.galoisMap X₀.hom (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _
          (Fintype.ofFinite D.k₀) D.k _ _ _) = 𝟙 _ ∧
    D.galoisMap X₀.hom (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _
        (Fintype.ofFinite D.k₀) D.k _ _ _) ≫
      (D.geometricFrobenius X₀).hom = 𝟙 _ := by
  classical
  have hsep : IsSeparated (D.geometricFiber X₀).hom := by
    change IsSeparated (pullback.snd X₀.hom _)
    infer_instance
  have hft : LocallyOfFiniteType (D.geometricFiber X₀).hom := by
    change LocallyOfFiniteType (pullback.snd X₀.hom _)
    infer_instance
  have hqc : QuasiCompact (D.geometricFiber X₀).hom := by
    change QuasiCompact (pullback.snd X₀.hom _)
    infer_instance
  have : IsLocallyNoetherian (D.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber X₀).hom
  have : CompactSpace (D.geometricFiber X₀).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber X₀).hom
  refine ⟨hsep, hft, hqc, ⟨⟩, exists_topologicalKrullDim_le (D.geometricFiber X₀).hom,
    ?_, ?_, ?_⟩
  · let : Fintype D.k₀ := Fintype.ofFinite _
    have : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
    have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    have hl0 : (l : D.k) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime _ hl hlp.symm
    intro x
    let φ := ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
      (D.geometricFiber X₀).hom.appTop ≫
      (D.geometricFiber X₀).left.presheaf.Γgerm x).hom
    refine ⟨Units.map φ (Units.mk0 (l : D.k) hl0), ?_, ?_⟩
    · exact map_natCast φ l
    · rfl
  · change _ = 𝟙 (D.geometricFiber X₀).left
    simpa only [geometricFrobenius,
      FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv,
      AlgEquiv.aut_inv, AlgEquiv.symm_symm] using
      (D.geometricFrobenius X₀).hom_inv_id
  · change _ = 𝟙 (D.geometricFiber X₀).left
    simpa only [geometricFrobenius,
      FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv,
      AlgEquiv.aut_inv, AlgEquiv.symm_symm] using
      (D.geometricFrobenius X₀).inv_hom_id

end WeilConjectures.FiniteFieldDatum
