/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.Irreducible
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.AlgebraicGeometry.GenericFibreAffineRingModels
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Sober

/-!
# The complement of a horizontal closed subscheme over a trait

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §6.5, Theorem 1 proof,
printed p.162 (PDF p.168), the thin schematic closure of the generic complement
(blueprint: lem-sfb-trait-horizontal-closed-complement).

The generic and closed fibres use the canonical residue fields at the zero and maximal
primes. These are canonically the fraction field and residue field of the DVR.
For `g : ZF ⟶ Y`, `g.ker.support` is the underlying closed subset of `g.image`.
The equality of opens identifies the generic fibre of the open complement.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The schematic closure of a closed generic subscheme containing no generic-fibre
component has a complement dense in every geometric fibre, with the prescribed generic
fibre; the closure contains no closed-fibre component.

Source: BLR, Néron Models, §6.5, proof of Theorem 1, printed p.162 (PDF p.168)
(blueprint: lem-sfb-trait-horizontal-closed-complement).

Proof:
1. Choose a uniformizer π. The smooth-trait infrastructure gives Noetherian regular Y,
   reduced closed fibre, an open generic fibre, and DVR stalks with uniformizer π at
   special-fibre generic points (lem-sfb-smooth-trait-volume-infrastructure).
   Regular-normal decomposition (rem-pc-regular-normal) gives integral clopen components.
2. On an affine U = Spec A the generic fibre is Spec A[1/π]
   (lem-sbc-generic-fibre-affine-ring-models). If its closed subscheme has ideal J,
   its inverse image is affine, so the composite g is affine, hence quasi-compact and
   quasi-separated (lem-weil-pbc-affine-morphism-permanence). Its image ideal is
   I = ker(A → A[1/π]/J), by lem-weil-pbc-scheme-image-qc-kernel.
   Inverting π gives I[1/π] = J, and I is π-saturated.
3. Restricting the image to the generic open commutes with the image
   (lemma-nagata-scheme-image-restrict-open). A closed immersion is its own image
   (lemma-nagata-scheme-image-of-closed-immersion). Taking open complements gives
   the asserted equality of opens on the generic fibre.
4. At a generic point ξ of a closed-fibre component, choose an affine integral
   neighbourhood inside its clopen ambient component. The affine stalk localization
   (lem-weil-pbc-affine-open-stalk-localization) identifies its localization with
   the DVR stalk. The image of π in A is nonzero. The generic part of the ambient
   component is a nonempty irreducible clopen component of the generic fibre.
   Thus J cannot vanish: otherwise ZF contains a dense open in that component.
5. A nonzero numerator of an element of J lies in I. The injection A → A_ξ gives
   I A_ξ ≠ 0. Localization preserves π-saturation: clear a denominator outside ξ
   and use the saturation of I.
6. Every nonzero element of the DVR A_ξ is a unit times π^n
   (lem-weil-pbc-dvr-unit-times-uniformizer-power). Saturation therefore gives
   1 ∈ I A_ξ. Hence ξ is outside the image support, proving the last assertion.
7. Sobriety supplies generic points of fibre components (lem-sc-scheme-sober).
   These points lie in the open complement in both ordinary fibres. Components
   cover (lem-sc-irreducible-components-cover), so both complements are dense.
   The DVR has just its zero and maximal primes, by the unit-times-power theorem.
8. Smooth fibrewise density is preserved by base change
   (lem-sfb-smooth-fibrewise-dense-open-base-change); apply this to Spec Ω at t.
   This gives the displayed density for every algebraically closed extension.
   Empty fibres satisfy density vacuously. For empty ZF, all J and I are unit ideals,
   so the image is empty and the complement is Y. No perfection or excellence is used. -/
theorem trait_horizontal_closed_complement
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {ZF : Scheme.{u}}
    (i : ZF ⟶ f.fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R))
    [IsClosedImmersion i]
    (hthin : ∀ C ∈ irreducibleComponents
      (f.fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)),
      ¬ C ⊆ (i.ker.support : Set (f.fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)))) :
    (f.fiberι (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) ⁻¹ᵁ
        (i ≫ f.fiberι (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)).ker.support.compl =
      i.ker.support.compl ∧
    (∀ (t : Spec (.of R)) (Ω : Type u) [Field Ω]
      [Algebra ((Spec (.of R)).residueField t) Ω] [IsAlgClosed Ω],
      Dense ((pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of R)).residueField t) Ω)) ≫
          (Spec (.of R)).fromSpecResidueField t)) ⁻¹'
        ((i ≫ f.fiberι (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)).ker.support : Set Y)ᶜ)) ∧
    (∀ C ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)),
      ¬ C ⊆ (f.fiberι (IsLocalRing.closedPoint R)) ⁻¹'
        ((i ≫ f.fiberι (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)).ker.support : Set Y)) := by
  sorry

end AlgebraicGeometry
