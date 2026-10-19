/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.RingTheory.EtaleNormalRing
import Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso

/-!
# Comparing a normal finite cover with a finite etale cover

Source: Stacks Project, Tags 035I, 035L and 0BQM; the comparison in Tag 0EYJ.
(blueprint: lem-sbc-finite-normal-dense-open-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Etale ascent of normality on affine charts, transported to stalks.
Source: Stacks Project, Tag 033C, through `RingHom.Etale.isNormalRing`. -/
private theorem normal_stalks_of_etale {B E : Scheme.{u}} [IsIntegral B]
    (hB : ∀ y : B, IsIntegrallyClosed (B.presheaf.stalk y))
    (p : E ⟶ B) [Etale p] :
    ∀ z : E, IsDomain (E.presheaf.stalk z) ∧
      IsIntegrallyClosed (E.presheaf.stalk z) := by
  intro z
  obtain ⟨V, hV, hzV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := B) (x := p z) (U := ⊤) trivial
  obtain ⟨T, hT, hzT, hTV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := E) (x := z) (U := p ⁻¹ᵁ V) hzV
  have he := HasRingHomProperty.appLE @Etale p ‹_› ⟨V, hV⟩ ⟨T, hT⟩ hTV
  have hA : ∀ (a : Ideal Γ(B, V)) [a.IsPrime],
      IsDomain (Localization.AtPrime a) ∧ IsIntegrallyClosed (Localization.AtPrime a) := by
    intro a ha
    let y : PrimeSpectrum Γ(B, V) := ⟨a, ha⟩
    have hy : hV.fromSpec y ∈ V := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]
      exact Set.mem_range_self y
    let := B.presheaf.algebra_section_stalk ⟨hV.fromSpec y, hy⟩
    have := hV.isLocalization_stalk' y hy
    have := hB (hV.fromSpec y)
    let e := (IsLocalization.algEquiv a.primeCompl
      (B.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime a)).toRingEquiv
    exact ⟨e.toMulEquiv.symm.isDomain, IsIntegrallyClosed.of_equiv e⟩
  obtain ⟨hd, hc⟩ := he.isNormalRing hA (hT.primeIdealOf ⟨z, hzT⟩).asIdeal
  let := E.presheaf.algebra_section_stalk ⟨z, hzT⟩
  have := hT.isLocalization_stalk ⟨z, hzT⟩
  let e := (IsLocalization.algEquiv (hT.primeIdealOf ⟨z, hzT⟩).asIdeal.primeCompl
    (Localization.AtPrime (hT.primeIdealOf ⟨z, hzT⟩).asIdeal)
    (E.presheaf.stalk z)).toRingEquiv
  exact ⟨e.toMulEquiv.symm.isDomain, IsIntegrallyClosed.of_equiv e⟩

/-- A normal finite cover agrees with a finite etale cover if they agree on a dense open.

Source: Stacks Project, Tags 035I and 035L (relative normalization), Tag 0BQM
(integral-closure description), and the comparison in Tag 0EYJ.
(blueprint: lem-sbc-finite-normal-dense-open-comparison)

Proof: On an affine open Spec R of the normal integral base B, the two finite
covers are Spec C and Spec D. They are Noetherian and normal: normality of C comes
from hN; normality of D ascends through the etale ring map by 033C. A normal
Noetherian ring is a finite product of integrally closed domains. Density of
n^{-1} U ensures every component of C meets this open. As n is etale there, each
such component dominates the integral base: the etale image of its nonempty open
part is open and contains the generic point. The components of D also dominate,
since a finite etale morphism is flat and open. Since U is nonempty, it contains
the generic point of B. The given isomorphism over U therefore identifies the
finite generic algebras of C and D. In every component C is precisely the integral
closure of R in its generic field: its elements are integral over R by finiteness;
conversely an element integral over R is integral over C and belongs to C by
integral closedness. The same holds for D. Hence the generic isomorphism identifies
C with D. These affine identifications agree on overlaps because their generic
restrictions agree and both algebras inject into their generic algebras. They glue
to the stated isomorphism e over B. For empty covers the zero algebras are identified;
no connectedness or surjectivity of either cover is required. This comparison does
not construct an etale extension of an open cover. -/
theorem finite_normal_iso_of_dense_open_etale_comparison
    {B N E : Scheme.{u}} [IsLocallyNoetherian B] [IsIntegral B]
    (hB : ∀ y : B, IsIntegrallyClosed (B.presheaf.stalk y))
    (n : N ⟶ B) (p : E ⟶ B) [IsFinite n] [IsFinite p] [Etale p]
    (hN : ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z))
    (U : B.Opens) (hU : (U : Set B).Nonempty)
    (hdense : Dense (↑(n ⁻¹ᵁ U) : Set N))
    (hnU : Etale (n ∣_ U))
    (eU : (n ⁻¹ᵁ U).toScheme ≅ (p ⁻¹ᵁ U).toScheme)
    (heU : eU.hom ≫ p ∣_ U = n ∣_ U) :
    ∃ e : N ≅ E, e.hom ≫ p = n := by
  have : Etale (n ∣_ U) := hnU
  have hEdense : Dense (↑(p ⁻¹ᵁ U) : Set E) :=
    (U.isOpen.dense hU).preimage p.isOpenMap
  exact finite_normal_iso_of_dense_open n p hN (normal_stalks_of_etale hB p)
    U hdense hEdense eU heU

end AlgebraicGeometry.Scheme
