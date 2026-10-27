/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.TraitRationalMap
public import Sheaf.AlgebraicGeometry.TraitTopFormOrder
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import Sheaf.AlgebraicGeometry.StrictHenselizationDVR

/-! # Differential order detects open immersions of smooth trait models

Source: BLR, Néron Models, 4.3 order construction and Lemma 1, printed pp.104--105
(PDF pp.110--111); strict-henselian sections: 2.2 Corollary 13, Proposition 14 and
2.3 Proposition 5. The finite-component clause uses the same determinant argument
(blueprint: lem-sfb-smooth-model-volume-order-comparison).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Orders, strict-henselian points, and the entire-domain open-immersion criterion.
Source: BLR 4.3 order construction and Lemma 1, printed pp.104--105, with its
finite-component extension; sections from 2.2/13--14 and 2.3/5
(blueprint: lem-sfb-smooth-model-volume-order-comparison).

Proof:
1. [lem-sfb-smooth-trait-volume-infrastructure],
[lem-sfb-group-scheme-differentials-from-identity], and
[lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension]: smooth trait geometry gives DVR
stalks at special-fibre generic points, with π
as uniformizer. Group differentials are pulled back from the identity, so have one
constant rank, equal to fibre dimension d. Their determinant lines have rank one.
A vector in a rank-one fraction-field module has a unique integral order.
2. [lem-sfb-smooth-space-cover-etale-sections],
[lem-trf-space-fibre-products-etale-covers], [lem-weil-pbc-etale-local-ring-triples],
[lem-weil-pbc-strict-henselization-triples],
[lem-sbc-strict-henselian-etale-neighbourhood-section], and
[lem-sc-strict-henselization-dvr]: a smooth model with nonempty special fibre is surjective over
the trait. Smooth
étale-local sections, pulled back to the strict henselization, give a section since
an étale neighbourhood of the closed point of a strictly henselian local ring splits.
The strict henselization is a DVR and π remains a uniformizer.
3. [lem-sfb-trait-line-section-order-normalization]: the line-section normalization lemma makes
π⁻ⁿᴹω and π⁻ⁿᴺω global frames. Applied
to the unit multiplier a and the given section it says a extends as a global unit.
4. [lem-sfb-smooth-trait-local-rational-spreading]: on the maximal domain the determinant
coefficient b satisfies
b = π^(nM - nN) a. At the special-fibre generic DVR its order is nonnegative, proving
nM ≥ nN. The maximal domain contains the whole generic fibre by separated spreading.
5. [lem-sfb-smooth-cotangent-etale-criterion] and
[lem-sfb-space-flat-isomorphism-dense-open]: if the orders agree, b is a unit on the whole domain
by generic-fibre injectivity.
The smooth cotangent criterion makes the map étale. It is separated and an isomorphism
on the quasi-compact schematically dense generic fibre, hence an open immersion.
6. Conversely an open immersion has invertible differential determinant. Its order
at the special-fibre generic point is zero, so nM = nN.
7. [lem-sfb-trait-line-section-order-normalization],
[lem-sfb-smooth-trait-volume-infrastructure], [lem-sfb-smooth-cotangent-etale-criterion],
and [lem-sfb-space-flat-isomorphism-dense-open]: with finitely many components of common order n0,
normalize globally. On each
source component open the corresponding section makes a a unit. These opens cover
the whole domain (including the case of empty special fibre). Thus b is a unit
everywhere, and the same étale generic-isomorphism criterion applies globally. -/
theorem smoothModel_volumeOrder_comparison
    {R E Ω : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field E] [Algebra R E] [IsFractionRing R E] [Field Ω] [IsAlgClosed Ω]
    (π : R) (hπ : Irreducible π)
    (s : Spec (.of Ω) ⟶ Spec (.of R))
    (hs : s (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R)
    (G : Over (Spec (.of E))) [GrpObj G]
    (hGsmooth : Smooth G.hom) (hGsep : IsSeparated G.hom)
    (hGft : LocallyOfFiniteType G.hom) (hGqc : QuasiCompact G.hom)
    (d : ℕ) (hd : topologicalKrullDim G.left = (d : WithBot ℕ∞))
    (ω : Γ(traitTopForms G.hom d, ⊤))
    (hω : Scheme.Modules.IsFreeGenerator ω) (hinv : IsLeftInvariantTopForm G d ω) :
    (∀ (M : SmoothTraitModel (R := R) G)
      (C : Set (M.hom.fiber (IsLocalRing.closedPoint R)))
      (hC : C ∈ irreducibleComponents (M.hom.fiber (IsLocalRing.closedPoint R)))
      (z : M.hom.fiber (IsLocalRing.closedPoint R)) (hz : IsGenericPoint z C),
      ∃ hdom : IsDomain (M.scheme.presheaf.stalk
          (M.hom.fiberι (IsLocalRing.closedPoint R) z)).1,
        IsDiscreteValuationRing (M.scheme.presheaf.stalk
          (M.hom.fiberι (IsLocalRing.closedPoint R) z)).1 ∧
        Irreducible (M.stalkScalar (M.hom.fiberι (IsLocalRing.closedPoint R) z) π) ∧
        ∃! n : ℤ, IsTraitVolumeOrder M π d ω
          (M.hom.fiberι (IsLocalRing.closedPoint R) z) n) ∧
    (∀ M : SmoothTraitModel (R := R) G,
      Nonempty (M.hom.fiber (IsLocalRing.closedPoint R)) →
        ∃ x : Scheme.strictHenselizationScheme s ⟶ M.scheme,
          x ≫ M.hom = traitStrictBase s) ∧
    (∀ (M N : SmoothTraitModel (R := R) G)
      (hM : IrreducibleSpace (M.hom.fiber (IsLocalRing.closedPoint R)))
      (hN : IrreducibleSpace (N.hom.fiber (IsLocalRing.closedPoint R)))
      (zM : M.hom.fiber (IsLocalRing.closedPoint R))
      (zN : N.hom.fiber (IsLocalRing.closedPoint R))
      (hzM : IsGenericPoint zM Set.univ) (hzN : IsGenericPoint zN Set.univ)
      (nM nN : ℤ)
      (hoM : IsTraitVolumeOrder M π d ω
        (M.hom.fiberι (IsLocalRing.closedPoint R) zM) nM)
      (hoN : IsTraitVolumeOrder N π d ω
        (N.hom.fiberι (IsLocalRing.closedPoint R) zN) nN)
      (v : M.scheme.RationalMap N.scheme) (hv : IsTraitRationalMap M.hom N.hom v)
      (e : G ≅ G) (he : HasGenericModelIso M N v e) (a : Γ(G.left, ⊤)ˣ)
      (ha : TopFormPullsTo G.hom G.hom e.hom.left d ω ((a : Γ(G.left, ⊤)) • ω))
      (hx : HasTraitUnitSection M s a Set.univ),
      nN ≤ nM ∧ ∃ p : M.scheme.PartialMap N.scheme,
        IsMaximalTraitRepresentative M.hom N.hom v p ∧
          (IsOpenImmersion p.hom ↔ nM = nN)) ∧
    (∀ (M N : SmoothTraitModel (R := R) G)
      (hM : (irreducibleComponents (M.hom.fiber (IsLocalRing.closedPoint R))).Finite)
      (hN : (irreducibleComponents (N.hom.fiber (IsLocalRing.closedPoint R))).Finite)
      (n₀ : ℤ)
      (hoM : ∀ (C : Set (M.hom.fiber (IsLocalRing.closedPoint R))),
        C ∈ irreducibleComponents (M.hom.fiber (IsLocalRing.closedPoint R)) →
        ∀ z : M.hom.fiber (IsLocalRing.closedPoint R), IsGenericPoint z C →
          IsTraitVolumeOrder M π d ω (M.hom.fiberι (IsLocalRing.closedPoint R) z) n₀)
      (hoN : ∀ (C : Set (N.hom.fiber (IsLocalRing.closedPoint R))),
        C ∈ irreducibleComponents (N.hom.fiber (IsLocalRing.closedPoint R)) →
        ∀ z : N.hom.fiber (IsLocalRing.closedPoint R), IsGenericPoint z C →
          IsTraitVolumeOrder N π d ω (N.hom.fiberι (IsLocalRing.closedPoint R) z) n₀)
      (v : M.scheme.RationalMap N.scheme) (hv : IsTraitRationalMap M.hom N.hom v)
      (e : G ≅ G) (he : HasGenericModelIso M N v e) (a : Γ(G.left, ⊤)ˣ)
      (ha : TopFormPullsTo G.hom G.hom e.hom.left d ω ((a : Γ(G.left, ⊤)) • ω))
      (hx : ∀ (C : Set (M.hom.fiber (IsLocalRing.closedPoint R))),
        C ∈ irreducibleComponents (M.hom.fiber (IsLocalRing.closedPoint R)) →
          HasTraitUnitSection M s a (traitComponentSet M C)),
      ∃ p : M.scheme.PartialMap N.scheme,
        IsMaximalTraitRepresentative M.hom N.hom v p ∧ IsOpenImmersion p.hom) := by
  sorry

end AlgebraicGeometry
