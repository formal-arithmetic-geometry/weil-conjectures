/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Compatible etale origins of normalized finite-coefficient towers

Source: blueprint main-20261015, proper base change,
prop-weil-pbc-preservation-constructible.proof.md, compatible witness sentence;
Stacks Project, proetale.tex, Tag 09B1, lemma-compare-derived (2)
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses).

The published fixed-ring presentation is used through its canonical coefficient
realization. Index n denotes the positive exponent n+1. No level is omitted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Canonical identity restriction on sheaves, given by identity section maps.
Source: Stacks 06YY, unit balancing in the coefficient refinement of Tag 09B1
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
def normalizedOriginRestrictionUnit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] (φ : R →+* R) (hφ : φ = RingHom.id R) :
    Sheaf.restrictScalars J φ ≅ 𝟭 (Sheaf J (ModuleCat.{u + 1} R)) :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId' φ hφ) ≪≫
        F.obj.rightUnitor))
    (fun {F G} f ↦ by
      apply (fullyFaithfulSheafToPresheaf J _).map_injective
      ext U x
      rfl)

/-- Canonical self-extension unit, the adjunction mate of identity scalar restriction.
It is the derived map x tensor a to ax, not a chosen automorphism.
Source: Stacks 06YY, unit balancing in the coefficient refinement of Tag 09B1
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
def normalizedOriginScalarUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]
    (φ : R →+* R) (hφ : φ = RingHom.id R) :
    pbcFixedScalarExtension J φ ≅ 𝟭 (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  Adjunction.leftAdjointIdIso (Adjunction.ofIsRightAdjoint _)
    (Functor.mapDerivedCategoryNatIso (normalizedOriginRestrictionUnit J φ hφ) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- The canonical scalar unit at a positive quotient, including the first quotient.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
def normalizedOriginQuotientUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    pbcFixedScalarExtension J (pbcWitnessQuotientMap d n n (le_refl n)) ≅ 𝟭 _ :=
  normalizedOriginScalarUnit J _
    (Scheme.adicQuotientMap_id d.ideal ⟨n + 1, Nat.succ_pos n⟩)

/-- Canonical reassociation for three quotient levels. This is the published
scalar-extension composition comparison, with the actual quotient-factor identity.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
def normalizedOriginQuotientComp
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (k m n : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) :
    pbcFixedScalarExtension J (pbcWitnessQuotientMap d k m hmk) ⋙
        pbcFixedScalarExtension J (pbcWitnessQuotientMap d m n hnm) ≅
      pbcFixedScalarExtension J (pbcWitnessQuotientMap d k n (hnm.trans hmk)) :=
  pbcFixedScalarExtensionComp J _ _ _
    (Scheme.adicQuotientMap_comp d.ideal ⟨k + 1, Nat.succ_pos k⟩
      ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
      (Nat.add_le_add_right hnm 1) (Nat.add_le_add_right hmk 1)).symm

/-- Direct quotient scalar extension, in the published fixed-ring presentation.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
abbrev normalizedOriginReduction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (m n : ℕ) (h : n ≤ m) :=
  pbcFixedScalarExtension J (pbcWitnessQuotientMap d m n h)

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : Scheme.AdicCoefficientDatum A)
  (M : ∀ n : ℕ, PbcWitnessAmbient T d n)
  (hM : ∀ n : ℕ, DerivedCategory.TStructure.t.plus
    ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (M n)))
  (W : ∀ n : ℕ, Scheme.EtaleOriginWitness T (PbcQuotient d n)
    ⟨(finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (M n), hM n⟩)
  (rho : ∀ (m n : ℕ) (h : n ≤ m),
    (normalizedOriginReduction (Scheme.ProEt.topology T) d m n h).obj (M m) ≅ M n)

/-- The required equation for a lift of a supplied normalization. Its source is
identified using the inverse of the canonical comparison-reduction mate.
Source: Stacks 07A4 and Tag 09B1, coefficient refinement of the blueprint's witness sentence
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
def NormalizedOriginCompatibility (m n : ℕ) (h : n ≤ m)
    (beta : (normalizedOriginReduction T.smallEtaleTopology d m n h).obj (W m).L.obj ≅
      (W n).L.obj) : Prop :=
  (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
      beta.hom ≫ (pbcFixedOriginAlpha T (PbcQuotient d n) (M n) (hM n) (W n)).hom =
    (pbcComparisonReduction T (pbcWitnessQuotientMap d m n h)).inv.app (W m).L.obj ≫
      (normalizedOriginReduction (Scheme.ProEt.topology T) d m n h).map
        (pbcFixedOriginAlpha T (PbcQuotient d m) (M m) (hM m) (W m)).hom ≫ (rho m n h).hom

/-- Chosen bounded-below etale origins lift every normalization uniquely, with unit
and quotient-cocycle compatibility. There is no common bound, constructibility, or
finite Tor-dimension assumption. The natural number n denotes P_(n+1).
Source: blueprint main-20261015, proper base change,
prop-weil-pbc-preservation-constructible.proof.md, compatible witness sentence;
Stacks Project Tag 09B1, lemma-compare-derived (2), with coefficient-reduction refinement
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses).

Proof plan, following all six steps of the node:
1. Compute coefficient reduction by a K-flat resolution with flat terms, using
lem-pur-derived-change-of-rings. The canonical inverse-image tensor comparison of
lem-weil-pbc-ringed-topoi-derived-tensor-pullback identifies inverse image of the etale
reduction with reduction of inverse image, including its final quotient action.
2. The extension of a K-flat complex to a quotient remains K-flat over that quotient:
tensoring it with an acyclic quotient complex is the original K-flat tensor after
restriction. Ordinary balancing therefore computes the canonical comparisons. For
three quotients both paths send ((x tensor a) tensor b) to x tensor q(a)b. This proves
naturality, the unit x tensor a to ax, and coherence without quotient flatness.
3. Compose the tensor comparison, the reduction of the retained origin isomorphism,
and rho. Its target is M_n, hence bounded below. Exact comparison commutes with
cohomology. The invertible sheaf-level unit from
prop-weil-pbc-site-comparison-finite-level reflects zero cohomology, so the etale
reduction is bounded below. The bound may depend on n and no uniform interval is used.
4. Both etale objects now lie in D+. Full faithfulness from
thm-weil-pbc-site-comparison uniquely lifts the resulting comparison isomorphism.
Lift its inverse too; faithfulness proves the inverse identities and uniqueness.
This is exactly NormalizedOriginCompatibility, with the canonical source comparison.
5. At equal indices the unit comparison and rho_id make the lifted map the identity
under normalizedOriginQuotientUnit; faithfulness proves equality.
6. Apply comparison to the two-stage lift. Naturality and the balancing associator
identify its image with rho_mn after the reduction of rho_km, followed by the reduced
origin isomorphism. The assumed rho cocycle identifies it with the image of beta_kn.
Cancel the invertible origin isomorphism and use faithfulness. This gives the displayed
cocycle under normalizedOriginQuotientComp for every k >= m >= n.
-/
theorem normalizedEtaleOriginWitnesses
    (rho_id : ∀ n : ℕ, (rho n n (le_refl n)).hom =
      (normalizedOriginQuotientUnit (Scheme.ProEt.topology T) d n).hom.app (M n))
    (rho_comp : ∀ (k m n : ℕ) (hnm : n ≤ m) (hmk : m ≤ k),
      (normalizedOriginReduction (Scheme.ProEt.topology T) d m n hnm).map
          (rho k m hmk).hom ≫ (rho m n hnm).hom =
        (normalizedOriginQuotientComp (Scheme.ProEt.topology T) d k m n hnm hmk).hom.app
          (M k) ≫ (rho k n (hnm.trans hmk)).hom) :
    (∀ (m n : ℕ) (h : n ≤ m), DerivedCategory.TStructure.t.plus
      ((normalizedOriginReduction T.smallEtaleTopology d m n h).obj (W m).L.obj)) ∧
    ∃ beta : ∀ (m n : ℕ) (h : n ≤ m),
        (normalizedOriginReduction T.smallEtaleTopology d m n h).obj (W m).L.obj ≅
          (W n).L.obj,
      (∀ (m n : ℕ) (h : n ≤ m),
        NormalizedOriginCompatibility T d M hM W rho m n h (beta m n h)) ∧
      (∀ (m n : ℕ) (h : n ≤ m)
        (beta' : (normalizedOriginReduction T.smallEtaleTopology d m n h).obj (W m).L.obj ≅
          (W n).L.obj),
        NormalizedOriginCompatibility T d M hM W rho m n h beta' → beta' = beta m n h) ∧
      (∀ n : ℕ, (beta n n (le_refl n)).hom =
        (normalizedOriginQuotientUnit T.smallEtaleTopology d n).hom.app (W n).L.obj) ∧
      (∀ (k m n : ℕ) (hnm : n ≤ m) (hmk : m ≤ k),
        (normalizedOriginReduction T.smallEtaleTopology d m n hnm).map
            (beta k m hmk).hom ≫ (beta m n hnm).hom =
          (normalizedOriginQuotientComp T.smallEtaleTopology d k m n hnm hmk).hom.app
            (W k).L.obj ≫ (beta k n (hnm.trans hmk)).hom) := by
  sorry

end AlgebraicGeometry.ProEtale
