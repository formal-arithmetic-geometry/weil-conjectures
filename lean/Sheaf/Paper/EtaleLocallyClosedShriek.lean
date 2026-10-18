/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.FiniteCoefficientReductionFlatModel
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.SixFunctors.EtaleOpenTensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# Ordinary étale locally closed exceptional restriction and coefficient change

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
`thm-coef-finite-hom.md`, proof paragraphs 3--4
(blueprint: lem-coef-etale-locally-closed-shriek).

The closed exceptional functor is the ambient ordinary unbounded étale right adjoint.
All scalar functors are ordinary uncompleted scalar extension. The comparisons below
are constructed from the published coefficient map and the specified adjunction counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The ordinary closed exceptional right adjoint supplied by lem-exc-closed-ambient.
Source: blueprint thm-coef-finite-hom, paragraph 3
(blueprint: lem-coef-etale-locally-closed-shriek). -/
abbrev etaleShriekClosedExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g] :=
  (R(lowerStar (ModuleCat.{u + 1} A) g)).rightAdjoint

/-- The fixed ordinary closed exceptional adjunction.
Source: blueprint thm-coef-finite-hom, paragraph 3
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekClosedAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g] :
    R(lowerStar (ModuleCat.{u + 1} A) g) ⊣ etaleShriekClosedExceptional A g :=
  Adjunction.ofIsLeftAdjoint _

/-- The composite ordinary adjunction `g_* j_! ⊣ j^* Rg^!`, with its pasted counit.
This is the locally closed case of the recorded compact-support construction.
Source: blueprint thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekLocallyClosedAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] :
    derivedExtension (A := A) j ⋙ R(lowerStar (ModuleCat.{u + 1} A) g) ⊣
      etaleShriekClosedExceptional A g ⋙ derivedRestriction (A := A) j :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
    (etaleShriekClosedAdjunction A g)

/-- Inverse of the actual coefficient comparison on its isomorphism locus.
The zero extension elsewhere merely makes the formula total; the theorem explicitly
asserts invertibility of this comparison on every input on which it uses the inverse.
Source: blueprint thm-coef-finite-hom, paragraph 3
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekDirectInverse
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z X : Scheme.{u}} (g : Z ⟶ X) (N : DerivedCategoryModule A Z) :
    (R(lowerStar (ModuleCat.{u + 1} B) g)).obj ((scalarExtension φ Z).obj N) ⟶
      (scalarExtension φ X).obj ((R(lowerStar (ModuleCat.{u + 1} A) g)).obj N) :=
  open Classical in
  if h : IsIso (finiteCoefficientDirectImageMap φ g N) then
    @inv _ _ _ _ (finiteCoefficientDirectImageMap φ g N) h
  else 0

/-- The specified closed coefficient map: the exceptional-adjunction transpose of
`c_g⁻¹` followed by scalar extension of the A-exceptional counit.
Source: blueprint thm-coef-finite-hom, paragraph 3
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekClosedCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Z).obj ((etaleShriekClosedExceptional A g).obj M) ⟶
      (etaleShriekClosedExceptional B g).obj ((scalarExtension φ X).obj M) :=
  (etaleShriekClosedAdjunction B g).homEquiv _ _
    (etaleShriekDirectInverse φ g ((etaleShriekClosedExceptional A g).obj M) ≫
      (scalarExtension φ X).map ((etaleShriekClosedAdjunction A g).counit.app M))

/-- Restrict the closed coefficient map, with the canonical scalar/restriction
identification. This is precisely the map `b_s = j^* b_g` under that identification.
Source: blueprint thm-coef-finite-hom, paragraphs 3--4
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekLocallyClosedCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] (M : DerivedCategoryModule A X) :
    (scalarExtension φ S).obj
        ((derivedRestriction (A := A) j).obj ((etaleShriekClosedExceptional A g).obj M)) ⟶
      (derivedRestriction (A := B) j).obj
        ((etaleShriekClosedExceptional B g).obj ((scalarExtension φ X).obj M)) :=
  (openScalarRestriction φ j).hom.app ((etaleShriekClosedExceptional A g).obj M) ≫
    (derivedRestriction (A := B) j).map (etaleShriekClosedCoefficientMap φ g M)

/-- The fixed compact-support coefficient map `g_*(q_j) ∘ c_{g,j_!P}`.
The open comparison is the published natural isomorphism normalized to the identity
on the open stratum, not an arbitrary choice of scalar comparison.
Source: blueprint thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def etaleShriekLocallyClosedSupportMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S Z X : Scheme.{u}} (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j]
    (P : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) g)).obj ((derivedExtension (A := A) j).obj P)) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) g)).obj
        ((derivedExtension (A := B) j).obj ((scalarExtension φ S).obj P)) :=
  finiteCoefficientDirectImageMap φ g ((derivedExtension (A := A) j).obj P) ≫
    (R(lowerStar (ModuleCat.{u + 1} B) g)).map ((openScalarExtension φ j).hom.app P)

/-- All clauses of the ordinary étale locally closed comparison, including naturality
on the specified finite-Tor constructible domains and the counit identity.
The final theorem supplies the existing finite-stage predicate as `ctf`; this parameter
only packages the assertions and introduces no alternative constructibility definition.
Source: blueprint thm-coef-finite-hom, paragraphs 3--4
(blueprint: lem-coef-etale-locally-closed-shriek). -/
def EtaleLocallyClosedShriekComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (ctf : ∀ T : Scheme.{u}, ObjectProperty (DerivedCategoryModule A T))
    {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] : Prop :=
  (∀ N : DerivedCategoryModule A Z, ctf Z N →
    IsIso (finiteCoefficientDirectImageMap φ g N)) ∧
  (∀ M : DerivedCategoryModule A X, ctf X M →
    ctf Z ((etaleShriekClosedExceptional A g).obj M) ∧
    ctf S
      ((derivedRestriction (A := A) j).obj ((etaleShriekClosedExceptional A g).obj M)) ∧
    IsIso (finiteCoefficientDirectImageMap φ g ((etaleShriekClosedExceptional A g).obj M)) ∧
    IsIso (etaleShriekClosedCoefficientMap φ g M) ∧
    IsIso (etaleShriekLocallyClosedCoefficientMap φ g j M) ∧
    etaleShriekLocallyClosedSupportMap φ g j
        ((derivedRestriction (A := A) j).obj ((etaleShriekClosedExceptional A g).obj M)) ≫
      (derivedExtension (A := B) j ⋙ R(lowerStar (ModuleCat.{u + 1} B) g)).map
        (etaleShriekLocallyClosedCoefficientMap φ g j M) ≫
      (etaleShriekLocallyClosedAdjunction B g j).counit.app ((scalarExtension φ X).obj M) =
        (scalarExtension φ X).map ((etaleShriekLocallyClosedAdjunction A g j).counit.app M)) ∧
  (∀ P : DerivedCategoryModule A S, ctf S P →
    IsIso (etaleShriekLocallyClosedSupportMap φ g j P)) ∧
  (∀ (M N : DerivedCategoryModule A X),
    ctf X M → ctf X N →
    ∀ f : M ⟶ N,
      (etaleShriekClosedExceptional A g ⋙ scalarExtension φ Z).map f ≫
          etaleShriekClosedCoefficientMap φ g N =
        etaleShriekClosedCoefficientMap φ g M ≫
          (scalarExtension φ X ⋙ etaleShriekClosedExceptional B g).map f) ∧
  (∀ (M N : DerivedCategoryModule A X),
    ctf X M → ctf X N →
    ∀ f : M ⟶ N,
      (etaleShriekClosedExceptional A g ⋙ derivedRestriction (A := A) j ⋙
          scalarExtension φ S).map f ≫ etaleShriekLocallyClosedCoefficientMap φ g j N =
        etaleShriekLocallyClosedCoefficientMap φ g j M ≫
          (scalarExtension φ X ⋙ etaleShriekClosedExceptional B g ⋙
            derivedRestriction (A := B) j).map f) ∧
  (∀ (P Q : DerivedCategoryModule A S),
    ctf S P → ctf S Q →
    ∀ f : P ⟶ Q,
      (derivedExtension (A := A) j ⋙ R(lowerStar (ModuleCat.{u + 1} A) g) ⋙
          scalarExtension φ X).map f ≫ etaleShriekLocallyClosedSupportMap φ g j Q =
        etaleShriekLocallyClosedSupportMap φ g j P ≫
          (scalarExtension φ S ⋙ derivedExtension (A := B) j ⋙
            R(lowerStar (ModuleCat.{u + 1} B) g)).map f) ∧
  (∀ M : DerivedCategoryModule A X,
    (etaleShriekLocallyClosedAdjunction A g j).counit.app M =
      (R(lowerStar (ModuleCat.{u + 1} A) g)).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).counit.app ((etaleShriekClosedExceptional A g).obj M)) ≫
        (etaleShriekClosedAdjunction A g).counit.app M)

/-- Finite quotient coefficient change commutes with ordinary étale locally closed
exceptional restriction and compact support, with the normalized counit identity.
Source: blueprint thm-coef-finite-hom, proof paragraphs 3--4
(blueprint: lem-coef-etale-locally-closed-shriek).

Proof (the twelve steps of the DAG node):
1. The closed subscheme and the two opens are separated finite type over k: use
   lem-weil-pbc-finite-type-over-noetherian, the Noetherian-open lemma and the
   quasi-compact-open finite-type lemma. The coefficient rings are finite and B is
   a finite A-module since it is a quotient (def-weil-l-adic-coefficient-extension).
2. The complementary open has finite cohomological dimension by
   lem-etale-finite-type-sep-closed-derived-dimension. Its higher images are
   constructible by sbc-thm-finiteness-finite-type. A power of l kills A, since
   l is a unit times a positive power of the uniformizer
   (lem-weil-l-adic-extension-integers-dvr). Apply prop-exc-closed-tor to get
   finite-Tor bounded constructibility of Ng in the ambient ordinary adjunction.
3. Exact inverse image preserves constructibility (prop-constructible-pullback).
   Bounded flat models (lem-sf-flat-model), K-flatness of bounded flat complexes,
   and lem-weil-pbc-ringed-topoi-derived-tensor-pullback give the Tor bounds on
   both open restrictions; lem-coef-etale-open-tensor fixes their scalar comparison.
4. The closed-support equivalence lem-kun-04ca lifts to module sheaves by transporting
   scalar actions. The closed stalk formula and exact conservative geometric stalks
   show that g_* is exact. The inverse-image/direct-image adjunction descends,
   with invertible counit, so derived g_* is fully faithful and reflects isomorphisms.
   On its image, composition with the exceptional counit is a Hom bijection.
5. Apply lem-coef-finite-direct-image to Ng and to the complementary-open restriction
   of M. Its counit normalization fixes the comparisons, including the third terms
   of the closed-support triangles.
6. Transpose the complementary-open unit square. The defining coefficient-counit
   equation and the triangle identity identify both transposes with the identity.
7. Apply the exact scalar functor (lem-pur-derived-change-of-rings) to the A-support
   triangle (lem-exc-closed-support-triangle). Rotate, use TR3, and rotate back.
   The identity on middle terms and the isomorphism on third terms give an isomorphism
   on first terms (lem-sf-triangle-morphism-iso), whose counit composite is F(epsilon_A).
8. The Hom bijection in step 4 identifies that first map with g_*b_g composed with c_g.
   Reflect invertibility to obtain b_g. Its defining adjunction transpose gives naturality.
9. Apply exact restriction to b_g and the canonical open scalar identification to get b_s.
   Extension by zero preserves bounded constructibility (lem-fin-extension-by-zero)
   and finite Tor amplitude by lem-coef-etale-open-tensor and its K-flat models.
10. Compose the degreewise open adjunction with the ambient closed adjunction.
    Its counit is g_*(epsilon_j) followed by epsilon_g. Compose c_g with g_*(q_j)
    to obtain q_s, natural and invertible on the specified domain.
11. Expand q_s, b_s and the pasted counit. Naturality of the closed B-counit moves
    j^*b_g past the open counit; the open coefficient-counit identity removes q_j;
    naturality of c_g then reduces the result to the defining transpose of b_g.
12. For S=Z and j the identity, the open adjunction and comparisons identify with
    identities, giving exactly the closed comparison and its counit equation. -/
theorem etaleLocallyClosedShriekComparisons
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n m : ℕ) (hmn : m ≤ n) (hm : 1 ≤ m)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    {Z S : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] :
    @EtaleLocallyClosedShriekComparisons.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)) inferInstance inferInstance
      (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n (hm.trans hmn)))
      (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E m hm))
      (Scheme.flatModelReductionCoefficientMap l E m n hmn)
      (WeilConjectures.finiteTorConstructibleEtale l E n (hm.trans hmn))
      S Z X g inferInstance j
        inferInstance := by
  sorry

end AlgebraicGeometry.Etale
