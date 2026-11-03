/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomThickLocus
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
public import WeilConjectures.AlgebraicGeometry.GeneralCoefficientTensor.GeneralEtaleTensorComparison

/-! # Canonical maps for general étale coefficient pairing change

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps).

This module records the ordinary small-étale coefficient maps used by the pairing
change statement.  The direct-image map is the scalar mate of the published
inverse-image/direct-image adjunction, and scalar extension is the fixed left
adjoint of derived restriction of scalars on the small étale site.  No
finite-direct-image or witness-compatibility module is imported here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.GeneralCoefficientPairingChange

/-- The fixed ordinary derived scalar extension `F_T = - ⊗_A^L B` on a small étale site:
the left adjoint of exact derived restriction of scalars (lem-pur-derived-change-of-rings).
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
abbrev fixedCoefficientDerivedScalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension T.smallEtaleTopology φ

/-- Short notation for the fixed scalar extension `F_T` used by all maps below.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
abbrev scalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  fixedCoefficientDerivedScalarExtension φ T

/-- The canonical ordinary direct-image coefficient comparison family, the counit-normalized
scalar mate of lem-coef-general-finite-direct-image; its `etale` component is `c_f`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
abbrev directImageMaps := AlgebraicGeometry.FiniteCoefficientOrdinary.directImageMaps

/-- The geometric transpose of the specified ordinary direct-image family.
Source: thm-coef-finite-hom, paragraph 4, and the scalar-unit normalization
`directImageMaps.etale_counit` (blueprint: def-coef-general-etale-pairing-maps).
This construction uses just the two ordinary geometric adjunctions. -/
def scalarPullComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    scalarExtension φ X ⋙ L(upperStar (ModuleCat B) f) ⟶
      L(upperStar (ModuleCat A) f) ⋙ scalarExtension φ Y :=
  ((mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat B) f)).symm
      (TwoSquare.mk _ _ _ _ (directImageMaps.etale φ f))).natTrans

/-- The ordinary open/scalar isomorphism, fixed by uniqueness of the composite
left adjoints to the actual coefficient restrictions and exact open restrictions.
Source: Stacks 03EL and 06YY (blueprint: def-coef-general-etale-pairing-maps). -/
def fixedOpenScalarExtension {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedExtension (A := A) j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ derivedExtension (A := B) j :=
  Adjunction.leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).comp
      (FiniteCoefficientOrdinary.scalarAdjunction X.smallEtaleTopology φ))
    (((FiniteCoefficientOrdinary.scalarAdjunction U.smallEtaleTopology φ).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat B) j)).ofNatIsoRight
        (openDerivedRestrictScalarsIso φ j))

/-- The normalized fixed-coefficient tensor comparison, computed on K-flat models.
Source: Stacks 07A4 (blueprint: def-coef-general-etale-pairing-maps). -/
abbrev tensorComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (T : Scheme.{u}) (φ : A →+* B) := GeneralCoefficientTensor.comparison φ T

/-- Compact support `s_! = g_* j_!` for `s = g j`, `j` open and `g` closed
(def-amb-etale-compact-support).
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
abbrev shriek (A : Type (u + 1)) [CommRing A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j] :=
  derivedExtension (A := A) j ⋙ R(lowerStar (ModuleCat A) g)

/-- Ordinary direct image `R s_* = R g_* R j_*` for `s = g j`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
abbrev star (A : Type (u + 1)) [CommRing A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) (j : S ⟶ Z) :=
  R(lowerStar (ModuleCat A) j) ⋙ R(lowerStar (ModuleCat A) g)

/-- Exceptional inverse image `s^! = j^* R g^!`, with `R g^!` the right adjoint of `R g_*`
for the closed immersion `g` (lem-exc-closed-ambient).
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
abbrev exceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z)
    [IsOpenImmersion j] :=
  (R(lowerStar (ModuleCat A) g)).rightAdjoint ⋙ derivedRestriction (A := A) j

/-- The exceptional counit `ε_s : s_! s^! M → M` of the composite adjunction
`j_! ⊣ j^*` followed by `R g_* ⊣ R g^!`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
def counit (A : Type (u + 1)) [CommRing A] [Finite A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z)
    [IsOpenImmersion j] (M : DerivedCategoryModule A X) :
    (shriek A g j).obj ((exceptional A g j).obj M) ⟶ M :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).comp
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat A) g)))).counit.app M

/-- The ordinary counit `α : s^* R s_* Q → Q` of the composite adjunction
`g^* ⊣ R g_*` followed by `j^* ⊣ R j_*`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
def ordinaryCounit (A : Type (u + 1)) [CommRing A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) (j : S ⟶ Z)
    (Q : DerivedCategoryModule A S) :
    L(upperStar (ModuleCat A) j).obj
      (L(upperStar (ModuleCat A) g).obj ((star A g j).obj Q)) ⟶ Q :=
  ((derivedUpperStarLowerStarAdjunction (ModuleCat A) g).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat A) j)).counit.app Q

/-- The first pairing arrow `P(T, L) : s_! L ⊗ T → s_!(L ⊗ s^* T)`: the closed projection map
of def-kun-projection-formula-map for `g` followed by `R g_*` of the inverse of the open
projection isomorphism for `j` (lem-coef-etale-open-tensor).
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
def projection (A : Type (u + 1)) [CommRing A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (T : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat A) X).obj ((shriek A g j).obj L)).obj T ⟶
      (shriek A g j).obj
        (((derivedTensor (ModuleCat A) S).obj L).obj
          (L(upperStar (ModuleCat A) j).obj (L(upperStar (ModuleCat A) g).obj T))) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat A) g).app
      ((derivedExtension (A := A) j).obj L)).app T ≫
    R(lowerStar (ModuleCat A) g).map
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat A) j).inv.app L).app
        (L(upperStar (ModuleCat A) g).obj T))

/-- The internal adjunction `I : R s_* H(L, s^! M) → H(s_! L, M)`, the tensor--Hom transpose
of the pairing `ε_s ∘ s_!(ev) ∘ s_!(α ⊗ 1) ∘ P`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
def internalAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z)
    [IsOpenImmersion j] (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) :
    (star A g j).obj
        (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)) ⟶
      ((derivedHom (ModuleCat A) X).obj (op ((shriek A g j).obj L))).obj M :=
  ((derivedTensorHomAdjunction (ModuleCat A) ((shriek A g j).obj L)).homEquiv _ _)
    (projection A g j L _ ≫
      (shriek A g j).map
        (((derivedTensor (ModuleCat A) S).obj L).map
            (ordinaryCounit A g j _) ≫
          (derivedTensorHomAdjunction (ModuleCat A) L).counit.app
            ((exceptional A g j).obj M)) ≫ counit A g j M)

/-- The compact-support comparison `q_s = R g_*(q_j) ∘ c_g : F_X s_! L → s_! F_S L`, with `c_g`
the ordinary direct-image comparison and `q_j` the canonical open comparison
(lem-coef-etale-open-tensor).
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
def compactComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {S Z X : Scheme.{u}} (g : Z ⟶ X) (j : S ⟶ Z)
    [IsOpenImmersion j] (L : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj ((shriek A g j).obj L) ⟶
      (shriek B g j).obj ((scalarExtension φ S).obj L) :=
  (directImageMaps.etale φ g).app ((derivedExtension (A := A) j).obj L) ≫
    R(lowerStar (ModuleCat B) g).map ((fixedOpenScalarExtension φ j).hom.app L)

/-- The ordinary direct-image comparison `c_s = R g_*(c_j) ∘ c_g : F_X R s_* Q → R s_* F_S Q`
of lem-coef-general-finite-direct-image.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
def ordinaryComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {S Z X : Scheme.{u}} (g : Z ⟶ X) (j : S ⟶ Z)
    (Q : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj ((star A g j).obj Q) ⟶
      (star B g j).obj ((scalarExtension φ S).obj Q) :=
  (directImageMaps.etale φ g).app ((R(lowerStar (ModuleCat A) j)).obj Q) ≫
    R(lowerStar (ModuleCat B) g).map ((directImageMaps.etale φ j).app Q)

/-- The evaluation-defined comparison `v_{K,M} : F H_A(K, M) → H_B(F K, F M)`: the
tensor--Hom transpose of `F(ev) ∘ μ` (lem-coef-etale-hom-thick-locus); no invertibility.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
def evaluationComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (K M : DerivedCategoryModule A T) :
    (scalarExtension φ T).obj (((derivedHom (ModuleCat A) T).obj (op K)).obj M) ⟶
      ((derivedHom (ModuleCat B) T).obj (op ((scalarExtension φ T).obj K))).obj
        ((scalarExtension φ T).obj M) :=
  ((derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ T).obj K)).homEquiv _ _)
    ((tensorComparison T φ K _).hom ≫
      (scalarExtension φ T).map ((derivedTensorHomAdjunction (ModuleCat A) K).counit.app M))

/-- The exceptional counit equation `ε_{s,B} ∘ s_!(b) ∘ q_{s,N} = F_X ε_{s,A}` for
`b : F_S s^! M ≅ s^! F_X M`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
def CounitCompatible {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] (M : DerivedCategoryModule A X)
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M)) : Prop :=
  compactComparison φ g j ((exceptional A g j).obj M) ≫
      (shriek B g j).map b.hom ≫ counit B g j ((scalarExtension φ X).obj M) =
    (scalarExtension φ X).map (counit A g j M)

/-- The pairing-change equation
`H_B(q_{s,L}, 1) ∘ I_B ∘ R s_*(H_B(1, b) ∘ u) ∘ c_{s,Q} = v_{s_! L, M} ∘ F_X I_A`,
with `u` the evaluation comparison at `(L, N)`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/thm-coef-finite-hom.proof.md, paragraph 4
(blueprint: def-coef-general-etale-pairing-maps). -/
def PairingChangeEquation {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {S Z X : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j] (L : DerivedCategoryModule A S)
    (M : DerivedCategoryModule A X)
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M)) : Prop :=
  ordinaryComparison φ g j _ ≫
      (star B g j).map
        (evaluationComparison φ S L _ ≫
          ((derivedHom (ModuleCat B) S).obj
            (op ((scalarExtension φ S).obj L))).map b.hom) ≫
      internalAdjunction B g j ((scalarExtension φ S).obj L) ((scalarExtension φ X).obj M) ≫
      ((derivedHom (ModuleCat B) X).map (compactComparison φ g j L).op).app
        ((scalarExtension φ X).obj M) =
    (scalarExtension φ X).map (internalAdjunction A g j L M) ≫
      evaluationComparison φ X ((shriek A g j).obj L) M

end AlgebraicGeometry.Etale.GeneralCoefficientPairingChange
