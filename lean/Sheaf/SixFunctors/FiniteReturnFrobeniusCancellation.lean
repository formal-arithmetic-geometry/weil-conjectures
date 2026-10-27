/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.SixFunctors.GraphFrobeniusPointExchange
public import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.KFlatRingedToposPullback

import Sheaf.AlgebraicGeometry.FrobeniusDetailed
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
import Sheaf.AlgebraicGeometry.FrobeniusFactorization
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.PointProEtaleSectionsExact
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Finite return-square cancellation of absolute Frobenius

Source: main-20261015, prop-trf-karoubi-independence.proof.md, final sentence;
Stacks Project, Tag 0F6W (blueprint: lem-trf-finite-return-frobenius-cancellation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option compiler.extract_closed false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- The specified m-th geometric Frobenius of the point.
Source: finite-return convention (blueprint: lem-trf-finite-return-frobenius-cancellation). -/
abbrev returnBasePower (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ) :
    (Spec (.of T.datum.k)) ⟶ (Spec (.of T.datum.k)) :=
  HPow.hPow (α := End (Spec (.of T.datum.k))) (frobeniusPointIso T.datum).hom m

/-- A power of the specified point automorphism is an isomorphism.
This directly applies the existing is-unit/is-iso equivalence and closure under powers.
Source: finite-return convention (blueprint: lem-trf-finite-return-frobenius-cancellation). -/
instance returnBasePowerIsIso (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ) :
    IsIso (T.returnBasePower m) :=
  (isUnit_iff_isIso (T.returnBasePower m)).mp
    (((isUnit_iff_isIso (End.of (frobeniusPointIso T.datum).hom)).mpr
      (inferInstanceAs (IsIso (frobeniusPointIso T.datum).hom))).pow m)

/-- The prescribed absolute Frobenius, at exponent am.
Source: Stacks Tag 0F6W (blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnAbsolute (T : TraceFormulaCoefficientConventions.{u})
    {W : Scheme.{u}} (f : W ⟶ Spec (.of T.datum.k₀)) (m : ℕ) : W ⟶ W :=
  W.iterateFrobenius T.datum.prime (T.datum.model_characteristic f) (T.datum.a * m)

/-- The adjunction-normalized Frobenius trivialization with explicit finite coefficients.
Source: Stacks Tag 0F6W
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnAbsoluteTrivialization (p : ℕ) (hp : p.Prime)
    (A : Type u) [CommRing A] [Finite A] (W : Scheme.{u})
    (hW : (p : Γ(W, ⊤)) = 0) (b : ℕ) :
    sfIntrinsicPullback A (W.iterateFrobenius hp hW b) ≅ 𝟭 _ :=
  (openSquarePullbackModel A (W.iterateFrobenius hp hW b)).symm ≪≫
    (absoluteFrobenius_proEtale_trivialization_pullback p hp A).choose_spec.2.choose_spec.2.choose
      W ⟨hp, natCast_eq_zero_of_natCast_top_eq_zero hW⟩ b

/-- The actual adjoint-normalized trivialization, in intrinsic pullback coordinates.
The relative-Frobenius projections and the sectionwise adjunction-unit equation in the
recorded theorem determine this map. Its selection does not choose an arbitrary iso.
Source: Stacks Tag 0F6W (blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnTau (T : TraceFormulaCoefficientConventions.{u})
    {W : Scheme.{u}} (f : W ⟶ Spec (.of T.datum.k₀)) (m : ℕ) :
    sfIntrinsicPullback T.coefficientRing (T.returnAbsolute f m) ≅ 𝟭 _ :=
  returnAbsoluteTrivialization T.datum.p T.datum.prime T.coefficientRing W
    (T.datum.model_characteristic f) (T.datum.a * m)

attribute [local irreducible] returnTau

/-- Canonical composition followed by a specified trivialization, for arbitrary finite
coefficients. Keeping the coefficient ring explicit retains the same scalar structures.
Source: the construction of kappa
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnTrivializedComposition (A : Type u) [CommRing A] [Finite A]
    {X : Scheme.{u}} (φ H g : X ⟶ X) (w : φ = H ≫ g)
    (τ : sfIntrinsicPullback A H ≅ 𝟭 _) :
    sfIntrinsicPullback A φ ⟶ sfIntrinsicPullback A g :=
  eqToHom (congrArg (sfIntrinsicPullback A) w) ≫
    (sfIntrinsicPullbackComp A H g).hom ≫
      Functor.whiskerLeft (sfIntrinsicPullback A g) τ.hom ≫
        (Functor.rightUnitor _).hom

/-- The normalized kappa on module sheaves: the factorization compositor followed by tau_X.
Source: the specified multiplicative comparison
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnKappa (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ)
    (w : T.datum.schemeFrobeniusIterate T.X₀ m =
      T.returnAbsolute (W := T.geometricBaseChange) (T.structureMap ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m ≫
      HPow.hPow (α := End T.geometricBaseChange)
        (T.datum.geometricGaloisFrobenius T.X₀) m) :
    sfIntrinsicPullback T.coefficientRing (T.datum.schemeFrobeniusIterate T.X₀ m) ⟶
      sfIntrinsicPullback T.coefficientRing
        (HPow.hPow (α := End T.geometricBaseChange)
          (T.datum.geometricGaloisFrobenius T.X₀) m) :=
  returnTrivializedComposition T.coefficientRing
    (T.datum.schemeFrobeniusIterate T.X₀ m)
    (T.returnAbsolute (W := T.geometricBaseChange) (T.structureMap ≫
      Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m)
    (HPow.hPow (α := End T.geometricBaseChange)
      (T.datum.geometricGaloisFrobenius T.X₀) m) w
    (T.returnTau (W := T.geometricBaseChange) (T.structureMap ≫
      Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m)

/-- The already recorded unit-preserving comparison at positive finite level.
Source: Stacks Tag 00YV
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnPointChainModel (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    integralOperationsLevelPullback l E (frobeniusPointIso D).hom n ≅
      @sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) _
        (Padic.finite_coefficientExtensionRing l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n))) _ _ (frobeniusPointIso D).hom := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  exact inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
    (Padic.coefficientExtensionRing l E (n + 1))

/-- The recorded restriction--insertion--coefficient-unit map on complexes at level n+1.
The parameters are kept explicit to preserve the recorded scalar instances.
Source: finite point transport (blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnPointChainRaw (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (N : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :=
  frobeniusPointFiniteSigma D l E n N ≫
    ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).map (inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n N) ≫
    ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex
        (returnPointChainModel D l E n).hom (.up ℤ)).app N)

/-- Positive-level specialization of the recorded chain map; zero is excluded only by
its explicit contradiction with hn. No field or coefficient data are chosen here.
Source: the finite positive-level convention
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnPointChainPositive (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (n : ℕ) → (hn : 1 ≤ n) →
    (N : CochainComplex (proEtaleRingModules (Spec (.of D.k))
      (proEtaleConstantRing (Spec (.of D.k)) (Padic.coefficientExtensionRing l E n))) ℤ) →
    ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex
      (.up ℤ)).obj N ⟶
    ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex
      (.up ℤ)).obj
        (((@sfIntrinsicPullback (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n hn) _ _
            (frobeniusPointIso D).hom).mapHomologicalComplex (.up ℤ)).obj N)
  | 0, hn, _ => False.elim (Nat.not_succ_le_zero 0 hn)
  | n + 1, _, N => returnPointChainRaw D l E n N

/-- The same specified one-step point chain map at the fixed positive level.
Source: finite point transport (blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnPointChainOne (T : TraceFormulaCoefficientConventions.{u}) :=
  returnPointChainPositive T.datum T.coefficients.l T.coefficientField T.level T.level_pos

/-- The exact intrinsic pullback applied to cochain complexes.
Source: the specified ordinary representatives of derived pullback
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnComplexPullback (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (sfIntrinsicPullback A f).mapHomologicalComplex (.up ℤ)

/-- Identity comparison on those representatives, including the complex identity comparison.
Source: canonical identity pullback
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnComplexPullbackId (A : Type u) [CommRing A] [Finite A] (X : Scheme.{u}) :
    returnComplexPullback A (𝟙 X) ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (sfIntrinsicPullbackId A X) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)

/-- Composition comparison on the exact ordinary representatives.
Source: canonical composition pullback
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnComplexPullbackComp (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    returnComplexPullback A (f ≫ g) ≅
      returnComplexPullback A g ⋙ returnComplexPullback A f :=
  (Functor.mapHomologicalComplexCompIso (sfIntrinsicPullbackComp A f g).symm (.up ℤ)).symm

/-- Iteration of specified fibre maps with specified identity and composition comparisons.
This is ordinary categorical composition, with no choice of maps or normalization.
Source: the definition of I^(j)
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnTransportPowers (C : Type (u + 2)) [Category.{u + 1} C]
    (D : Type (u + 2)) [Category.{u + 1} D] (Γ : C ⥤ D)
    (B : C ⥤ C) (F : ℕ → C ⥤ C)
    (e0 : F 0 ≅ 𝟭 C) (eSucc : ∀ m : ℕ, F (m + 1) ≅ B ⋙ F m)
    (iota : ∀ N : C, Γ.obj N ⟶ Γ.obj (B.obj N)) :
    (m : ℕ) → (N : C) → Γ.obj N ⟶ Γ.obj ((F m).obj N)
  | 0, N => Γ.map (e0.inv.app N)
  | m + 1, N => iota N ≫
    returnTransportPowers C D Γ B F e0 eSucc iota m (B.obj N) ≫
      Γ.map ((eSucc m).inv.app N)

/-- Successive specified point chain maps with the ordinary canonical compositors.
The zero case is the canonical identity-pullback comparison, so no scalar is chosen.
Source: finite-return definition of I^(j)
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnPointChainPowerRaw (k : Type u) [Field k] (A : Type u) [CommRing A] [Finite A]
    (h : Spec (.of k) ⟶ Spec (.of k))
    (iota : ∀ N : CochainComplex
      (proEtaleRingModules (Spec (.of k)) (proEtaleConstantRing (Spec (.of k)) A)) ℤ,
      ((pointFiniteSections k A).mapHomologicalComplex (.up ℤ)).obj N ⟶
        ((pointFiniteSections k A).mapHomologicalComplex (.up ℤ)).obj
          ((returnComplexPullback A h).obj N)) :=
  returnTransportPowers _ _ ((pointFiniteSections k A).mapHomologicalComplex (.up ℤ))
    (returnComplexPullback A h)
    (fun m ↦ returnComplexPullback A ((End.of h) ^ m))
    (returnComplexPullbackId A (Spec (.of k)))
    (fun m ↦ eqToIso (congrArg (fun t ↦
        returnComplexPullback A t) (pow_succ' (End.of h) m)) ≪≫
      returnComplexPullbackComp A ((End.of h) ^ m) h)
    iota

/-- The canonical point powers specialized to the recorded coefficient datum.
Source: the specified successive point transport
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnPointChainPower (T : TraceFormulaCoefficientConventions.{u}) :=
  returnPointChainPowerRaw T.datum.k T.coefficientRing (frobeniusPointIso T.datum).hom
    T.returnPointChainOne

/-- The fixed-point comparison on complexes, with its explicit composition identification.
Source: canonical pullback composition
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnFixedChain (A : Type u) [CommRing A] [Finite A] {S X : Scheme.{u}}
    (z : S ⟶ X) (f : X ⟶ X) (w : z ≫ f = z)
    (K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) :=
  eqToHom (congrArg (fun t ↦ ((sfIntrinsicPullback A t).mapHomologicalComplex (.up ℤ)).obj K)
    w.symm) ≫
    (Functor.mapHomologicalComplexCompIso (sfIntrinsicPullbackComp A z f).symm
      (.up ℤ)).inv.app K

/-- The return-square comparison on complexes, including both composition identifications.
Source: canonical pullback composition
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnSquareChain (A : Type u) [CommRing A] [Finite A] {S X : Scheme.{u}}
    (h : S ⟶ S) (z : S ⟶ X) (g : X ⟶ X) (w : z ≫ g = h ≫ z)
    (K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (sfIntrinsicPullback A z ⋙ sfIntrinsicPullback A h)) (.up ℤ)).hom.app K ≫
    (NatIso.mapHomologicalComplex (sfIntrinsicSquarePullback A h z z g w.symm)
      (.up ℤ)).hom.app K ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (sfIntrinsicPullback A g ⋙ sfIntrinsicPullback A z)) (.up ℤ)).inv.app K

/-- The site restriction along h, from (s,h) to the final object (s,id).
Source: the final-object formula
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnRestriction (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ) :
    (proEtaleIsoPostcompose (T.returnBasePower m)).obj (ProEt.mk (𝟙 (Spec (.of T.datum.k)))) ⟶
      ProEt.mk (𝟙 (Spec (.of T.datum.k))) :=
  (ProEt.forget (Spec (.of T.datum.k))).preimage (Over.homMk (T.returnBasePower m))

/-- Restriction along absolute Frobenius, in the opposite direction to res_(g_s^m).
Source: the final-object inverse-restriction formula
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnRestrictionInverse (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ)
    (w : T.returnAbsolute
        (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m ≫
      T.returnBasePower m = 𝟙 (Spec (.of T.datum.k))) :
    ProEt.mk (𝟙 (Spec (.of T.datum.k))) ⟶
      (proEtaleIsoPostcompose (T.returnBasePower m)).obj
        (ProEt.mk (𝟙 (Spec (.of T.datum.k)))) :=
  (ProEt.forget (Spec (.of T.datum.k))).preimage
    (Over.homMk (T.returnAbsolute
      (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m) w)

/-- The distinguished inverse-image insertion followed by the coefficient unit,
in the intrinsic presentation fixed by its adjunction unit. It is a function on sections;
no choice of a fibre isomorphism or scalar is made.
Source: the finite-return final-object formula
(blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnSectionInsertion (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ)
    (N : proEtaleRingModules (Spec (.of T.datum.k))
      (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing))
    (x : N.val.obj (op ((proEtaleIsoPostcompose (T.returnBasePower m)).obj
      (ProEt.mk (𝟙 (Spec (.of T.datum.k))))))) :
    ((sfIntrinsicPullback T.coefficientRing (T.returnBasePower m)).obj N).val.obj
      (op (ProEt.mk (𝟙 (Spec (.of T.datum.k))))) :=
  ((sfIntrinsicPullback T.coefficientRing (T.returnBasePower m)).obj N).val.map
    (proEtaleIsoCommaArrow (T.returnBasePower m) (ProEt.mk (𝟙 (Spec (.of T.datum.k))))).op
    (((sfIntrinsicConstantModuleAdjunction (T.returnBasePower m) T.coefficientRing).unit.app
      N).val.app
        (op ((proEtaleIsoPostcompose (T.returnBasePower m)).obj
          (ProEt.mk (𝟙 (Spec (.of T.datum.k)))))) x)

/-- The normalized inverse-absolute-Frobenius point map before localization.
Source: final-object cancellation (blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnPointAbsolute (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ)
    (w : T.returnAbsolute
        (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m ≫
      T.returnBasePower m = 𝟙 (Spec (.of T.datum.k))) :
    𝟭 (proEtaleRingModules (Spec (.of T.datum.k))
      (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing)) ⟶
      sfIntrinsicPullback T.coefficientRing (T.returnBasePower m) :=
  (sfIntrinsicPullbackId T.coefficientRing (Spec (.of T.datum.k))).inv ≫
    returnTrivializedComposition T.coefficientRing (𝟙 (Spec (.of T.datum.k)))
      (T.returnAbsolute
        (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m)
      (T.returnBasePower m) w.symm
      (T.returnTau (Spec.map (CommRingCat.ofHom
        (algebraMap T.datum.k₀ T.datum.k))) m)

/-- The already selected multiplicative comparison in the same intrinsic coordinates
as point transport. Both coordinate maps preserve the specified adjunction units.
Source: the prescribed kappa (blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnDerivedKappa (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ) (hm : 1 ≤ m) :
    sfIntrinsicDerivedPullback T.coefficientRing (T.datum.schemeFrobeniusIterate T.X₀ m) ⟶
      sfIntrinsicDerivedPullback T.coefficientRing
        (HPow.hPow (α := End T.geometricBaseChange)
          (T.datum.geometricGaloisFrobenius T.X₀) m) :=
  (openSquareDerivedPullbackModel T.coefficientRing _).inv ≫
    (T.selectedSchemeGaloisComparison T.X₀ m hm).hom ≫
      (openSquareDerivedPullbackModel T.coefficientRing _).hom

/-- Canonical rho before applying the recorded point sections functor.
Source: Phi^m z = z (blueprint: lem-trf-finite-return-frobenius-cancellation). -/
def returnDerivedFixed (T : TraceFormulaCoefficientConventions.{u})
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) (m : ℕ)
    (w : z ≫ T.datum.schemeFrobeniusIterate T.X₀ m = z) :
    sfIntrinsicDerivedPullback T.coefficientRing z ⟶
      sfIntrinsicDerivedPullback T.coefficientRing
        (T.datum.schemeFrobeniusIterate T.X₀ m) ⋙
          sfIntrinsicDerivedPullback T.coefficientRing z :=
  eqToHom (congrArg (sfIntrinsicDerivedPullback T.coefficientRing) w.symm) ≫
    (sfIntrinsicDerivedPullbackComp T.coefficientRing z
      (T.datum.schemeFrobeniusIterate T.X₀ m)).hom

/-- Finite return-square cancellation, with the arbitrary-sheaf final-object formula,
the successive chain transport normalization, the specified derived comparison and
its equality already on flat-term K-flat representatives. All paths use the canonical
composition comparisons; no scalar can be inserted.

Source: main-20261015, prop-trf-karoubi-independence.proof.md, last sentence;
Stacks Project, Tag 0F6W (blueprint: lem-trf-finite-return-frobenius-cancellation).

Proof, following the ten steps in the DAG:
1. Evaluate z on affine tensors by a tensor b mapping to e(a)b. Because e(a) lies
   in F_(q^m), the three scheme identities follow. The inverse Frobenius convention
   gives rh = hr = id, and prop-trf-frobenius-factorization gives Phi^m = H g^m.
2. For automorphism h, use lem-weil-proetale-isomorphism-inverse-image. The graph
   index (U,hu) is initial in the inverse-image comma category; its insertion is
   the sectionwise identification. Coefficient transport sends x tensor a to ax.
3. Ordinary pullback composition identifies successive graph insertions and sends
   x tensor a to (x tensor 1) tensor a. The coefficient composition equality is
   lem-trf-constant-coefficient-composition; exact termwise descent gives the
   compositors of lem-weil-pbc-proetale-derived-pullback-composition.
4. The unit equation defining tau_s, evaluated at (s,r), identifies tau_s with
   restriction along r inverse. The relative Frobenius at this object is r.
5. Apply this to h*N. The identifications hr = id and r inverse = h make its
   final-object value exactly res_h, followed by the distinguished insertion.
   No constructibility or flatness of this sheaf is needed.
6. In def-weil-frobenius-point-transport each step is res_(g_s) followed by that
   insertion and tensor unit. Induction, with identity at zero, identifies the
   successive chain maps with res_(g_s^m), using the same compositors as in Step 3.
7. Put P=z*, R=r*, V=h*, S=H*, T=(g^m)*. The canonical square comparisons give
   d a = R(v)e: both are the comparison for g^m H z = z. This is the triple
   identity of lem-trf-derived-pullback-coherence. It holds termwise on generators.
8. Apply lem-pur-frobenius-trivialization-pullback to z and exponent am:
   P(tau_X) = tau_s d. Naturality of tau_s gives tau_s R(v) = v tau_s.
9. Substituting kappa = tau_X c and Step 7 gives P(kappa)b = v tau_s e.
   Apply the exact point sections functor of def-weil-finite-coefficient-point
   and Steps 5--6 to obtain J(kappa) rho = Fib(v) I^(m).
10. All maps are specified ordinary module maps, and commute with differentials.
    Choose the flat-term K-flat representative by lem-pc-kflat-resolution;
    lem-weil-pbc-ringed-pullback-preserves-kflat preserves that property.
    Constant-coefficient pullback and point sections are exact. The localization
    universal property carries the chain equality to the derived equality.
    Restrictions, coefficient comparisons and insertions all preserve 1.
-/
theorem finiteReturn_frobenius_cancellation
    (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ) (hm : 1 ≤ m)
    (y : T.datum.extensionPoints T.X₀ m hm) :
    ∃ wPhi : localExtensionPoint T.datum T.X₀ m hm y ≫
        T.datum.schemeFrobeniusIterate T.X₀ m = localExtensionPoint T.datum T.X₀ m hm y,
    ∃ wH : localExtensionPoint T.datum T.X₀ m hm y ≫
        T.returnAbsolute (W := T.geometricBaseChange) (T.structureMap ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m =
      T.returnAbsolute
          (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m ≫
        localExtensionPoint T.datum T.X₀ m hm y,
    ∃ wG : localExtensionPoint T.datum T.X₀ m hm y ≫
        HPow.hPow (α := End T.geometricBaseChange)
          (T.datum.geometricGaloisFrobenius T.X₀) m =
      T.returnBasePower m ≫ localExtensionPoint T.datum T.X₀ m hm y,
    ∃ wRH : T.returnAbsolute
        (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m ≫
      T.returnBasePower m = 𝟙 (Spec (.of T.datum.k)),
      (T.returnBasePower m ≫ T.returnAbsolute
        (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m =
          𝟙 (Spec (.of T.datum.k))) ∧
    ∃ wFactor : T.datum.schemeFrobeniusIterate T.X₀ m =
      T.returnAbsolute (W := T.geometricBaseChange) (T.structureMap ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m ≫
        HPow.hPow (α := End T.geometricBaseChange)
          (T.datum.geometricGaloisFrobenius T.X₀) m,
    (∀ (N : proEtaleRingModules (Spec (.of T.datum.k))
        (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing))
      (x : N.val.obj (op (ProEt.mk (𝟙 (Spec (.of T.datum.k)))))),
      ((T.returnPointAbsolute m wRH).app N).val.app
          (op (ProEt.mk (𝟙 (Spec (.of T.datum.k))))) x =
        T.returnSectionInsertion m N (N.val.map (T.returnRestriction m).op x) ∧
      N.val.map (T.returnRestrictionInverse m wRH).op
        (N.val.map (T.returnRestriction m).op x) = x) ∧
    (∀ (N : proEtaleRingModules (Spec (.of T.datum.k))
        (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing))
      (x : N.val.obj (op ((proEtaleIsoPostcompose (T.returnBasePower m)).obj
        (ProEt.mk (𝟙 (Spec (.of T.datum.k))))))),
      N.val.map (T.returnRestriction m).op
        (N.val.map (T.returnRestrictionInverse m wRH).op x) = x) ∧
    (∀ N : CochainComplex
        (proEtaleRingModules (Spec (.of T.datum.k))
          (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing)) ℤ,
      ((pointFiniteSections T.datum.k T.coefficientRing).mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (T.returnPointAbsolute m wRH) (.up ℤ)).app N) =
        T.returnPointChainPower m N) ∧
    (∀ K : T.boundedConstructible.FullSubcategory,
      T.graphPointFibre.map
          ((T.returnDerivedFixed (localExtensionPoint T.datum T.X₀ m hm y) m wPhi).app K.obj) ≫
        T.graphPointFibre.map
          ((sfIntrinsicDerivedPullback T.coefficientRing
            (localExtensionPoint T.datum T.X₀ m hm y)).map
              ((T.returnDerivedKappa m hm).app K.obj)) =
      T.graphPointTransportPower m
          ((sfIntrinsicDerivedPullback T.coefficientRing
            (localExtensionPoint T.datum T.X₀ m hm y)).obj K.obj) ≫
        T.graphPointFibre.map
          ((sfIntrinsicDerivedSquarePullback T.coefficientRing (T.returnBasePower m)
            (localExtensionPoint T.datum T.X₀ m hm y)
            (localExtensionPoint T.datum T.X₀ m hm y)
            (HPow.hPow (α := End T.geometricBaseChange)
              (T.datum.geometricGaloisFrobenius T.X₀) m) wG.symm).hom.app K.obj)) ∧
    (∀ K : CochainComplex
        (proEtaleRingModules T.geometricBaseChange
          (proEtaleConstantRing T.geometricBaseChange T.coefficientRing)) ℤ,
      T.boundedConstructible (DerivedCategory.Q.obj K) →
      CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology T.geometricBaseChange)
        (R := proEtaleConstantRing T.geometricBaseChange T.coefficientRing) K →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology T.geometricBaseChange)
        (R := proEtaleConstantRing T.geometricBaseChange T.coefficientRing) (K.X i)) →
      ((pointFiniteSections T.datum.k T.coefficientRing).mapHomologicalComplex (.up ℤ)).map
          (returnFixedChain T.coefficientRing (localExtensionPoint T.datum T.X₀ m hm y)
            (T.datum.schemeFrobeniusIterate T.X₀ m) wPhi K) ≫
        ((pointFiniteSections T.datum.k T.coefficientRing).mapHomologicalComplex (.up ℤ)).map
          (((sfIntrinsicPullback T.coefficientRing
            (localExtensionPoint T.datum T.X₀ m hm y)).mapHomologicalComplex (.up ℤ)).map
              ((NatTrans.mapHomologicalComplex (T.returnKappa m wFactor) (.up ℤ)).app K)) =
      T.returnPointChainPower m
          (((sfIntrinsicPullback T.coefficientRing
            (localExtensionPoint T.datum T.X₀ m hm y)).mapHomologicalComplex (.up ℤ)).obj K) ≫
        ((pointFiniteSections T.datum.k T.coefficientRing).mapHomologicalComplex (.up ℤ)).map
          (returnSquareChain T.coefficientRing (T.returnBasePower m)
            (localExtensionPoint T.datum T.X₀ m hm y)
            (HPow.hPow (α := End T.geometricBaseChange)
              (T.datum.geometricGaloisFrobenius T.X₀) m) wG K)) := by
  sorry

end WeilConjectures.TraceFormulaCoefficientConventions
