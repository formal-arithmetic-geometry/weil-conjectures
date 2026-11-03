/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModIhom
import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFreeTensorLinear
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
public import WeilConjectures.Algebra.Homology.SmoothPurity.InvertibleTensorScalarExtensionDefinitionsSupplement
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Connected.Separation
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
import WeilConjectures.RingTheory.ProEtale.WeakDimension
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.ProperBaseChange.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueQuotient
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueLimit
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality
import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Kummer.PurityFiniteKummerLevel
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
public import WeilConjectures.AlgebraicGeometry.TwistModelComparison

/-! # The canonical Weil maps of condensed coefficient twists

Source: current blueprint, `def-weil-frobenius-coefficient-twists`, order 2855
(blueprint: def-weil-frobenius-coefficient-twists).

The construction is specified by its universal properties, including the root
normalization, every finite projection, scalar extension, tensor powers and
internal duals. The existence-and-uniqueness theorem below postpones only a
proof: its specification fixes all the maps used by the definition. In particular
no unnormalized natural isomorphism or choice of a root generator is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace WeilConjectures

/-- The specified adjoint pullback-of-units map in the upstream root presentation.
Source: the natural Weil isomorphism paragraph
(blueprint: def-weil-frobenius-coefficient-twists). -/
abbrev frobeniusRootMap {X : Scheme.{u}} (g : Aut X) (N : ℕ) :
    (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj
      (rootsOfUnitySheaf X N) ⟶ rootsOfUnitySheaf X N :=
  AlgebraicGeometry.ProEtale.PurityTransport.rootPull g.hom N

/-- The specific degree-one comparisons and their defining universal-property
 equations. Finite maps use alpha tensor the specified root map; integral maps
 are fixed by all projections; rational maps are fixed by their scalar quotient.
 The last three fields separately record precisely the upstream internal Z_l
 tower and its extension to Qbar. Source: natural Weil isomorphism paragraph
 (blueprint: def-weil-frobenius-coefficient-twists). -/
structure FrobeniusDegreeOneMaps (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (g : Aut X) where
  finite : ∀ n : ℕ, (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj
    (coefficientFiniteTwistOne l E X n).X ≅ (coefficientFiniteTwistOne l E X n).X
  integral : (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj
    (coefficientIntegralTwistOne l E X).X ≅ (coefficientIntegralTwistOne l E X).X
  rational : (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj
    (coefficientRationalTwistOne l E X).X ≅ (coefficientRationalTwistOne l E X).X
  tateLevel : ∀ r : ℕ, (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj
    (tateModuleLevel X l r).X ≅ (tateModuleLevel X l r).X
  tate : (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj
    (tateModule X l).X ≅ (tateModule X l).X
  qbar : (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj
    (tateTwistOne X l).X ≅ (tateTwistOne X l).X
  finite_spec : ∀ n : ℕ, (finite n).hom =
    Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} g.hom)
      (condensedRingObj (twistFiniteRing l E n) X) (rootsOfUnitySheaf X (l ^ (n + 1))) ≫
      (condensedPullbackHom (twistFiniteRing l E n) g.hom ⊗ₘ
        frobeniusRootMap g (l ^ (n + 1)))
  integral_spec : ∀ n : ℕ,
    integral.hom ≫ (limit.π (coefficientIntegralTwistSystem l E X) (op n)).hom =
      (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map
        (limit.π (coefficientIntegralTwistSystem l E X) (op n)).hom ≫ (finite n).hom
  rational_spec : (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map
      (Mod.extendπ (coefficientMap (twistIntegralToRational l E) X)
        (coefficientIntegralTwistOne l E X)) ≫ rational.hom =
    Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} g.hom)
      (condensedRingObj (twistRationalRing l E) X) (coefficientIntegralTwistOne l E X).X ≫
      (condensedPullbackHom (twistRationalRing l E) g.hom ⊗ₘ integral.hom) ≫
        Mod.extendπ (coefficientMap (twistIntegralToRational l E) X)
          (coefficientIntegralTwistOne l E X)
  tateLevel_spec : ∀ r : ℕ, (tateLevel r).hom =
    Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} g.hom)
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X)
      (rootsOfUnitySheaf X (l ^ r)) ≫
      (condensedPullbackHom (Profinite.continuousMapRingObj ℤ_[l]) g.hom ⊗ₘ
        frobeniusRootMap g (l ^ r))
  tate_spec : ∀ r : ℕ,
    tate.hom ≫ (limit.π (tateModuleSystem X l) (op r)).hom =
      (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map
        (limit.π (tateModuleSystem X l) (op r)).hom ≫ (tateLevel r).hom
  qbar_spec : (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map
      (Mod.extendπ (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl l) X)
        (tateModule X l)) ≫ qbar.hom =
    Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} g.hom)
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) (tateModule X l).X ≫
      (condensedPullbackHom (Profinite.padicAlgClRingObj l) g.hom ⊗ₘ tate.hom) ≫
        Mod.extendπ (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl l) X)
          (tateModule X l)

/-- The displayed degree-one equations have exactly one solution.
Source: natural Weil isomorphism paragraph
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: the finite tensor formulas specify every finite map. Compatibility of
root powers with pullback makes their projections a cone; the inverse-limit
universal property gives exactly one integral map. Its scalar-extension
coequalizer gives exactly one rational map. Apply the same argument separately
to the upstream Z_l free-root tower, then extend along Z_l to Qbar. Inverse
image along an isomorphism preserves these limits, tensors and coequalizers;
the inverse scheme isomorphism supplies inverse maps at each stage. Thus all
six map fields, and hence the record, are uniquely determined. -/
theorem frobeniusDegreeOneMaps_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (g : Aut X) :
    ∃ d : FrobeniusDegreeOneMaps l E X g,
      ∀ d' : FrobeniusDegreeOneMaps l E X g, d' = d := by
  sorry

/-- The uniquely normalized degree-one data. No unnormalized existence choice
is used. Source: natural Weil isomorphism paragraph
(blueprint: def-weil-frobenius-coefficient-twists). -/
def frobeniusDegreeOneMaps (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (g : Aut X) : FrobeniusDegreeOneMaps l E X g :=
  (frobeniusDegreeOneMaps_existsUnique l E X g).choose

/-- The signed comparisons of one fixed coefficient line. Degree zero is alpha,
positive degrees are fixed on relative tensor generators, and negative degrees
are fixed by evaluation against the positive isomorphism. Source: powers and
Hom transposes (blueprint: def-weil-frobenius-coefficient-twists). -/
structure FrobeniusSignedMaps (X : Scheme.{u}) (g : Aut X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (τ : (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj L.X ≅ L.X) where
  maps : ∀ m : ℤ, (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj
    (coefficientSignedTwist X _ L m).X ≅ (coefficientSignedTwist X _ L m).X
  zero : (maps 0).hom = condensedPullbackHom Λ g.hom
  positive : ∀ n : ℕ,
    (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map
      (Mod.tensorObjπ (coefficientTwistNat X _ L n) L) ≫ (maps ((n + 1 : ℕ) : ℤ)).hom =
    Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} g.hom)
      (coefficientTwistNat X _ L n).X L.X ≫ ((maps (n : ℤ)).hom ⊗ₘ τ.hom) ≫
        Mod.tensorObjπ (coefficientTwistNat X _ L n) L
  negative : ∀ n : ℕ,
    (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map
      (Mod.tensorObjπ
        ((ihom (coefficientTwistNat X _ L (n + 1))).obj (𝟙_ _))
        (coefficientTwistNat X _ L (n + 1)) ≫
          (Mod.ihomEvRight (coefficientTwistNat X _ L (n + 1)) (𝟙_ _)).hom) ≫
            condensedPullbackHom Λ g.hom =
    Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} g.hom)
      ((ihom (coefficientTwistNat X _ L (n + 1))).obj (𝟙_ _)).X
      (coefficientTwistNat X _ L (n + 1)).X ≫
        ((maps (Int.negSucc n)).hom ⊗ₘ (maps ((n + 1 : ℕ) : ℤ)).hom) ≫
          Mod.tensorObjπ ((ihom (coefficientTwistNat X _ L (n + 1))).obj (𝟙_ _))
            (coefficientTwistNat X _ L (n + 1)) ≫
              (Mod.ihomEvRight (coefficientTwistNat X _ L (n + 1)) (𝟙_ _)).hom

/-- The fixed degree-one comparison determines exactly one signed family.
Source: natural Weil isomorphism, powers and duals
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: start with alpha at zero and recursively descend the tensor of the
previous comparison and tau through the relative tensor coequalizer. Its
projection is epimorphic, so the equation determines each positive map.
For a negative degree, transport the internal Hom across the scheme-isomorphism
inverse image, postcompose by alpha and precompose by the inverse positive
comparison. The evaluation equation determines that map uniquely by the
internal Hom adjunction. All maps are invertible because alpha and tau are;
their inverses are obtained by the same tensor and dual constructions. -/
theorem frobeniusSignedMaps_existsUnique (X : Scheme.{u}) (g : Aut X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (τ : (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj L.X ≅ L.X)
    (hτ : Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} g.hom)
        (condensedRingObj Λ X) L.X ≫
      (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map (Mod.act L.X) ≫ τ.hom =
      (condensedPullbackHom Λ g.hom ⊗ₘ τ.hom) ≫ Mod.act L.X) :
    ∃ d : FrobeniusSignedMaps X g Λ L τ,
      ∀ d' : FrobeniusSignedMaps X g Λ L τ, d' = d := by
  sorry

-- These elementary free-module and limit constructions reuse the proofs in
-- CartesianCoefficientTwists, ModuleComparisons. Their role here is only to verify
-- the prescribed degree-one equations; they do not choose new comparison maps.

private def frobeniusMapFreeIso (R : C) [MonObj R] (A : C) :
    ((F.mapMod R).obj ((Mod.free R).obj A)) ≅
      (Mod.free (F.obj R)).obj (F.obj A) := by
  refine Mod.isoMk (Functor.Monoidal.μIso F R A).symm ?_
  rw [Iso.symm_hom, Functor.Monoidal.μIso_inv]
  dsimp +instances only [Mod.act, Functor.mapMod, Mod.free, Functor.modObjObj, Mod.freeModObj,
    ModObj.mk']
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_left]
  rw [Functor.Monoidal.map_associator_inv]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [Functor.obj.μ_def, comp_whiskerRight]

private def frobeniusFreeMap {R S : C} [MonObj R] [MonObj S] (ρ : R ⟶ S) [IsMonHom ρ]
    {A B : C} (a : A ⟶ B) :
    (Mod.free R).obj A ⟶ (Mod.comap ρ).obj ((Mod.free S).obj B) := by
  refine Mod.homMk (ρ ⊗ₘ a) ?_
  change ((α_ R R A).inv ≫ μ[R] ▷ A) ≫ (ρ ⊗ₘ a) =
    R ◁ (ρ ⊗ₘ a) ≫ ρ ▷ (S ⊗ B) ≫ (α_ S S B).inv ≫ μ[S] ▷ B
  have hs : R ◁ (ρ ⊗ₘ a) ≫ ρ ▷ (S ⊗ B) = ρ ⊗ₘ (ρ ⊗ₘ a) := by
    rw [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  rw [← Category.assoc (R ◁ (ρ ⊗ₘ a)), hs]
  rw [associator_inv_naturality_assoc]
  simp only [Category.assoc]
  apply congrArg ((α_ R R A).inv ≫ ·)
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, IsMonHom.mul_hom]
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]

private def frobeniusRestrictedFreeMap {R B : C} [MonObj R] [MonObj B]
    {R' B' : D} [MonObj R'] [MonObj B']
    (r : R ⟶ B) [IsMonHom r] (s : R' ⟶ B') [IsMonHom s]
    (a : F.obj R ⟶ R') [IsMonHom a] (b : F.obj B ⟶ B') [IsMonHom b]
    (hsq : F.map r ≫ b = a ≫ s) {M : C} {N : D} (t : F.obj M ⟶ N) :
    (F.mapMod R).obj ((Mod.comap r).obj ((Mod.free B).obj M)) ⟶
      (Mod.comap a).obj ((Mod.comap s).obj ((Mod.free B').obj N)) :=
  (F.mapModComapIso r).hom.app ((Mod.free B).obj M) ≫
    (Mod.comap (F.map r)).map ((frobeniusMapFreeIso F B M).hom) ≫
    (Mod.comap (F.map r)).map (frobeniusFreeMap b t) ≫
    (Mod.comapComp (F.map r) b).inv.app ((Mod.free B').obj N) ≫
    (Mod.comapCongr hsq).hom.app ((Mod.free B').obj N) ≫
    (Mod.comapComp a s).hom.app ((Mod.free B').obj N)

private theorem frobeniusRestrictedFreeMap_hom {R B : C} [MonObj R] [MonObj B]
    {R' B' : D} [MonObj R'] [MonObj B']
    (r : R ⟶ B) [IsMonHom r] (s : R' ⟶ B') [IsMonHom s]
    (a : F.obj R ⟶ R') [IsMonHom a] (b : F.obj B ⟶ B') [IsMonHom b]
    (hsq : F.map r ≫ b = a ≫ s) {M : C} {N : D} (t : F.obj M ⟶ N) :
    (frobeniusRestrictedFreeMap F r s a b hsq t).hom =
      Functor.OplaxMonoidal.δ F B M ≫ (b ⊗ₘ t) := by
  change 𝟙 _ ≫ Functor.OplaxMonoidal.δ F B M ≫ (b ⊗ₘ t) ≫
    𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

private noncomputable def frobeniusLinearIntoLimit {R S : D} [MonObj R] [MonObj S]
    {J : Type*} [Category J] (K : J ⥤ Mod D S) [HasLimit K] [PreservesLimit K (Mod.forget S)]
    (M : Mod D R) (a : R ⟶ S) [IsMonHom a]
    (g : M.X ⟶ (limit K).X)
    (c : ∀ j, M ⟶ (Mod.comap a).obj (K.obj j))
    (hc : ∀ j, g ≫ (limit.π K j).hom = (c j).hom) :
    M ⟶ (Mod.comap a).obj (limit K) := by
  refine Mod.homMk g ?_
  apply (isLimitOfPreserves (Mod.forget S) (limit.isLimit K)).hom_ext
  intro j
  change (Mod.act M.X ≫ g) ≫ (limit.π K j).hom =
    (R ◁ g ≫ a ▷ (limit K).X ≫ Mod.act (limit K).X) ≫ (limit.π K j).hom
  rw [Category.assoc, hc, Mod.act_hom]
  change R ◁ (c j).hom ≫ a ▷ (K.obj j).X ≫ Mod.act (K.obj j).X = _
  rw [← hc, whiskerLeft_comp, Category.assoc]
  erw [whisker_exchange_assoc, ← Mod.act_hom]
  simp only [Category.assoc]

private theorem frobeniusSemilinearEquation
    {R : C} [MonObj R] {S : D} [MonObj S]
    (a : F.obj R ⟶ S) [IsMonHom a] (M : Mod C R) (N : Mod D S)
    (c : (F.mapMod R).obj M ⟶ (Mod.comap a).obj N) :
    Functor.LaxMonoidal.μ F R M.X ≫ F.map (Mod.act M.X) ≫ c.hom =
      (a ⊗ₘ c.hom) ≫ Mod.act N.X := by
  have h := Mod.act_hom c
  change (Functor.LaxMonoidal.μ F R M.X ≫ F.map (Mod.act M.X)) ≫ c.hom =
    F.obj R ◁ c.hom ≫ a ▷ N.X ≫ Mod.act N.X at h
  simpa only [Mod.comap, tensorHom_def', Category.assoc] using h

private def frobeniusFreeSemilinear
    {R : C} [MonObj R] {S : D} [MonObj S]
    (a : F.obj R ⟶ S) [IsMonHom a] {U : C} {V : D} (t : F.obj U ⟶ V) :
    (F.mapMod R).obj ((Mod.free R).obj U) ⟶
      (Mod.comap a).obj ((Mod.free S).obj V) :=
  (frobeniusMapFreeIso F R U).hom ≫ frobeniusFreeMap a t

private theorem frobeniusFreeSemilinear_hom
    {R : C} [MonObj R] {S : D} [MonObj S]
    (a : F.obj R ⟶ S) [IsMonHom a] {U : C} {V : D} (t : F.obj U ⟶ V) :
    (frobeniusFreeSemilinear F a t).hom =
      Functor.OplaxMonoidal.δ F R U ≫ (a ⊗ₘ t) := rfl

private theorem frobeniusSemilinearOfPresentation
    {R : C} [MonObj R] {S : D} [MonObj S]
    (a : F.obj R ⟶ S) [IsMonHom a] (M : Mod C R) (N : Mod D S)
    (U : C) (V : D) (p : (Mod.free R).obj U ⟶ M)
    (q : (Mod.free S).obj V ⟶ N) (t : F.obj U ⟶ V)
    (c : F.obj M.X ⟶ N.X)
    [Epi (F.obj R ◁ F.map p.hom)]
    (hc : F.map p.hom ≫ c =
      Functor.OplaxMonoidal.δ F R U ≫ (a ⊗ₘ t) ≫ q.hom) :
    Functor.LaxMonoidal.μ F R M.X ≫ F.map (Mod.act M.X) ≫ c =
      (a ⊗ₘ c) ≫ Mod.act N.X := by
  let : ModObj R (R ⊗ U) := ((Mod.free R).obj U).mod
  let d := frobeniusFreeSemilinear F a t ≫ (Mod.comap a).map q
  have hd : d.hom = F.map p.hom ≫ c := by
    change (frobeniusFreeSemilinear F a t).hom ≫ q.hom = _
    rw [frobeniusFreeSemilinear_hom]
    simpa only [Category.assoc] using hc.symm
  have h := frobeniusSemilinearEquation F a ((Mod.free R).obj U) N d
  rw [hd] at h
  apply (cancel_epi (F.obj R ◁ F.map p.hom)).1
  calc
    _ = Functor.LaxMonoidal.μ F R (R ⊗ U) ≫
        F.map (R ◁ p.hom ≫ Mod.act M.X) ≫ c := by
      rw [Functor.map_comp, Category.assoc, Functor.LaxMonoidal.μ_natural_right_assoc]
    _ = Functor.LaxMonoidal.μ F R (R ⊗ U) ≫
        F.map (Mod.act ((Mod.free R).obj U).X ≫ p.hom) ≫ c := by
      rw [Mod.act_hom]
    _ = (a ⊗ₘ (F.map p.hom ≫ c)) ≫ Mod.act N.X := by
      simpa only [Functor.map_comp, Category.assoc] using h
    _ = _ := by
      simp only [tensorHom_def', whiskerLeft_comp, Category.assoc]

private theorem frobeniusWhiskerMap_epi [F.PreservesEpimorphisms]
    (S : C) {U V : C} (p : U ⟶ V) [Epi (S ◁ p)] :
    Epi (F.obj S ◁ F.map p) := by
  have h : F.obj S ◁ F.map p =
      Functor.LaxMonoidal.μ F S U ≫ F.map (S ◁ p) ≫
        Functor.OplaxMonoidal.δ F S V := by
    apply (cancel_mono (Functor.LaxMonoidal.μ F S V)).1
    simp only [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
    exact Functor.LaxMonoidal.μ_natural_right F S p
  rw [h]
  infer_instance

private def frobeniusExtensionProjection
    [HasCoequalizers C] [BraidedCategory C]
    [∀ T : C, PreservesColimitsOfSize.{0, 0} (tensorLeft T)]
    [∀ T : C, PreservesColimitsOfSize.{0, 0} (tensorRight T)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ]
    (M : Mod C R) :
    (Mod.free S).obj M.X ⟶ (Mod.extendScalars φ).obj M := by
  refine Mod.homMk (Mod.extendπ φ M) ?_
  change ((α_ S S M.X).inv ≫ μ[S] ▷ M.X) ≫ Mod.extendπ φ M =
    S ◁ Mod.extendπ φ M ≫ Mod.act (Mod.extendScalarsObj φ M).X
  simpa only [Category.assoc] using (Mod.whiskerLeft_extendπ_smul φ M).symm

/-- The specified degree-one maps are semilinear over alpha.
Source: coefficient compatibility in the natural Weil map paragraph
(blueprint: def-weil-frobenius-coefficient-twists).
Proof: at finite levels the free-module action is on the coefficient factor,
so alpha tensor the root map is semilinear. Restrict these maps along finite
reduction, using the coefficient square. Their equations at every integral
projection give semilinearity of the integral map. For rational and Qbar
coefficients, the specified scalar-extension formula is a linear map from a
free module followed by its linear quotient projection. The pullback quotient
and its tensor with the coefficient ring are epimorphic, so the linearity
equation descends to the specified comparison itself. -/
theorem frobeniusDegreeOneMaps_semilinear (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (g : Aut X) :
    (∀ n : ℕ, Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} g.hom)
        (condensedRingObj (twistFiniteRing l E n) X) (coefficientFiniteTwistOne l E X n).X ≫
      (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map
        (Mod.act (coefficientFiniteTwistOne l E X n).X) ≫
          ((frobeniusDegreeOneMaps l E X g).finite n).hom =
      (condensedPullbackHom (twistFiniteRing l E n) g.hom ⊗ₘ
        ((frobeniusDegreeOneMaps l E X g).finite n).hom) ≫
          Mod.act (coefficientFiniteTwistOne l E X n).X) ∧
    (Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} g.hom)
        (condensedRingObj (twistIntegralRing l E) X) (coefficientIntegralTwistOne l E X).X ≫
      (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map
        (Mod.act (coefficientIntegralTwistOne l E X).X) ≫
          (frobeniusDegreeOneMaps l E X g).integral.hom =
      (condensedPullbackHom (twistIntegralRing l E) g.hom ⊗ₘ
        (frobeniusDegreeOneMaps l E X g).integral.hom) ≫
          Mod.act (coefficientIntegralTwistOne l E X).X) ∧
    (Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} g.hom)
        (condensedRingObj (twistRationalRing l E) X) (coefficientRationalTwistOne l E X).X ≫
      (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map
        (Mod.act (coefficientRationalTwistOne l E X).X) ≫
          (frobeniusDegreeOneMaps l E X g).rational.hom =
      (condensedPullbackHom (twistRationalRing l E) g.hom ⊗ₘ
        (frobeniusDegreeOneMaps l E X g).rational.hom) ≫
          Mod.act (coefficientRationalTwistOne l E X).X) ∧
    (Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} g.hom)
        (condensedRingObj (Profinite.padicAlgClRingObj l) X) (tateTwistOne X l).X ≫
      (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).map
        (Mod.act (tateTwistOne X l).X) ≫ (frobeniusDegreeOneMaps l E X g).qbar.hom =
      (condensedPullbackHom (Profinite.padicAlgClRingObj l) g.hom ⊗ₘ
        (frobeniusDegreeOneMaps l E X g).qbar.hom) ≫ Mod.act (tateTwistOne X l).X) := by
  let F := upperStar Ab.{u + 1} g.hom
  let d := frobeniusDegreeOneMaps l E X g
  have hfinite (n : ℕ) := frobeniusSemilinearEquation F
    (condensedPullbackHom (twistFiniteRing l E n) g.hom)
    (coefficientFiniteTwistOne l E X n) (coefficientFiniteTwistOne l E X n)
    (frobeniusFreeSemilinear F
      (condensedPullbackHom (twistFiniteRing l E n) g.hom)
      (frobeniusRootMap g (l ^ (n + 1))))
  let hlevel (n : ℕ) := frobeniusRestrictedFreeMap F
    (coefficientMap (twistReduction l E n) X)
    (coefficientMap (twistReduction l E n) X)
    (condensedPullbackHom (twistIntegralRing l E) g.hom)
    (condensedPullbackHom (twistFiniteRing l E n) g.hom)
    (map_coefficientMap_comp_condensedPullbackHom (twistReduction l E n) g.hom)
    (frobeniusRootMap g (l ^ (n + 1)))
  let cIntegral := frobeniusLinearIntoLimit
    (coefficientIntegralTwistSystem l E X)
    ((F.mapMod _).obj (coefficientIntegralTwistOne l E X))
    (condensedPullbackHom (twistIntegralRing l E) g.hom) d.integral.hom
    (fun n ↦ (F.mapMod _).map
      (limit.π (coefficientIntegralTwistSystem l E X) n) ≫ hlevel n.unop) (by
      intro n
      change d.integral.hom ≫
          (limit.π (coefficientIntegralTwistSystem l E X) n).hom =
        F.map (limit.π (coefficientIntegralTwistSystem l E X) n).hom ≫
          (hlevel n.unop).hom
      rw [frobeniusRestrictedFreeMap_hom, ← d.finite_spec]
      exact d.integral_spec n.unop)
  have hIntegral := frobeniusSemilinearEquation F
    (condensedPullbackHom (twistIntegralRing l E) g.hom)
    (coefficientIntegralTwistOne l E X) (coefficientIntegralTwistOne l E X) cIntegral
  refine ⟨?_, hIntegral, ?_, ?_⟩
  · intro n
    rw [show ((frobeniusDegreeOneMaps l E X g).finite n).hom = _ from d.finite_spec n]
    simpa only [frobeniusFreeSemilinear_hom, F, Mod.comap, upperStar,
      Scheme.proEtaleSheafInverseImage, Scheme.proEtaleBaseChange] using hfinite n
  · have : Epi (F.obj (condensedRingObj (twistRationalRing l E) X) ◁
        F.map (frobeniusExtensionProjection
          (coefficientMap (twistIntegralToRational l E) X)
          (coefficientIntegralTwistOne l E X)).hom) := by
      change Epi (F.obj (condensedRingObj (twistRationalRing l E) X) ◁
        F.map (Mod.extendπ (coefficientMap (twistIntegralToRational l E) X)
          (coefficientIntegralTwistOne l E X)))
      exact frobeniusWhiskerMap_epi F _ _
    exact frobeniusSemilinearOfPresentation F
      (condensedPullbackHom (twistRationalRing l E) g.hom)
      (coefficientRationalTwistOne l E X) (coefficientRationalTwistOne l E X)
      (coefficientIntegralTwistOne l E X).X (coefficientIntegralTwistOne l E X).X
      (frobeniusExtensionProjection (coefficientMap (twistIntegralToRational l E) X) _)
      (frobeniusExtensionProjection (coefficientMap (twistIntegralToRational l E) X) _)
      d.integral.hom d.rational.hom d.rational_spec
  · have : Epi (F.obj (condensedRingObj (Profinite.padicAlgClRingObj l) X) ◁
        F.map (frobeniusExtensionProjection
          (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl l) X)
          (tateModule X l)).hom) := by
      change Epi (F.obj (condensedRingObj (Profinite.padicAlgClRingObj l) X) ◁
        F.map (Mod.extendπ (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl l) X)
          (tateModule X l)))
      exact frobeniusWhiskerMap_epi F _ _
    exact frobeniusSemilinearOfPresentation F
      (condensedPullbackHom (Profinite.padicAlgClRingObj l) g.hom)
      (tateTwistOne X l) (tateTwistOne X l)
      (tateModule X l).X (tateModule X l).X
      (frobeniusExtensionProjection
        (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl l) X) _)
      (frobeniusExtensionProjection
        (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl l) X) _)
      d.tate.hom d.qbar.hom d.qbar_spec

/-- The four coefficient families, all in the recorded condensed internal-module
model. The finite extension is an actual field, not an abstract coefficient label.
Source: coefficient families in the natural Weil map paragraph
(blueprint: def-weil-frobenius-coefficient-twists). -/
inductive FrobeniusTwistCoefficient
  | finite (n : ℕ)
  | integral
  | rational
  | qbar

/-- The actual signed coefficient sheaf. In the qbar case this is precisely the
upstream internal Tate module followed by extension of scalars, not the colimit
of a different family of signed lines. Source: coefficient-twist construction
(blueprint: def-weil-frobenius-coefficient-twists). -/
def frobeniusTwistSheaf (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (A : FrobeniusTwistCoefficient) (m : ℤ) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  match A with
  | .finite n => (coefficientSignedTwist X _ (coefficientFiniteTwistOne l E X n) m).X
  | .integral => (coefficientSignedTwist X _ (coefficientIntegralTwistOne l E X) m).X
  | .rational => (coefficientSignedTwist X _ (coefficientRationalTwistOne l E X) m).X
  | .qbar => (tateTwist X l m).X

/-- Restriction along g, followed by the canonical section reindexing and theta.
This is literally Gamma(theta) composed with res_g. Source: scalar assertions
paragraph (blueprint: def-weil-frobenius-coefficient-twists). -/
def frobeniusTwistSectionAction {X : Scheme.{u}} (g : Aut X)
    (M : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (θ : (Scheme.proEtaleSheafInverseImage g.hom Ab.{u + 1}).obj M ≅ M) :
    M.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) →+
      M.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  ((θ.hom.hom.app (op (Scheme.ProEt.mk (𝟙 X)))).hom.comp
    ((((Scheme.proEtaleIsoInverseImageIdentification g.hom Ab.{u + 1}).inv.app M).app
      (op (Scheme.ProEt.mk (𝟙 X)))).hom)).comp
        (M.obj.map (MorphismProperty.Over.homMk
          (A := (Scheme.proEtaleIsoPostcompose g.hom).obj (Scheme.ProEt.mk (𝟙 X)))
          (B := Scheme.ProEt.mk (𝟙 X)) g.hom (by
            change g.hom ≫ 𝟙 X = 𝟙 X ≫ g.hom
            simp)).op).hom

/-- Spec of the geometric field Frobenius, on s = Spec k itself.
Source: scalar-assertions paragraph
(blueprint: def-weil-frobenius-coefficient-twists). -/
def frobeniusCoefficientPoint (D : FiniteFieldDatum.{u}) :
    Aut (Spec (CommRingCat.of D.k)) :=
  letI := Fintype.ofFinite D.k₀
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

end WeilConjectures
