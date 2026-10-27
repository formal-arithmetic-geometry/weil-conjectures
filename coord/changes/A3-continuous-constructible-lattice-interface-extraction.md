# Continuous constructible lattice interfaces

## Reason

Separate the existing data interfaces from the final theorem so each genuine proof step
can live in its own module without an import cycle. This is a proof decomposition, not
a change of coefficients, encoding, scalar maps, lattice inclusions or target statements.
The extracted data module has no sorry. No arbitrary lattice witness is put into a definition.

## Old

The item module publicly declared Coefficients, inclusion, Coefficients.scalar,
Coefficients.rationalEncoding, Coefficients.integralEncoding, abCoefficients, chart,
internalInclusion, continuousPull, internalPullUnit, LisseCriterion, Encoding,
internalExtend, ScalarComparison, CoefficientFamily, Lattice, LatticeRestriction,
Restriction, FieldChange, Stratified, OrdinaryScalars and Family in namespace
WeilConjectures.StratifiedContinuousLattices.

Original public imports (verbatim):

```lean
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.ContinuousCoefficientRealizations
public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.Paper.ContinuousModuleEncodingUniverses
public import Sheaf.Paper.ContinuousScalarEncodingUniverses
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.AdicHeartPullbackFibres
public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.Paper.ContinuousLocallyFreePullback
```

The original declaration block (verbatim):

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.StratifiedContinuousLattices

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} X.ProEt

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Continuous coefficient coordinates, with every positive quotient projection fixed.
Source: BS 6.8.2(1),(2) and 6.8.15
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Coefficients (X : Scheme.{u}) where
  integral : pbcAdicCompletion X (pbcIntegralDatum l E) ≅
    latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E)
  rational : latticeCoefficientSheaf X E ≅ rationalCoefficientSheaf l X E
  rational_values : ∀ (U : X.ProEtᵒᵖ) (s : C(U.unop.left, E)) (x : U.unop.left),
    rationalCoefficientValue l E X U (rational.hom.hom.app U (ULift.up s)) x = s x
  finite : ∀ n : ℕ, (pbcAdicRings X (pbcIntegralDatum l E)).obj (op n) ≅
    finiteContinuousCoefficientSheaf l X E n
  finite_constants : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1)) (x : U.unop.left),
    finiteContinuousCoefficientValue l E X n U
      ((finite n).hom.hom.app U (pbcFunctionScalars X (pbcIntegralDatum l E) n |>.app U
        |>.hom <| a)) x = integralCoefficientULift l E n a
  integral_reduction : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
    (s : C(U.unop.left, Padic.coefficientExtensionIntegers l E)) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E X n U
      ((integral.inv ≫ pbcAdicProjection X (pbcIntegralDatum l E) n ≫
        (finite n).hom).hom.app U (ULift.up s)) x).down =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) (s x)
  localization : integralCoefficientLocalization l X E ≅ rationalCoefficientSheaf l X E
  localization_normalized :
    integralCoefficientLocalizationNormalized l E X localization.hom

/-- The specified integral-to-field scalar map, in continuous coordinates.
Source: BS 6.8.2(2), Stacks 03EK
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
abbrev inclusion (X : Scheme.{u}) :=
  latticeCoefficientSheafMap X (Padic.coefficientExtensionIntegers l E).subtype
    continuous_subtype_val

/-- The completed scalar map uses the same integral and rational coordinates.
Source: BS 6.8.2(2)
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def Coefficients.scalar {X : Scheme.{u}} (c : Coefficients l E X) :=
  c.integral.hom ≫ inclusion l E X ≫ c.rational.hom

/-- The rational encoding, with its coefficient transport fixed by the ring chart.
Source: Stacks 00YV; BS 6.8.2
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def Coefficients.rationalEncoding {X : Scheme.{u}} (c : Coefficients l E X) :=
  (ProEtale.CondensedRing.continuousFieldModuleEquivalenceUniverse l E X).trans
    (ProEtale.CondensedRing.ringModuleEquivalenceOfIso X
      ((adicLisseForget X).mapIso c.rational.symm))

/-- The integral encoding is the existing completed section-action encoding.
Source: Stacks 00YV; BS 6.8.2
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
abbrev Coefficients.integralEncoding {X : Scheme.{u}} (c : Coefficients l E X) :=
  ProEtale.CondensedRing.completedContinuousModuleEquivalence l E X c.integral

/-- Underlying abelian sheaf of a commutative coefficient sheaf.
Source: Stacks 00YV
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
abbrev abCoefficients (X : Scheme.{u}) :=
  sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})

/-- The canonical condensed chart followed by the identity section-ring comparison.
Source: BS 6.8.2; HRS Example 3.1
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def chart (X : Scheme.{u}) (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] :=
  ProEtale.ContinuousRingUniverse.comparison X R ≫
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (ProEtale.CondensedRing.continuousSectionRingIso X R).inv

/-- The actual condensed integral-to-rational coefficient map.
Its existing definition and ring-hom instance are owned by
`def-weil-pbc-continuous-scalar-map-universes`, not by the scalar-encoding theorem.
Source: BS 6.8.2, functoriality of pullback from the point
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
abbrev internalInclusion (X : Scheme.{u}) :=
  ProEtale.CondensedRing.continuousInternalScalarMapUniverses l E X

/-- Ordinary module pullback along the continuous-function coefficient map.
Source: Stacks 03D2, 03EL; BS 6.8.15
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def continuousPull {X Y : Scheme.{u}} (f : Y ⟶ X) (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :=
  proEtaleModuleInverseImage f (latticeCoefficientSheaf X R) ⋙
    pbcExtend (ProEtale.continuousCoefficientInverseImageMap f R)

/-- The actual internal inverse-image unit, followed by the coefficient extension unit.
Source: Stacks 03EL; BS 6.8.15
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def internalPullUnit {X Y : Scheme.{u}} (f : Y ⟶ X) (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X))
    (U : X.ProEt) (m : P.X.obj.obj (op U)) :=
  (Mod.extendUnitHom
    (ProEtale.condensedPullbackHom (Profinite.continuousCoefficientRingObj R) f)
    (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj P)).hom.app
      (op ((proEtaleBaseChange f).obj U))
    (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app P.X).hom.app (op U) m)

/-- The lisse criterion, including rank zero and locally varying finite ranks.
Source: BS Definition 6.8.3; Stacks 03DM
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def LisseCriterion (X : Scheme.{u}) (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [TotallyDisconnectedSpace R] : Prop :=
  ∀ P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X),
    ProEtale.CondensedRing.LocallyFree
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X) P ↔
      SheafOfModules.IsFiniteLocallyFree
        ((ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse X R).functor.obj P)


/-- The encoding is the identity on sections, maps and actions, with its actual inverse image.
The unit equation fixes the pullback comparison rather than choosing an arbitrary isomorphism.
Source: Stacks 00YV, 03EL; BS 6.8.15
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Encoding (X : Scheme.{u}) (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [TotallyDisconnectedSpace R] where
  sections : ∀ P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X),
    (SheafOfModules.toSheaf _).obj
      ((ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse X R).functor.obj P)
      ≅ P.X
  identity_sections : ∀ P (U : X.ProEtᵒᵖ) m,
    HEq ((sections P).hom.hom.app U m) m
  identity_maps : ∀ (P Q : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X))
    (g : P ⟶ Q) (U : X.ProEtᵒᵖ),
    HEq
      (SheafOfModules.Hom.val
        ((ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse X R).functor.map g)
        |>.app U) (g.hom.hom.app U)
  lisse : LisseCriterion X R
  restriction : [IsNoetherian X] → ∀ (Y : Scheme.{u}) (f : Y ⟶ X) [IsImmersion f],
    (ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse X R).functor ⋙
      continuousPull f R ≅
      ProEtale.CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) f ⋙
        (ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse Y R).functor
  restriction_unit : ∀ [IsNoetherian X] (Y : Scheme.{u}) (f : Y ⟶ X) [IsImmersion f] P
    (U : X.ProEt) (m :
      ((ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse X R).functor.obj
        P).val.obj (op U)),
    HEq (((restriction Y f).hom.app P).val.app (op ((proEtaleBaseChange f).obj U))
      (ContinuousRational.moduleUnit f
        (ProEtale.continuousCoefficientInverseImageMap f R) _ U m))
      (internalPullUnit f R P U ((sections P).hom.hom.app (op U) m))

/-- Internal scalar extension in the fixed sheaf universe. All size data are derived.
Source: Stacks 03EK; the published internal scalar extension
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def internalExtend (X : Scheme.{u}) :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  letI : HasSheafify (ProEt.topology X) Ab.{u + 1} :=
    hasSheafifyEssentiallySmallSite _ _
  Mod.extendScalars.{u + 1, u + 2} (internalInclusion l E X)

/-- The integral/rational encoding commutes with scalar restriction and extension.
Both normalization equations use the actual section-action encoding and tensor unit.
Source: Stacks 00YV, 03EK; BS 6.8.2
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure ScalarComparison (X : Scheme.{u}) (c : Coefficients l E X) where
  restriction : Mod.comap (internalInclusion l E X) ⋙ (c.integralEncoding l E).functor ≅
    (c.rationalEncoding l E).functor ⋙ pbcRestrict (c.scalar l E)
  restriction_identity : ∀ P (U : X.ProEtᵒᵖ),
    HEq ((restriction.hom.app P).val.app U) (id : P.X.obj.obj U → P.X.obj.obj U)
  extension : internalExtend l E X ⋙ (c.rationalEncoding l E).functor ≅
    (c.integralEncoding l E).functor ⋙ pbcExtend (c.scalar l E)
  tensor_unit : ∀ P (U : X.ProEtᵒᵖ)
    (m : ((c.integralEncoding l E).functor.obj P).val.obj U),
    (extension.hom.app P).val.app U
      (((c.integralEncoding l E).functor.map
        ((Mod.extendRestrictAdjunction.{u + 1, u + 2} (internalInclusion l E X)).unit.app P) ≫
        restriction.hom.app ((internalExtend l E X).obj P)).val.app U m) =
          pbcTensorSection (c.scalar l E)
            ((c.integralEncoding l E).functor.obj P) U 1 m

/-- One coefficient family, including the normalization of successive locally closed maps.
Source: BS 6.8.2, 6.8.13, 6.8.15; Stacks 00YV, 03EL
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure CoefficientFamily where
  [ultrametric : IsUltrametricDist E]
  atScheme : ∀ X : Scheme.{u}, Coefficients l E X
  integral_chart : ∀ X : Scheme.{u}, IsIso (chart X
    (Padic.coefficientExtensionIntegers l E))
  rational_chart : ∀ X : Scheme.{u}, IsIso (chart X E)
  inclusion_square : ∀ X : Scheme.{u},
    internalInclusion l E X ≫ chart X E =
      chart X (Padic.coefficientExtensionIntegers l E) ≫
        (abCoefficients X).map (inclusion l E X)
  integral_encoding : ∀ X : Scheme.{u}, Encoding X (Padic.coefficientExtensionIntegers l E)
  scalar : ∀ X : Scheme.{u}, ScalarComparison l E X (atScheme X)
  rational_encoding : ∀ X : Scheme.{u}, Encoding X E

/-- A genuine internal lattice inclusion together with its sectionwise encoding.
Source: BS 6.8.13, first paragraph; Stacks 00YV, 03EK
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Lattice (X : Scheme.{u}) (c : Coefficients l E X)
    (F : pbcModules X (rationalCoefficientSheaf l X E)) where
  moduleObject : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousCoefficientRingObj
      (Padic.coefficientExtensionIntegers l E)) X)
  internal_lisse : ProEtale.CondensedRing.LocallyFree
    (condensedRingObj (Profinite.continuousCoefficientRingObj
      (Padic.coefficientExtensionIntegers l E)) X) moduleObject
  internal_inclusion : moduleObject ⟶ (Mod.comap (internalInclusion l E X)).obj
    ((c.rationalEncoding l E).inverse.obj F)
  internal_mono : Mono internal_inclusion
  internal_localization :
    IsIso (Mod.extendHom.{u + 1, u + 2} (internalInclusion l E X) internal_inclusion)
  inclusion : (c.integralEncoding l E).functor.obj moduleObject ⟶
    (pbcRestrict (c.scalar l E)).obj F
  comparison : ScalarComparison l E X c
  same_inclusion : inclusion = (c.integralEncoding l E).functor.map internal_inclusion ≫
    comparison.restriction.hom.app ((c.rationalEncoding l E).inverse.obj F) ≫
      (pbcRestrict (c.scalar l E)).map ((c.rationalEncoding l E).counitIso.hom.app F)
  lisse : ((c.integralEncoding l E).functor.obj moduleObject).IsFiniteLocallyFree
  mono : Mono inclusion
  localization : IsIso (((pbcScalarAdjunction (c.scalar l E)).homEquiv _ _).symm inclusion)

/-- An inclusion stays a lisse full lattice under the actual ordinary inverse image.
The equality fixes the rationalization as the map induced by the pulled inclusion.
Source: BS 6.8.15; Stacks 03EL
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure LatticeRestriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    (cX : Coefficients l E X) (cY : Coefficients l E Y)
    (F : pbcModules X (rationalCoefficientSheaf l X E)) (L : Lattice l E X cX F) where
  integral : (adicTowerInverseImage f).obj
    (pbcAdicCompletion X (pbcIntegralDatum l E)) ⟶
      pbcAdicCompletion Y (pbcIntegralDatum l E)
  rational : (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ⟶
    rationalCoefficientSheaf l Y E
  rational_normalized : rationalCoefficientRestrictionNormalized l E f rational
  integral_normalized :
    (adicTowerInverseImage f).map cX.integral.hom ≫
      ProEtale.continuousCoefficientInverseImageMap f
        (Padic.coefficientExtensionIntegers l E) = integral ≫ cY.integral.hom
  square : (adicTowerInverseImage f).map (cX.scalar l E) ≫ rational =
    integral ≫ cY.scalar l E
  pulled : Lattice l E Y cY
    ((ContinuousRational.modulePull f rational).obj F)
  integral_iso : (ContinuousRational.modulePull f integral).obj
      ((cX.integralEncoding l E).functor.obj L.moduleObject) ≅
    (cY.integralEncoding l E).functor.obj pulled.moduleObject
  same_inclusion : ∀ (U : X.ProEt) (m :
      ((cX.integralEncoding l E).functor.obj L.moduleObject).val.obj (op U)),
    HEq (pulled.inclusion.val.app (op ((proEtaleBaseChange f).obj U))
      (integral_iso.hom.val.app (op ((proEtaleBaseChange f).obj U))
        (ContinuousRational.moduleUnit f integral _ U m)))
      (ContinuousRational.moduleUnit f rational F U (L.inclusion.val.app (op U) m))

/-- The coefficient square and its successive restrictions use the canonical function maps.
Source: BS 6.8.2, 6.8.15; Stacks 03EL
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Restriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    (cX : Coefficients l E X) (cY : Coefficients l E Y) where
  integral : (adicTowerInverseImage f).obj
    (pbcAdicCompletion X (pbcIntegralDatum l E)) ≅
      pbcAdicCompletion Y (pbcIntegralDatum l E)
  rational : (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ≅
    rationalCoefficientSheaf l Y E
  rational_normalized : rationalCoefficientRestrictionNormalized l E f rational.hom
  continuous_integral : IsIso (ProEtale.continuousCoefficientInverseImageMap f
    (Padic.coefficientExtensionIntegers l E))
  integral_normalized :
    (adicTowerInverseImage f).map cX.integral.hom ≫
      ProEtale.continuousCoefficientInverseImageMap f
        (Padic.coefficientExtensionIntegers l E) = integral.hom ≫ cY.integral.hom
  square : (adicTowerInverseImage f).map (cX.scalar l E) ≫ rational.hom =
    integral.hom ≫ cY.scalar l E

/-- Coefficient extension is the actual continuous map, fixed on every compatible quotient.
The relation between exponents allows ramification, hence does not equate uniformizers.
Source: BS 6.8.2, 6.8.15
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure FieldChange (E' : Type u) [NormedField E'] [NormedAlgebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E'] (i : E →ₐ[ℚ_[l]] E') (X : Scheme.{u})
    (c : Coefficients l E X) (c' : Coefficients l E' X) where
  integers : Padic.coefficientExtensionIntegers l E →+*
    Padic.coefficientExtensionIntegers l E'
  integer_values : ∀ a, (integers a).val = i a.val
  continuous : Continuous integers
  integral : pbcAdicCompletion X (pbcIntegralDatum l E) ⟶
    pbcAdicCompletion X (pbcIntegralDatum l E')
  integral_normalized : integral ≫ c'.integral.hom = c.integral.hom ≫
    latticeCoefficientSheafMap X integers continuous
  rational : rationalCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X E'
  rational_normalized : ∀ (U : X.ProEtᵒᵖ)
    (s : (rationalCoefficientSheaf l X E).obj.obj U) (x : U.unop.left),
    rationalCoefficientValue l E' X U (rational.hom.app U s) x =
      i (rationalCoefficientValue l E X U s x)
  square : c.scalar l E ≫ rational = integral ≫ c'.scalar l E'
  quotient_normalized : ∀ (m n : ℕ)
    (h : Padic.coefficientExtensionIdeal l E (m + 1) ≤
      Ideal.comap integers (Padic.coefficientExtensionIdeal l E' (n + 1)))
    (U : X.ProEtᵒᵖ) (s : C(U.unop.left, Padic.coefficientExtensionIntegers l E))
    (x : U.unop.left),
    (finiteContinuousCoefficientValue l E' X n U
      ((integral ≫ pbcAdicProjection X (pbcIntegralDatum l E') n ≫
        (c'.finite n).hom).hom.app U (c.integral.inv.hom.app U (ULift.up s))) x).down =
      Ideal.quotientMap _ integers h
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (m + 1)) (s x))

/-- The finite stratification refines a supplied lisse partition. Its reduction has the
same strata and pulled lattice inclusions; each admits all further locally closed pullbacks.
Source: BS 6.8.13, first paragraph, and 6.8.15; Stacks 054M
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Stratified (T : Scheme.{u}) (c : ∀ X : Scheme.{u}, Coefficients l E X)
    (F : pbcModules T (rationalCoefficientSheaf l T E))
    (S : Scheme.FiniteLocallyClosedStratification T) where
  refinement : Scheme.FiniteLocallyClosedStratification T
  empty : IsEmpty T → refinement.n = 0
  parent : Fin refinement.n → Fin S.n
  factor : ∀ a, refinement.domain a ⟶ S.domain (parent a)
  factor_immersion : ∀ a, IsImmersion (factor a)
  factorization : ∀ a, factor a ≫ S.immersion (parent a) = refinement.immersion a
  restriction : ∀ a, Restriction l E (refinement.immersion a) (c T)
    (c (refinement.domain a))
  lattice : ∀ a, Lattice l E (refinement.domain a) (c (refinement.domain a))
    ((ContinuousRational.modulePull (refinement.immersion a)
      (restriction a).rational.hom).obj F)
  reduced : Scheme.FiniteLocallyClosedStratification T
  same_length : reduced.n = refinement.n
  reduction : ∀ a : Fin reduced.n, reduced.domain a ≅
    (refinement.domain (Fin.cast same_length a)).nilradical.subscheme
  reduced_immersion : ∀ a, reduced.immersion a = (reduction a).hom ≫
    (refinement.domain (Fin.cast same_length a)).nilradical.subschemeι ≫
      refinement.immersion (Fin.cast same_length a)
  isReduced : ∀ a, IsReduced (reduced.domain a)
  reduction_lattice : ∀ a, LatticeRestriction l E
    ((reduction a).hom ≫
      (refinement.domain (Fin.cast same_length a)).nilradical.subschemeι)
    (c (refinement.domain (Fin.cast same_length a))) (c (reduced.domain a))
    _ (lattice (Fin.cast same_length a))
  further : ∀ (a : Fin reduced.n) (Y : Scheme.{u}) (f : Y ⟶ reduced.domain a)
    [IsImmersion f], LatticeRestriction l E f (c (reduced.domain a)) (c Y)
    _ (reduction_lattice a).pulled

/-- Ordinary scalar extension for arbitrary internal commutative coefficients.
The formula on pure tensors fixes the comparison, and hence its successive composites.
Source: Stacks 00YV, 03EK, 03EL
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure OrdinaryScalars (X : Scheme.{u})
    (R S : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] where
  extension : Mod.extendScalars φ ⋙
      (InternalAbelianSheafModule.sectionModuleEquivalence (ProEt.topology X) S).functor ≅
    (InternalAbelianSheafModule.sectionModuleEquivalence (ProEt.topology X) R).functor ⋙
      pbcExtend (ProEtale.CondensedRing.sectionRingMap X φ)
  pure_tensors : ∀ (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (U : X.ProEtᵒᵖ)
    (s : (InternalAbelianSheafModule.sectionRingSheaf (ProEt.topology X) S).obj.obj U)
    (m : ((InternalAbelianSheafModule.sectionModuleEquivalence
      (ProEt.topology X) R).functor.obj P).val.obj U),
    (extension.hom.app P).val.app U
      (s • (show (((InternalAbelianSheafModule.sectionModuleEquivalence
        (ProEt.topology X) S).functor.obj ((Mod.extendScalars φ).obj P)).val.obj U) from
          (((InternalAbelianSheafModule.sectionModuleEquivalence
            (ProEt.topology X) R).functor.map ((Mod.extendRestrictAdjunction φ).unit.app P) ≫
              (ProEtale.CondensedRing.sectionModuleComapIso X φ).hom.app
                ((Mod.extendScalars φ).obj P)).val.app U m))) =
      pbcTensorSection (ProEtale.CondensedRing.sectionRingMap X φ)
        ((InternalAbelianSheafModule.sectionModuleEquivalence
          (ProEt.topology X) R).functor.obj P) U s m

/-- The simultaneous coefficient, encoding and stratified lattice assertions.
Constructibility uses an explicit arbitrary lisse-partition witness S below.
The continuous-constructible dependency supplies the canonical inverse-image maps.
Source: BS 6.8.13 first paragraph, Proposition 6.8.4, Remark 6.8.15;
blueprint thm-zl-real-mixed-by-curves paragraph 6
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Family (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] where
  ordinary_scalars : ∀ (X : Scheme.{u})
    (R S : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ], Nonempty (OrdinaryScalars X R S φ)
  coefficients : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], CoefficientFamily l E
  restriction : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : PerAdic.Base D.k) (Y : PerAdic.Base D.k)
    (f : Y.scheme ⟶ X.scheme) [IsImmersion f],
    Restriction l E f ((coefficients E).atScheme X.scheme) ((coefficients E).atScheme Y.scheme)
  composition : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X Y Z : PerAdic.Base D.k)
    (f : Y.scheme ⟶ X.scheme) (g : Z.scheme ⟶ Y.scheme)
    [IsImmersion f] [IsImmersion g],
    (restriction E X Z (g ≫ f)).integral.hom =
      (proEtaleRingInverseImageComp g f).hom.app
        (pbcAdicCompletion X.scheme (pbcIntegralDatum l E)) ≫
      (adicTowerInverseImage g).map (restriction E X Y f).integral.hom ≫
        (restriction E Y Z g).integral.hom ∧
    (restriction E X Z (g ≫ f)).rational.hom =
      (proEtaleRingInverseImageComp g f).hom.app (rationalCoefficientSheaf l X.scheme E) ≫
      (adicTowerInverseImage g).map (restriction E X Y f).rational.hom ≫
        (restriction E Y Z g).rational.hom
  fieldChange : ∀ (E E' : Type u) [NormedField E] [NormedField E']
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E']
    (i : E →ₐ[ℚ_[l]] E') (X : PerAdic.Base D.k),
    FieldChange l E E' i X.scheme ((coefficients E).atScheme X.scheme)
      ((coefficients E').atScheme X.scheme)
  field_restriction : ∀ (E E' : Type u) [NormedField E] [NormedField E']
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E']
    (i : E →ₐ[ℚ_[l]] E') (X Y : PerAdic.Base D.k)
    (f : Y.scheme ⟶ X.scheme) [IsImmersion f],
    (adicTowerInverseImage f).map (fieldChange E E' i X).integral ≫
      (restriction E' X Y f).integral.hom =
        (restriction E X Y f).integral.hom ≫ (fieldChange E E' i Y).integral ∧
    (adicTowerInverseImage f).map (fieldChange E E' i X).rational ≫
      (restriction E' X Y f).rational.hom =
        (restriction E X Y f).rational.hom ≫ (fieldChange E E' i Y).rational
  field_composition : ∀ (E E' E'' : Type u)
    [NormedField E] [NormedField E'] [NormedField E'']
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] E'] [NormedAlgebra ℚ_[l] E'']
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E''] (i : E →ₐ[ℚ_[l]] E') (j : E' →ₐ[ℚ_[l]] E'')
    (X : PerAdic.Base D.k),
    (fieldChange E E'' (j.comp i) X).integral =
      (fieldChange E E' i X).integral ≫ (fieldChange E' E'' j X).integral ∧
    (fieldChange E E'' (j.comp i) X).rational =
      (fieldChange E E' i X).rational ≫ (fieldChange E' E'' j X).rational
  strata : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : PerAdic.Base D.k)
    (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (S : Scheme.FiniteLocallyClosedStratification X.scheme)
    (_hS : ∀ i : Fin S.n, ((proEtaleModuleInverseImage (S.immersion i)
      (rationalCoefficientSheaf l X.scheme E)).obj F).IsFiniteLocallyFree),
    Nonempty (Stratified l E X.scheme (coefficients E).atScheme F S)
```

## New

Every listed declaration, including its signature and body, moves verbatim into
Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData with those same public imports.
The item publicly imports that module, preserving all public availability, and privately
imports the four proof components. The extracted declarations retain their names and
visibility. The theorem continuous_constructible_stratified_lattices keeps its signature.

The new CoefficientGeometry structure copies precisely the restriction, composition,
fieldChange, field_restriction and field_composition fields of Family, with its
coefficient family supplied as a parameter. It adds no hypothesis to Family.

The extracted declaration block (verbatim, identical):

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.StratifiedContinuousLattices

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} X.ProEt

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Continuous coefficient coordinates, with every positive quotient projection fixed.
Source: BS 6.8.2(1),(2) and 6.8.15
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Coefficients (X : Scheme.{u}) where
  integral : pbcAdicCompletion X (pbcIntegralDatum l E) ≅
    latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E)
  rational : latticeCoefficientSheaf X E ≅ rationalCoefficientSheaf l X E
  rational_values : ∀ (U : X.ProEtᵒᵖ) (s : C(U.unop.left, E)) (x : U.unop.left),
    rationalCoefficientValue l E X U (rational.hom.hom.app U (ULift.up s)) x = s x
  finite : ∀ n : ℕ, (pbcAdicRings X (pbcIntegralDatum l E)).obj (op n) ≅
    finiteContinuousCoefficientSheaf l X E n
  finite_constants : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1)) (x : U.unop.left),
    finiteContinuousCoefficientValue l E X n U
      ((finite n).hom.hom.app U (pbcFunctionScalars X (pbcIntegralDatum l E) n |>.app U
        |>.hom <| a)) x = integralCoefficientULift l E n a
  integral_reduction : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
    (s : C(U.unop.left, Padic.coefficientExtensionIntegers l E)) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E X n U
      ((integral.inv ≫ pbcAdicProjection X (pbcIntegralDatum l E) n ≫
        (finite n).hom).hom.app U (ULift.up s)) x).down =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) (s x)
  localization : integralCoefficientLocalization l X E ≅ rationalCoefficientSheaf l X E
  localization_normalized :
    integralCoefficientLocalizationNormalized l E X localization.hom

/-- The specified integral-to-field scalar map, in continuous coordinates.
Source: BS 6.8.2(2), Stacks 03EK
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
abbrev inclusion (X : Scheme.{u}) :=
  latticeCoefficientSheafMap X (Padic.coefficientExtensionIntegers l E).subtype
    continuous_subtype_val

/-- The completed scalar map uses the same integral and rational coordinates.
Source: BS 6.8.2(2)
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def Coefficients.scalar {X : Scheme.{u}} (c : Coefficients l E X) :=
  c.integral.hom ≫ inclusion l E X ≫ c.rational.hom

/-- The rational encoding, with its coefficient transport fixed by the ring chart.
Source: Stacks 00YV; BS 6.8.2
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def Coefficients.rationalEncoding {X : Scheme.{u}} (c : Coefficients l E X) :=
  (ProEtale.CondensedRing.continuousFieldModuleEquivalenceUniverse l E X).trans
    (ProEtale.CondensedRing.ringModuleEquivalenceOfIso X
      ((adicLisseForget X).mapIso c.rational.symm))

/-- The integral encoding is the existing completed section-action encoding.
Source: Stacks 00YV; BS 6.8.2
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
abbrev Coefficients.integralEncoding {X : Scheme.{u}} (c : Coefficients l E X) :=
  ProEtale.CondensedRing.completedContinuousModuleEquivalence l E X c.integral

/-- Underlying abelian sheaf of a commutative coefficient sheaf.
Source: Stacks 00YV
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
abbrev abCoefficients (X : Scheme.{u}) :=
  sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})

/-- The canonical condensed chart followed by the identity section-ring comparison.
Source: BS 6.8.2; HRS Example 3.1
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def chart (X : Scheme.{u}) (R : Type u) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] :=
  ProEtale.ContinuousRingUniverse.comparison X R ≫
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (ProEtale.CondensedRing.continuousSectionRingIso X R).inv

/-- The actual condensed integral-to-rational coefficient map.
Its existing definition and ring-hom instance are owned by
`def-weil-pbc-continuous-scalar-map-universes`, not by the scalar-encoding theorem.
Source: BS 6.8.2, functoriality of pullback from the point
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
abbrev internalInclusion (X : Scheme.{u}) :=
  ProEtale.CondensedRing.continuousInternalScalarMapUniverses l E X

/-- Ordinary module pullback along the continuous-function coefficient map.
Source: Stacks 03D2, 03EL; BS 6.8.15
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def continuousPull {X Y : Scheme.{u}} (f : Y ⟶ X) (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :=
  proEtaleModuleInverseImage f (latticeCoefficientSheaf X R) ⋙
    pbcExtend (ProEtale.continuousCoefficientInverseImageMap f R)

/-- The actual internal inverse-image unit, followed by the coefficient extension unit.
Source: Stacks 03EL; BS 6.8.15
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def internalPullUnit {X Y : Scheme.{u}} (f : Y ⟶ X) (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X))
    (U : X.ProEt) (m : P.X.obj.obj (op U)) :=
  (Mod.extendUnitHom
    (ProEtale.condensedPullbackHom (Profinite.continuousCoefficientRingObj R) f)
    (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj P)).hom.app
      (op ((proEtaleBaseChange f).obj U))
    (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app P.X).hom.app (op U) m)

/-- The lisse criterion, including rank zero and locally varying finite ranks.
Source: BS Definition 6.8.3; Stacks 03DM
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def LisseCriterion (X : Scheme.{u}) (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [TotallyDisconnectedSpace R] : Prop :=
  ∀ P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X),
    ProEtale.CondensedRing.LocallyFree
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X) P ↔
      SheafOfModules.IsFiniteLocallyFree
        ((ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse X R).functor.obj P)


/-- The encoding is the identity on sections, maps and actions, with its actual inverse image.
The unit equation fixes the pullback comparison rather than choosing an arbitrary isomorphism.
Source: Stacks 00YV, 03EL; BS 6.8.15
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Encoding (X : Scheme.{u}) (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [TotallyDisconnectedSpace R] where
  sections : ∀ P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X),
    (SheafOfModules.toSheaf _).obj
      ((ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse X R).functor.obj P)
      ≅ P.X
  identity_sections : ∀ P (U : X.ProEtᵒᵖ) m,
    HEq ((sections P).hom.hom.app U m) m
  identity_maps : ∀ (P Q : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X))
    (g : P ⟶ Q) (U : X.ProEtᵒᵖ),
    HEq
      (SheafOfModules.Hom.val
        ((ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse X R).functor.map g)
        |>.app U) (g.hom.hom.app U)
  lisse : LisseCriterion X R
  restriction : [IsNoetherian X] → ∀ (Y : Scheme.{u}) (f : Y ⟶ X) [IsImmersion f],
    (ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse X R).functor ⋙
      continuousPull f R ≅
      ProEtale.CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) f ⋙
        (ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse Y R).functor
  restriction_unit : ∀ [IsNoetherian X] (Y : Scheme.{u}) (f : Y ⟶ X) [IsImmersion f] P
    (U : X.ProEt) (m :
      ((ProEtale.CondensedRing.continuousLatticeModuleEquivalenceUniverse X R).functor.obj
        P).val.obj (op U)),
    HEq (((restriction Y f).hom.app P).val.app (op ((proEtaleBaseChange f).obj U))
      (ContinuousRational.moduleUnit f
        (ProEtale.continuousCoefficientInverseImageMap f R) _ U m))
      (internalPullUnit f R P U ((sections P).hom.hom.app (op U) m))

/-- Internal scalar extension in the fixed sheaf universe. All size data are derived.
Source: Stacks 03EK; the published internal scalar extension
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
def internalExtend (X : Scheme.{u}) :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  letI : HasSheafify (ProEt.topology X) Ab.{u + 1} :=
    hasSheafifyEssentiallySmallSite _ _
  Mod.extendScalars.{u + 1, u + 2} (internalInclusion l E X)

/-- The integral/rational encoding commutes with scalar restriction and extension.
Both normalization equations use the actual section-action encoding and tensor unit.
Source: Stacks 00YV, 03EK; BS 6.8.2
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure ScalarComparison (X : Scheme.{u}) (c : Coefficients l E X) where
  restriction : Mod.comap (internalInclusion l E X) ⋙ (c.integralEncoding l E).functor ≅
    (c.rationalEncoding l E).functor ⋙ pbcRestrict (c.scalar l E)
  restriction_identity : ∀ P (U : X.ProEtᵒᵖ),
    HEq ((restriction.hom.app P).val.app U) (id : P.X.obj.obj U → P.X.obj.obj U)
  extension : internalExtend l E X ⋙ (c.rationalEncoding l E).functor ≅
    (c.integralEncoding l E).functor ⋙ pbcExtend (c.scalar l E)
  tensor_unit : ∀ P (U : X.ProEtᵒᵖ)
    (m : ((c.integralEncoding l E).functor.obj P).val.obj U),
    (extension.hom.app P).val.app U
      (((c.integralEncoding l E).functor.map
        ((Mod.extendRestrictAdjunction.{u + 1, u + 2} (internalInclusion l E X)).unit.app P) ≫
        restriction.hom.app ((internalExtend l E X).obj P)).val.app U m) =
          pbcTensorSection (c.scalar l E)
            ((c.integralEncoding l E).functor.obj P) U 1 m

/-- One coefficient family, including the normalization of successive locally closed maps.
Source: BS 6.8.2, 6.8.13, 6.8.15; Stacks 00YV, 03EL
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure CoefficientFamily where
  [ultrametric : IsUltrametricDist E]
  atScheme : ∀ X : Scheme.{u}, Coefficients l E X
  integral_chart : ∀ X : Scheme.{u}, IsIso (chart X
    (Padic.coefficientExtensionIntegers l E))
  rational_chart : ∀ X : Scheme.{u}, IsIso (chart X E)
  inclusion_square : ∀ X : Scheme.{u},
    internalInclusion l E X ≫ chart X E =
      chart X (Padic.coefficientExtensionIntegers l E) ≫
        (abCoefficients X).map (inclusion l E X)
  integral_encoding : ∀ X : Scheme.{u}, Encoding X (Padic.coefficientExtensionIntegers l E)
  scalar : ∀ X : Scheme.{u}, ScalarComparison l E X (atScheme X)
  rational_encoding : ∀ X : Scheme.{u}, Encoding X E

/-- A genuine internal lattice inclusion together with its sectionwise encoding.
Source: BS 6.8.13, first paragraph; Stacks 00YV, 03EK
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Lattice (X : Scheme.{u}) (c : Coefficients l E X)
    (F : pbcModules X (rationalCoefficientSheaf l X E)) where
  moduleObject : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousCoefficientRingObj
      (Padic.coefficientExtensionIntegers l E)) X)
  internal_lisse : ProEtale.CondensedRing.LocallyFree
    (condensedRingObj (Profinite.continuousCoefficientRingObj
      (Padic.coefficientExtensionIntegers l E)) X) moduleObject
  internal_inclusion : moduleObject ⟶ (Mod.comap (internalInclusion l E X)).obj
    ((c.rationalEncoding l E).inverse.obj F)
  internal_mono : Mono internal_inclusion
  internal_localization :
    IsIso (Mod.extendHom.{u + 1, u + 2} (internalInclusion l E X) internal_inclusion)
  inclusion : (c.integralEncoding l E).functor.obj moduleObject ⟶
    (pbcRestrict (c.scalar l E)).obj F
  comparison : ScalarComparison l E X c
  same_inclusion : inclusion = (c.integralEncoding l E).functor.map internal_inclusion ≫
    comparison.restriction.hom.app ((c.rationalEncoding l E).inverse.obj F) ≫
      (pbcRestrict (c.scalar l E)).map ((c.rationalEncoding l E).counitIso.hom.app F)
  lisse : ((c.integralEncoding l E).functor.obj moduleObject).IsFiniteLocallyFree
  mono : Mono inclusion
  localization : IsIso (((pbcScalarAdjunction (c.scalar l E)).homEquiv _ _).symm inclusion)

/-- An inclusion stays a lisse full lattice under the actual ordinary inverse image.
The equality fixes the rationalization as the map induced by the pulled inclusion.
Source: BS 6.8.15; Stacks 03EL
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure LatticeRestriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    (cX : Coefficients l E X) (cY : Coefficients l E Y)
    (F : pbcModules X (rationalCoefficientSheaf l X E)) (L : Lattice l E X cX F) where
  integral : (adicTowerInverseImage f).obj
    (pbcAdicCompletion X (pbcIntegralDatum l E)) ⟶
      pbcAdicCompletion Y (pbcIntegralDatum l E)
  rational : (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ⟶
    rationalCoefficientSheaf l Y E
  rational_normalized : rationalCoefficientRestrictionNormalized l E f rational
  integral_normalized :
    (adicTowerInverseImage f).map cX.integral.hom ≫
      ProEtale.continuousCoefficientInverseImageMap f
        (Padic.coefficientExtensionIntegers l E) = integral ≫ cY.integral.hom
  square : (adicTowerInverseImage f).map (cX.scalar l E) ≫ rational =
    integral ≫ cY.scalar l E
  pulled : Lattice l E Y cY
    ((ContinuousRational.modulePull f rational).obj F)
  integral_iso : (ContinuousRational.modulePull f integral).obj
      ((cX.integralEncoding l E).functor.obj L.moduleObject) ≅
    (cY.integralEncoding l E).functor.obj pulled.moduleObject
  same_inclusion : ∀ (U : X.ProEt) (m :
      ((cX.integralEncoding l E).functor.obj L.moduleObject).val.obj (op U)),
    HEq (pulled.inclusion.val.app (op ((proEtaleBaseChange f).obj U))
      (integral_iso.hom.val.app (op ((proEtaleBaseChange f).obj U))
        (ContinuousRational.moduleUnit f integral _ U m)))
      (ContinuousRational.moduleUnit f rational F U (L.inclusion.val.app (op U) m))

/-- The coefficient square and its successive restrictions use the canonical function maps.
Source: BS 6.8.2, 6.8.15; Stacks 03EL
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Restriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    (cX : Coefficients l E X) (cY : Coefficients l E Y) where
  integral : (adicTowerInverseImage f).obj
    (pbcAdicCompletion X (pbcIntegralDatum l E)) ≅
      pbcAdicCompletion Y (pbcIntegralDatum l E)
  rational : (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ≅
    rationalCoefficientSheaf l Y E
  rational_normalized : rationalCoefficientRestrictionNormalized l E f rational.hom
  continuous_integral : IsIso (ProEtale.continuousCoefficientInverseImageMap f
    (Padic.coefficientExtensionIntegers l E))
  integral_normalized :
    (adicTowerInverseImage f).map cX.integral.hom ≫
      ProEtale.continuousCoefficientInverseImageMap f
        (Padic.coefficientExtensionIntegers l E) = integral.hom ≫ cY.integral.hom
  square : (adicTowerInverseImage f).map (cX.scalar l E) ≫ rational.hom =
    integral.hom ≫ cY.scalar l E

/-- Coefficient extension is the actual continuous map, fixed on every compatible quotient.
The relation between exponents allows ramification, hence does not equate uniformizers.
Source: BS 6.8.2, 6.8.15
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure FieldChange (E' : Type u) [NormedField E'] [NormedAlgebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E'] (i : E →ₐ[ℚ_[l]] E') (X : Scheme.{u})
    (c : Coefficients l E X) (c' : Coefficients l E' X) where
  integers : Padic.coefficientExtensionIntegers l E →+*
    Padic.coefficientExtensionIntegers l E'
  integer_values : ∀ a, (integers a).val = i a.val
  continuous : Continuous integers
  integral : pbcAdicCompletion X (pbcIntegralDatum l E) ⟶
    pbcAdicCompletion X (pbcIntegralDatum l E')
  integral_normalized : integral ≫ c'.integral.hom = c.integral.hom ≫
    latticeCoefficientSheafMap X integers continuous
  rational : rationalCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X E'
  rational_normalized : ∀ (U : X.ProEtᵒᵖ)
    (s : (rationalCoefficientSheaf l X E).obj.obj U) (x : U.unop.left),
    rationalCoefficientValue l E' X U (rational.hom.app U s) x =
      i (rationalCoefficientValue l E X U s x)
  square : c.scalar l E ≫ rational = integral ≫ c'.scalar l E'
  quotient_normalized : ∀ (m n : ℕ)
    (h : Padic.coefficientExtensionIdeal l E (m + 1) ≤
      Ideal.comap integers (Padic.coefficientExtensionIdeal l E' (n + 1)))
    (U : X.ProEtᵒᵖ) (s : C(U.unop.left, Padic.coefficientExtensionIntegers l E))
    (x : U.unop.left),
    (finiteContinuousCoefficientValue l E' X n U
      ((integral ≫ pbcAdicProjection X (pbcIntegralDatum l E') n ≫
        (c'.finite n).hom).hom.app U (c.integral.inv.hom.app U (ULift.up s))) x).down =
      Ideal.quotientMap _ integers h
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (m + 1)) (s x))

/-- The finite stratification refines a supplied lisse partition. Its reduction has the
same strata and pulled lattice inclusions; each admits all further locally closed pullbacks.
Source: BS 6.8.13, first paragraph, and 6.8.15; Stacks 054M
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Stratified (T : Scheme.{u}) (c : ∀ X : Scheme.{u}, Coefficients l E X)
    (F : pbcModules T (rationalCoefficientSheaf l T E))
    (S : Scheme.FiniteLocallyClosedStratification T) where
  refinement : Scheme.FiniteLocallyClosedStratification T
  empty : IsEmpty T → refinement.n = 0
  parent : Fin refinement.n → Fin S.n
  factor : ∀ a, refinement.domain a ⟶ S.domain (parent a)
  factor_immersion : ∀ a, IsImmersion (factor a)
  factorization : ∀ a, factor a ≫ S.immersion (parent a) = refinement.immersion a
  restriction : ∀ a, Restriction l E (refinement.immersion a) (c T)
    (c (refinement.domain a))
  lattice : ∀ a, Lattice l E (refinement.domain a) (c (refinement.domain a))
    ((ContinuousRational.modulePull (refinement.immersion a)
      (restriction a).rational.hom).obj F)
  reduced : Scheme.FiniteLocallyClosedStratification T
  same_length : reduced.n = refinement.n
  reduction : ∀ a : Fin reduced.n, reduced.domain a ≅
    (refinement.domain (Fin.cast same_length a)).nilradical.subscheme
  reduced_immersion : ∀ a, reduced.immersion a = (reduction a).hom ≫
    (refinement.domain (Fin.cast same_length a)).nilradical.subschemeι ≫
      refinement.immersion (Fin.cast same_length a)
  isReduced : ∀ a, IsReduced (reduced.domain a)
  reduction_lattice : ∀ a, LatticeRestriction l E
    ((reduction a).hom ≫
      (refinement.domain (Fin.cast same_length a)).nilradical.subschemeι)
    (c (refinement.domain (Fin.cast same_length a))) (c (reduced.domain a))
    _ (lattice (Fin.cast same_length a))
  further : ∀ (a : Fin reduced.n) (Y : Scheme.{u}) (f : Y ⟶ reduced.domain a)
    [IsImmersion f], LatticeRestriction l E f (c (reduced.domain a)) (c Y)
    _ (reduction_lattice a).pulled

/-- Ordinary scalar extension for arbitrary internal commutative coefficients.
The formula on pure tensors fixes the comparison, and hence its successive composites.
Source: Stacks 00YV, 03EK, 03EL
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure OrdinaryScalars (X : Scheme.{u})
    (R S : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] where
  extension : Mod.extendScalars φ ⋙
      (InternalAbelianSheafModule.sectionModuleEquivalence (ProEt.topology X) S).functor ≅
    (InternalAbelianSheafModule.sectionModuleEquivalence (ProEt.topology X) R).functor ⋙
      pbcExtend (ProEtale.CondensedRing.sectionRingMap X φ)
  pure_tensors : ∀ (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (U : X.ProEtᵒᵖ)
    (s : (InternalAbelianSheafModule.sectionRingSheaf (ProEt.topology X) S).obj.obj U)
    (m : ((InternalAbelianSheafModule.sectionModuleEquivalence
      (ProEt.topology X) R).functor.obj P).val.obj U),
    (extension.hom.app P).val.app U
      (s • (show (((InternalAbelianSheafModule.sectionModuleEquivalence
        (ProEt.topology X) S).functor.obj ((Mod.extendScalars φ).obj P)).val.obj U) from
          (((InternalAbelianSheafModule.sectionModuleEquivalence
            (ProEt.topology X) R).functor.map ((Mod.extendRestrictAdjunction φ).unit.app P) ≫
              (ProEtale.CondensedRing.sectionModuleComapIso X φ).hom.app
                ((Mod.extendScalars φ).obj P)).val.app U m))) =
      pbcTensorSection (ProEtale.CondensedRing.sectionRingMap X φ)
        ((InternalAbelianSheafModule.sectionModuleEquivalence
          (ProEt.topology X) R).functor.obj P) U s m

/-- The simultaneous coefficient, encoding and stratified lattice assertions.
Constructibility uses an explicit arbitrary lisse-partition witness S below.
The continuous-constructible dependency supplies the canonical inverse-image maps.
Source: BS 6.8.13 first paragraph, Proposition 6.8.4, Remark 6.8.15;
blueprint thm-zl-real-mixed-by-curves paragraph 6
(blueprint: lem-zl-continuous-constructible-stratified-lattices). -/
structure Family (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] where
  ordinary_scalars : ∀ (X : Scheme.{u})
    (R S : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ], Nonempty (OrdinaryScalars X R S φ)
  coefficients : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], CoefficientFamily l E
  restriction : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : PerAdic.Base D.k) (Y : PerAdic.Base D.k)
    (f : Y.scheme ⟶ X.scheme) [IsImmersion f],
    Restriction l E f ((coefficients E).atScheme X.scheme) ((coefficients E).atScheme Y.scheme)
  composition : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X Y Z : PerAdic.Base D.k)
    (f : Y.scheme ⟶ X.scheme) (g : Z.scheme ⟶ Y.scheme)
    [IsImmersion f] [IsImmersion g],
    (restriction E X Z (g ≫ f)).integral.hom =
      (proEtaleRingInverseImageComp g f).hom.app
        (pbcAdicCompletion X.scheme (pbcIntegralDatum l E)) ≫
      (adicTowerInverseImage g).map (restriction E X Y f).integral.hom ≫
        (restriction E Y Z g).integral.hom ∧
    (restriction E X Z (g ≫ f)).rational.hom =
      (proEtaleRingInverseImageComp g f).hom.app (rationalCoefficientSheaf l X.scheme E) ≫
      (adicTowerInverseImage g).map (restriction E X Y f).rational.hom ≫
        (restriction E Y Z g).rational.hom
  fieldChange : ∀ (E E' : Type u) [NormedField E] [NormedField E']
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E']
    (i : E →ₐ[ℚ_[l]] E') (X : PerAdic.Base D.k),
    FieldChange l E E' i X.scheme ((coefficients E).atScheme X.scheme)
      ((coefficients E').atScheme X.scheme)
  field_restriction : ∀ (E E' : Type u) [NormedField E] [NormedField E']
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E']
    (i : E →ₐ[ℚ_[l]] E') (X Y : PerAdic.Base D.k)
    (f : Y.scheme ⟶ X.scheme) [IsImmersion f],
    (adicTowerInverseImage f).map (fieldChange E E' i X).integral ≫
      (restriction E' X Y f).integral.hom =
        (restriction E X Y f).integral.hom ≫ (fieldChange E E' i Y).integral ∧
    (adicTowerInverseImage f).map (fieldChange E E' i X).rational ≫
      (restriction E' X Y f).rational.hom =
        (restriction E X Y f).rational.hom ≫ (fieldChange E E' i Y).rational
  field_composition : ∀ (E E' E'' : Type u)
    [NormedField E] [NormedField E'] [NormedField E'']
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] E'] [NormedAlgebra ℚ_[l] E'']
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E''] (i : E →ₐ[ℚ_[l]] E') (j : E' →ₐ[ℚ_[l]] E'')
    (X : PerAdic.Base D.k),
    (fieldChange E E'' (j.comp i) X).integral =
      (fieldChange E E' i X).integral ≫ (fieldChange E' E'' j X).integral ∧
    (fieldChange E E'' (j.comp i) X).rational =
      (fieldChange E E' i X).rational ≫ (fieldChange E' E'' j X).rational
  strata : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : PerAdic.Base D.k)
    (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (S : Scheme.FiniteLocallyClosedStratification X.scheme)
    (_hS : ∀ i : Fin S.n, ((proEtaleModuleInverseImage (S.immersion i)
      (rationalCoefficientSheaf l X.scheme E)).obj F).IsFiniteLocallyFree),
    Nonempty (Stratified l E X.scheme (coefficients E).atScheme F S)
```

## Users

`tools/downstream.py Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices
--uses Coefficients Encoding Lattice Family continuous_constructible_stratified_lattices`
reports no downstream modules and no direct importers in the current source. The item
remains attached to its DAG parent; no withdrawal or upstream declaration deletion is made.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | A3 | Publicly reexports identical interfaces; constructor proof from separate components. |
| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | new, A3 | Identical interfaces and public imports; compiled without holes. |
| Sheaf.DeligneLaumon.OrdinarySectionScalarComparison | new, A3 | Imports interfaces and states the ordinary scalar component. |
| Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily | new, A3 | Imports interfaces and states the fixed-field coefficient component. |
| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | new, A3 | Imports interfaces and states coefficient geometry separately. |
| Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices | new, A3 | Imports interfaces and states the lattice-refinement component. |

No target uses a changed definition: all original data bodies and structure fields are
identical. There are no forced consumer adaptations.

## Status

landed 20261025T122437-L-1771548 2026-10-25 (merge of deliver/A3/Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices)
