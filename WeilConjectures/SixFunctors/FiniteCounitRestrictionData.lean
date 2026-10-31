/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteDualizingData
public import WeilConjectures.SixFunctors.FiniteDualizing
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits

/-! # Restriction squares for finite exceptional counits

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower,
prop-coef-integral-dualizing.proof.md, paragraph 2, final sentences
(blueprint: def-coef-finite-counit-restriction-data).

Every compactification is retained explicitly. Natural level n means exponent n+1.
The ordinary etale formulas are transported by the specified comparison isomorphisms;
no ambient pro-etale right adjunction or strict tower is assumed.

Main constructions: `omega`, `value`, `counit`, `transition`, `unitTransition`,
`finiteSections`, `quotientMap`, and `targetConstantMap`.
The restriction-square theorem is assembled in `FiniteCounitRestrictionSquare`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteCounitRestriction

/-- Reexport the recorded site-size witness at its explicit universe, so generic
comparison imports cannot select a different inferred size. This adds no assumption.
Source: blueprint site convention (blueprint: def-coef-finite-counit-restriction-data). -/
instance siteSmall (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  finiteDualizingSiteSmall W

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [hft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [hqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [hsep : IsSeparated (X ↘ Spec (.of D.k))]
  (c : Compactification (X ↘ Spec (.of D.k)))

/-- Finite coefficient rings supply the finiteness instance required by the
ordinary exceptional adjunction. -/
instance finiteCoeff_finite (n : ℕ) : Finite (finiteDualizingCoeff l E n) :=
  haveI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  inferInstance

/-- The exceptional functor at the retained compactification.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def etaleExceptional (n : ℕ) :=
  letI := c.hasCompactification
  Etale.rightDerivedUpperShriek (finiteDualizingCoeff l E n)
    (X ↘ Spec (.of D.k))

/-- The dualizing object at this compactification, before its specified realization.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def etaleOmega (n : ℕ) :=
  (etaleExceptional l E D X c n).obj
    (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))

/-- The ordinary compact-support functor for precisely c.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
abbrev etaleSupport (n : ℕ) :=
  Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c

/-- The ordinary exceptional adjunction at c.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def etaleAdjunction (n : ℕ) : etaleSupport l E D X c n ⊣ etaleExceptional l E D X c n :=
  letI := c.hasCompactification
  Etale.rightDerivedUpperShriekAdjunction
    (finiteDualizingCoeff l E n) (X ↘ Spec (.of D.k)) |>.ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIso (finiteDualizingCoeff l E n) c).symm

/-- The specified finite counit at the regular coefficient object.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def etaleCounit (n : ℕ) :=
  (etaleAdjunction l E D X c n).counit.app
    (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))

/-- The counit-defined u at an arbitrary fixed compactification.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def comparison {m n : ℕ} (h : n ≤ m) :=
  (etaleAdjunction l E D X c n).homEquiv _ _
    (Etale.ExceptionalCoefficients.comparisonInverse (finiteDualizingQuotient l E h) c
        (etaleOmega l E D X c m) ≫
      (Etale.scalarExtension (finiteDualizingQuotient l E h) (Spec (.of D.k))).map
        (etaleCounit l E D X c m) ≫
      (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
        (Spec (.of D.k))).hom)

/-- b is the coefficient comparison followed by compact support of u.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def compactComparison {m n : ℕ} (h : n ≤ m) :=
  Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E h) c
      (etaleOmega l E D X c m) ≫
    (etaleSupport l E D X c n).map (comparison l E D X c h)

/-- d is exactly the scalar-adjunction transpose Res(b) eta.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def etaleTransition {m n : ℕ} (h : n ≤ m) :=
  (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
    (Spec (.of D.k)).smallEtaleTopology (finiteDualizingQuotient l E h))).homEquiv _ _
      (compactComparison l E D X c h)

/-- v is the scalar-adjunction transpose of the regular scalar-unit isomorphism.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def etaleUnitTransition {m n : ℕ} (h : n ≤ m) :=
  (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
    (Spec (.of D.k)).smallEtaleTopology (finiteDualizingQuotient l E h))).homEquiv _ _
      (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
        (Spec (.of D.k))).hom

/-- The canonical comparison pullback at a finite coefficient level.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
abbrev realization (W : Scheme.{u}) (n : ℕ) :
    Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) W ⥤
      DerivedCategory (Sheaf (ProEt.topology W)
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
    W).mapDerivedCategory

/-- The actual exceptional value G_n(A_n), in fixed constant-module coordinates.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def omega (n : ℕ) : DerivedCategory (Sheaf (ProEt.topology X)
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))) :=
  (ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).obj
    (𝟙_ _)

/-- The canonical comparison-unit identification with G_n(A_n).
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def omegaOrigin (n : ℕ) :
    (realization l E X n).obj (etaleOmega l E D X c n) ≅ omega l E D X c n :=
  letI := c.hasCompactification
  Etale.boundaryDualizingComparisonIso (finiteDualizingCoeff l E n) (X ↘ Spec (.of D.k))

/-- The ordinary bounded-below etale origin of omega.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def omegaPlus (n : ℕ) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))) :=
  letI := c.hasCompactification
  ⟨etaleOmega l E D X c n,
    Etale.plus_rightDerivedUpperShriek_obj
      (finiteDualizingCoeff l E n) (X ↘ Spec (.of D.k)) _
      (Etale.boundaryCoefficientPlus (finiteDualizingCoeff l E n) (Spec (.of D.k))).property⟩

/-- F_n omega_n for the actual pro-etale compact-support candidate at c.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def value (n : ℕ) : DerivedCategory (Sheaf (ProEt.topology (Spec (.of D.k)))
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))) :=
  (ProEtale.sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).obj
    (omega l E D X c n)

/-- The specified compact-support realization, including the dualizing origin.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def valueOrigin (n : ℕ) :
    value l E D X c n ≅
      (realization l E (Spec (.of D.k)) n).obj
        ((etaleSupport l E D X c n).obj (etaleOmega l E D X c n)) :=
  (ProEtale.sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).mapIso
      (omegaOrigin l E D X c n).symm ≪≫
    (ProEtale.compactSupportSiteComparison (finiteDualizingCoeff l E n) c).app
      (omegaPlus l E D X c n)

/-- Comparison pullback carries the regular coefficient object to the regular object.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def unitOrigin (n : ℕ) :
    (realization l E (Spec (.of D.k)) n).obj
        (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))) ≅
      𝟙_ (DerivedCategory (Sheaf (ProEt.topology (Spec (.of D.k)))
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))) :=
  (realization l E (Spec (.of D.k)) n).mapIso
      (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
      (Spec (.of D.k))).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (ProEtale.comparisonUpperStarUnitIso (finiteDualizingCoeff l E n) (Spec (.of D.k))) ≪≫
    DerivedCategory.singleFunctorObjUnitIso _

/-- The transported finite exceptional counit, with both unit normalizations retained.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def counit (n : ℕ) : value l E D X c n ⟶
    𝟙_ (DerivedCategory (Sheaf (ProEt.topology (Spec (.of D.k)))
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))) :=
  (valueOrigin l E D X c n).hom ≫
    (realization l E (Spec (.of D.k)) n).map (etaleCounit l E D X c n) ≫
      (unitOrigin l E D n).hom

/-- d in the actual pro-etale categories: the specified realization of its scalar transpose.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def transition {m n : ℕ} (h : n ≤ m) :
    value l E D X c m ⟶
      (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
        (finiteDualizingQuotient l E h)).obj (value l E D X c n) :=
  (valueOrigin l E D X c m).hom ≫
    (realization l E (Spec (.of D.k)) m).map (etaleTransition l E D X c h) ≫
    (ProEtale.pbcDerivedComparisonRestrict.{u} (Spec (.of D.k))
      (finiteDualizingQuotient l E h)).inv.app
        ((etaleSupport l E D X c n).obj (etaleOmega l E D X c n)) ≫
    (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
      (finiteDualizingQuotient l E h)).map (valueOrigin l E D X c n).inv

/-- v in the actual pro-etale categories, with the prescribed regular coefficient origins.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def unitTransition {m n : ℕ} (h : n ≤ m) :
    𝟙_ (DerivedCategory (Sheaf (ProEt.topology (Spec (.of D.k)))
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E m)))) ⟶
      (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
        (finiteDualizingQuotient l E h)).obj (𝟙_ _) :=
  (unitOrigin l E D m).inv ≫
    (realization l E (Spec (.of D.k)) m).map (etaleUnitTransition l E D h) ≫
    (ProEtale.pbcDerivedComparisonRestrict.{u} (Spec (.of D.k))
      (finiteDualizingQuotient l E h)).inv.app
        (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))) ≫
    (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
      (finiteDualizingQuotient l E h)).map (unitOrigin l E D n).hom


/-- The coefficient integers, without an artificial restriction on module size.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
abbrev integralRing := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The actual coefficient quotient, with its target in the common module universe.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def integralQuotient (n : ℕ) : integralRing l E →+* finiteDualizingCoeff l E n :=
  RingHom.ulift.{u + 1, u + 1}
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))

/-- Restriction to R and finite coefficient restriction have their canonical compositor.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def integralRestrictionComp {m n : ℕ} (h : n ≤ m) :
    Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
        (finiteDualizingQuotient l E h) ⋙
      Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k))) (integralQuotient l E m) ≅
    Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k))) (integralQuotient l E n) :=
  Sheaf.derivedRestrictScalarsCompIso.{u} (ProEt.topology (Spec (.of D.k)))
    (f := integralQuotient l E m) (g := finiteDualizingQuotient l E h)
    (gf := integralQuotient l E n) (by ext x; rfl)

/-- Ordinary final-object sections of constant-R-module sheaves.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
abbrev sections :=
  (sheafSections (ProEt.topology (Spec (.of D.k)))
    (ModuleCat.{u + 1} (integralRing l E))).obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))

/-- Additivity is inherited from pointwise addition of section maps.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
instance sections_additive : (sections l E D).Additive where
  map_add := rfl

/-- Evaluation preserves finite limits through the sheaf inclusion.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
instance sections_limits : PreservesFiniteLimits (sections l E D) := by
  change PreservesFiniteLimits
    (sheafToPresheaf (ProEt.topology (Spec (.of D.k)))
      (ModuleCat.{u + 1} (integralRing l E)) ⋙
        (CategoryTheory.evaluation _ _).obj (op (ProEt.mk (𝟙 (Spec (.of D.k))))))
  infer_instance

/-- Exactness of these sections follows from the published algebraically closed point result.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
instance sections_colimits : PreservesFiniteColimits (sections l E D) :=
  letI : IsAlgClosed D.k := pointFibreBaseIsAlgClosed D
  letI : PreservesColimitsOfShape WalkingParallelPair (sections l E D) :=
    ProEtale.preservesColimitsOfShape_sheafSections_of_iso (Iso.refl (Spec (.of D.k))) _
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- Derived point sections after actual constant-R restriction.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def finiteSections (n : ℕ) :=
  Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k))) (integralQuotient l E n) ⋙
    (sections l E D).mapDerivedCategory

/-- The regular quotient module with its actual R-action.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def quotientModule (n : ℕ) : ModuleCat.{u + 1} (integralRing l E) :=
  (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (integralQuotient l E n)).obj
    (ModuleCat.of (finiteDualizingCoeff l E n) (finiteDualizingCoeff l E n))

/-- The genuine R-linear quotient map, defined on residue classes.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def quotientMap {m n : ℕ} (h : n ≤ m) : quotientModule l E m ⟶ quotientModule l E n :=
  ModuleCat.ofHom
    { toFun := finiteDualizingQuotient l E h
      map_add' := (finiteDualizingQuotient l E h).map_add
      map_smul' := fun r x ↦ by
        rcases x with ⟨x⟩
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }

/-- The map C_m to C_n, obtained by applying the same sections functor to d.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def sectionTransition {m n : ℕ} (h : n ≤ m) :=
  (sections l E D).mapDerivedCategory.map
    ((Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
      (integralQuotient l E m)).map (transition l E D X c h) ≫
    (integralRestrictionComp l E D h).hom.app (value l E D X c n))

/-- Sections of v, with the same canonical integral restriction compositor.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def sectionUnitTransition {m n : ℕ} (h : n ≤ m) :=
  (sections l E D).mapDerivedCategory.map
    ((Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
      (integralQuotient l E m)).map (unitTransition l E D h) ≫
    (integralRestrictionComp l E D h).hom.app (𝟙_ _))

/-- The ordinary regular-unit identification used for constant sections.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def ordinaryUnitIso (n : ℕ) :
    (Sheaf.restrictScalars (ProEt.topology (Spec (.of D.k))) (integralQuotient l E n)).obj
        (𝟙_ (Sheaf (ProEt.topology (Spec (.of D.k)))
          (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))) ≅
      (constantSheaf (ProEt.topology (Spec (.of D.k)))
        (ModuleCat.{u + 1} (integralRing l E))).obj (quotientModule l E n) :=
  letI : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (integralQuotient l E n)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
      (integralQuotient l E n)).isLeftAdjoint
  (Sheaf.restrictScalars (ProEt.topology (Spec (.of D.k)))
    (integralQuotient l E n)).mapIso
      (Functor.Monoidal.εIso (constantSheaf (ProEt.topology (Spec (.of D.k)))
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))) ≪≫
    (constantCommuteCompose (ProEt.topology (Spec (.of D.k)))
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (integralQuotient l E n))).app
        (ModuleCat.of (finiteDualizingCoeff l E n) (finiteDualizingCoeff l E n))

/-- The actual map sending a coefficient to its constant section in the regular sheaf.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def constantSections (n : ℕ) :=
  (constantSheafAdj (ProEt.topology (Spec (.of D.k)))
    (ModuleCat.{u + 1} (integralRing l E)) (ProEt.isTerminalMkId _)).unit.app
      (quotientModule l E n) ≫ (sections l E D).map (ordinaryUnitIso l E D n).inv

/-- The exact-functor identification with the single complex of ordinary sections.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def targetSingleIso (n : ℕ) :
    (finiteSections l E D n).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (integralRing l E)) 0).obj
        ((sections l E D).obj
          ((Sheaf.restrictScalars (ProEt.topology (Spec (.of D.k)))
            (integralQuotient l E n)).obj (𝟙_ _))) :=
  (finiteSections l E D n).mapIso (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    (sections l E D).mapDerivedCategory.mapIso
      (((Sheaf.restrictScalars (ProEt.topology (Spec (.of D.k)))
        (integralQuotient l E n)).mapDerivedCategorySingleFunctor 0).app (𝟙_ _)) ≪≫
    ((sections l E D).mapDerivedCategorySingleFunctor 0).app _

/-- The constant-section map in D(R), whose inverse is the canonical target iota.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def targetConstantMap (n : ℕ) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (integralRing l E)) 0).map
      (constantSections l E D n) ≫ (targetSingleIso l E D n).inv

/-- The normalized identity restriction, induced by identity section maps.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def restrictionUnit (n : ℕ) :=
  Functor.mapDerivedCategoryNatIso
      (ProEtale.normalizedOriginRestrictionUnit (ProEt.topology (Spec (.of D.k)))
        (finiteDualizingQuotient l E (le_refl n)) (finiteDualizingQuotient_id l E n)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The specified compositor for restriction along successive quotients.
Source: blueprint paragraph 2 (blueprint: def-coef-finite-counit-restriction-data). -/
def restrictionComp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
        (finiteDualizingQuotient l E hmn) ⋙
      Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
        (finiteDualizingQuotient l E hrm) ≅
    Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
      (finiteDualizingQuotient l E (hmn.trans hrm)) :=
  Sheaf.derivedRestrictScalarsCompIso.{u} (ProEt.topology (Spec (.of D.k)))
    (finiteDualizingQuotient_comp l E hrm hmn)

end WeilConjectures.FiniteCounitRestriction
