/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedEtaleOriginWitnesses
public import WeilConjectures.AlgebraicGeometry.Boundary.BoundaryDualizingComposition
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Finite exceptional dualizing comparisons

Source: blueprint order 2140, `lem-coef-finite-dualizing` (blueprint:
lem-coef-finite-dualizing).

The finite term is the specified exceptional inverse image of the regular
coefficient unit.  The transition interface below is the adjunct of the
counit-defined coefficient comparison; it is exposed separately so a strict
normalized tower must identify its transitions with these maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The published ring-sheafification witness with both universes explicit.
Source: blueprint ordinary coefficient sheaves (blueprint: lem-coef-finite-dualizing). -/
instance finiteDualizingRingSheafify (Y : Scheme.{u}) :
    HasSheafify (ProEt.topology Y) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} Y

/-- The published small-site witness at the actual coefficient universe.
Source: blueprint small-site convention (blueprint: lem-coef-finite-dualizing). -/
instance finiteDualizingSiteSmall (Y : Scheme.{u}) :
    EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- `ω_(X,n)=Ra_n^!(A_n)_s`, with the positive level convention `n+1`.
Source: blueprint order 2140 (blueprint: lem-coef-finite-dualizing). -/
def integralDualizingFiniteTerm (D : FiniteFieldDatum.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] (n : ℕ) : normalizedDVRDerived l E X n :=
  letI := hasCompactification_of_finiteType_over_field D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k))
  ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1))
    (HasCompactification.compactification (X ↘ Spec (.of D.k)))).obj
    ((DerivedCategory.singleFunctor
      (scalarReductionTarget.{u, u} l E (Spec (.of D.k)) n) 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) n))))

/-- The coefficient ring in the standard fixed-scalar size presentation.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
abbrev finiteDualizingCoeff (n : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))

/-- The quotient before the standard coefficient-universe lift.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingQuotientBase {m n : ℕ} (h : n ≤ m) :
    Padic.coefficientExtensionRing l E (m + 1) →+*
      Padic.coefficientExtensionRing l E (n + 1) :=
  Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E (m + 1))
    (T := Padic.coefficientExtensionIdeal l E (n + 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The actual quotient homomorphism at positive levels.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingQuotient {m n : ℕ} (h : n ≤ m) :
    finiteDualizingCoeff l E m →+* finiteDualizingCoeff l E n :=
  RingHom.ulift.{u + 1, u + 1} (finiteDualizingQuotientBase l E h)

/-- Identity quotient. Source: blueprint order 2484
(blueprint: lem-coef-finite-dualizing).
Proof: both maps send the residue class of x to the residue class of x. -/
theorem finiteDualizingQuotient_id (n : ℕ) :
    finiteDualizingQuotient l E (le_refl n) = RingHom.id _ := by
  apply RingHom.ext
  intro ⟨x⟩
  exact congrArg ULift.up (DFunLike.congr_fun Ideal.Quotient.factor_eq x)

/-- Quotient composition. Source: blueprint order 2484
(blueprint: lem-coef-finite-dualizing).
Proof: on a representative x both composites give its class in the last quotient. -/
theorem finiteDualizingQuotient_comp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    finiteDualizingQuotient l E (hmn.trans hrm) =
      (finiteDualizingQuotient l E hmn).comp (finiteDualizingQuotient l E hrm) := by
  apply RingHom.ext
  intro ⟨x⟩
  exact congrArg ULift.up (Ideal.Quotient.factor_comp_apply
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hrm 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) x).symm

variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- One fixed compactification for all coefficient levels.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingCompactification : Compactification (X ↘ Spec (.of D.k)) :=
  letI := hasCompactification_of_finiteType_over_field D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k))
  HasCompactification.compactification (X ↘ Spec (.of D.k))

/-- The ordinary etale exceptional functor whose transport is sfFiniteExceptional.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleExceptional (n : ℕ) :
    Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) (Spec (.of D.k)) ⥤
      Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X :=
  letI := (finiteDualizingCompactification D X).hasCompactification
  Etale.rightDerivedUpperShriek (finiteDualizingCoeff l E n)
    (X ↘ Spec (.of D.k))

/-- The ordinary etale dualizing object, at the regular coefficient unit.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleTerm (n : ℕ) :
    Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X :=
  (finiteDualizingEtaleExceptional l E D X n).obj
    (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))

/-- The ordinary etale compact-support functor, for the same compactification.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
abbrev finiteDualizingEtaleSupport (n : ℕ) :=
  Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) (finiteDualizingCompactification D X)

/-- The actual etale exceptional adjunction, with its specified counit.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleAdjunction (n : ℕ) :
    finiteDualizingEtaleSupport l E D X n ⊣ finiteDualizingEtaleExceptional l E D X n :=
  letI := (finiteDualizingCompactification D X).hasCompactification
  Etale.rightDerivedUpperShriekAdjunction
    (finiteDualizingCoeff l E n) (X ↘ Spec (.of D.k))

/-- The dualizing counit, evaluated at the actual regular coefficient object.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleCounit (n : ℕ) :
    (finiteDualizingEtaleSupport l E D X n).obj (finiteDualizingEtaleTerm l E D X n) ⟶
      Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)) :=
  (finiteDualizingEtaleAdjunction l E D X n).counit.app
    (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))

/-- The coefficient comparison of lem-fix-compact-support-coefficient-change,
expressed using the published scalar functor and proper/open canonical mates.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingCompactComparison {m n : ℕ} (h : n ≤ m) :=
  Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E h)
    (finiteDualizingCompactification D X) (finiteDualizingEtaleTerm l E D X m)

/-- The precise counit-defined map u: the inverse compact-support comparison,
coefficient extension of epsilon, and the scalar-unit comparison, transposed under
F_B adjoint G_B. The imported total inverse is used only on the isomorphism domain
asserted in finiteDualizingCoefficientComparisons below.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleComparison {m n : ℕ} (h : n ≤ m) :
    (Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj
      (finiteDualizingEtaleTerm l E D X m) ⟶ finiteDualizingEtaleTerm l E D X n :=
  (finiteDualizingEtaleAdjunction l E D X n).homEquiv _ _
    (Etale.ExceptionalCoefficients.comparisonInverse (finiteDualizingQuotient l E h)
        (finiteDualizingCompactification D X) (finiteDualizingEtaleTerm l E D X m) ≫
      (Etale.scalarExtension (finiteDualizingQuotient l E h) (Spec (.of D.k))).map
        (finiteDualizingEtaleCounit l E D X m) ≫
      (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
        (Spec (.of D.k))).hom)

/-- The semilinear transition is the scalar-adjunction adjunct of u.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleTransition {m n : ℕ} (h : n ≤ m) :
    finiteDualizingEtaleTerm l E D X m ⟶
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (finiteDualizingQuotient l E h)).obj (finiteDualizingEtaleTerm l E D X n) :=
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (finiteDualizingQuotient l E h))).homEquiv _ _
        (finiteDualizingEtaleComparison l E D X h)

/-- Canonical comparison-site realization in intrinsic finite coefficients.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingRealization (Y : Scheme.{u}) (n : ℕ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
    Y).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).functor

/-- The fixed regular coefficient sheaf has its constant generator 1.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingFixedOne (Y : Scheme.{u}) (n : ℕ) (W : Y.ProEtᵒᵖ) :
    (𝟙_ (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))).obj.obj W :=
  (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
    (ModuleCat.of (finiteDualizingCoeff l E n)
      (finiteDualizingCoeff l E n)))).app W (1 : finiteDualizingCoeff l E n)

/-- The regular-module realization is uniquely fixed by 1 mapping to 1.
Source: blueprint order 2484, finite-duality site comparison
(blueprint: lem-coef-finite-dualizing).
Proof: the scalar sheafification unit is locally bijective. Its images of 1 locally
generate the regular module; the linear map sending 1 to 1 therefore glues uniquely.
The reverse construction on the same local generators is its inverse. -/
theorem finiteDualizingIntrinsicUnit_existsUnique (Y : Scheme.{u}) (n : ℕ) :
    ∃! e : (sfIntrinsicModuleEquivalence Y
      (Padic.coefficientExtensionRing l E (n + 1))).functor.obj (𝟙_ _) ≅
        SheafOfModules.unit (integralCoefficientSheaf l E Y n),
      ∀ W : Y.ProEtᵒᵖ, e.hom.val.app W
        (sfIntrinsicRealizationUnit Y (Padic.coefficientExtensionRing l E (n + 1))
          (𝟙_ _) W (finiteDualizingFixedOne l E Y n W)) =
          (1 : (integralCoefficientSheaf l E Y n).obj.obj W) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let J := ProEt.topology Y
  let R := integralCoefficientSheaf l E Y n
  let a := ProEtale.finiteCoefficientIntrinsicScalarMap Y A
  let C := (Functor.const Y.ProEtᵒᵖ).obj
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))
  let P := (ProEtale.finiteCoefficientModulePresheaf Y.ProEt (ULift.{u + 1, u} A)).obj C
  let Q := (ProEtale.finiteCoefficientModulePresheaf Y.ProEt (ULift.{u + 1, u} A)).obj
    (𝟙_ (Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).obj
  let S := PresheafOfModules.sheafification.{u + 1} a
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} a
  let δ := toSheafify J C
  let t : P ⟶ Q :=
    (ProEtale.finiteCoefficientModulePresheaf Y.ProEt (ULift.{u + 1, u} A)).map δ
  let η : P ⟶ (PresheafOfModules.restrictScalars a).obj (SheafOfModules.unit R).val :=
    { app W := ModuleCat.ofHom (X := P.obj W)
        (Y := ((PresheafOfModules.restrictScalars a).obj (SheafOfModules.unit R).val).obj W)
        { toFun := fun x ↦ a.app W x
          map_add' := fun x y ↦ map_add (a.app W).hom x y
          map_smul' := fun x y ↦ map_mul (a.app W).hom x y }
      naturality f := ModuleCat.hom_ext (LinearMap.ext fun x ↦
        ConcreteCategory.congr_hom (a.naturality f) x) }
  let f : S.obj P ⟶ SheafOfModules.unit R :=
    (PresheafOfModules.sheafificationHomEquiv a).symm η
  have hfac : toSheafify J P.presheaf ≫
      (PresheafOfModules.toPresheaf R.obj).map f.val =
        Functor.whiskerRight a (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
    have h := (PresheafOfModules.sheafificationHomEquiv a
      (P := P) (F := SheafOfModules.unit R)).apply_symm_apply η
    exact (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def a f).symm.trans
      (congrArg (fun g ↦ (PresheafOfModules.toPresheaf _).map g) h)
  have hi : Presheaf.IsLocallyInjective J
      (Functor.whiskerRight a (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) :=
    ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J a x y h⟩
  have hs : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight a (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) :=
    ⟨fun x ↦ Presheaf.imageSieve_mem J a x⟩
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply (Sheaf.isLocallyBijective_iff_isIso _).mp
    exact ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J _ hfac, Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac⟩
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  let g := S.map t
  have : IsIso g := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R)]
    change IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
      (Functor.whiskerRight δ
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})))
    rw [← GrothendieckTopology.W_iff, GrothendieckTopology.W_iff_isLocallyBijective]
    constructor
    · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J δ x y h⟩
    · exact ⟨fun x ↦ Presheaf.imageSieve_mem J δ x⟩
  let c := (asIso g).symm ≪≫ asIso f
  have hgc : g ≫ c.hom = f := by simp [c]
  have hc : ∀ W (x : ULift.{u + 1, u} A),
      c.hom.val.app W (sfIntrinsicRealizationUnit Y A (𝟙_ _) W (δ.app W x)) =
        a.app W x := by
    intro W x
    have ht : (adj.unit.app Q).app W (t.app W x) =
        g.val.app W ((adj.unit.app P).app W x) :=
      congrArg (fun k ↦ k.app W (show P.obj W from x)) (adj.unit.naturality t)
    have hg := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.val.app W) hgc) ((adj.unit.app P).app W x)
    have hf : f.val.app W ((adj.unit.app P).app W x) = a.app W x :=
      congrArg (fun k ↦ k.app W (show P.presheaf.obj W from x)) hfac
    change c.hom.val.app W ((adj.unit.app Q).app W (t.app W x)) = a.app W x
    rw [ht]
    exact hg.trans hf
  refine ⟨c, ?_, ?_⟩
  · intro W
    exact (hc W 1).trans (map_one (a.app W).hom)
  · intro d hd
    change S.obj Q ≅ SheafOfModules.unit R at d
    change ∀ W, d.hom.val.app W
      (sfIntrinsicRealizationUnit Y A (𝟙_ _) W
        (δ.app W (1 : ULift.{u + 1, u} A))) = (1 : R.obj.obj W) at hd
    apply Iso.ext
    apply (cancel_epi g).mp
    apply (adj.homEquiv P (SheafOfModules.unit R)).injective
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ULift.{u + 1, u} A at x
    let kd := (adj.homEquiv P (SheafOfModules.unit R)) (g ≫ d.hom)
    let kc := (adj.homEquiv P (SheafOfModules.unit R)) (g ≫ c.hom)
    have hn : (adj.unit.app Q).app W (t.app W (1 : ULift.{u + 1, u} A)) =
        g.val.app W ((adj.unit.app P).app W (1 : ULift.{u + 1, u} A)) :=
      congrArg (fun k ↦ k.app W (show P.obj W from (1 : ULift.{u + 1, u} A)))
        (adj.unit.naturality t)
    have h1 : (kd.app W) (1 : ULift.{u + 1, u} A) =
        (kc.app W) (1 : ULift.{u + 1, u} A) := by
      change d.hom.val.app W (g.val.app W ((adj.unit.app P).app W
          (1 : ULift.{u + 1, u} A))) =
        c.hom.val.app W (g.val.app W ((adj.unit.app P).app W
          (1 : ULift.{u + 1, u} A)))
      rw [← hn]
      exact (hd W).trans ((hc W 1).trans (map_one (a.app W).hom)).symm
    change (kd.app W) x = (kc.app W) x
    have hx : x = x • (1 : ULift.{u + 1, u} A) := by simp
    rw [hx, map_smul, map_smul, h1]

/-- The canonical regular-module realization in degree zero.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingIntrinsicUnit (Y : Scheme.{u}) (n : ℕ) :
    (sfIntrinsicDerivedEquivalence Y
      (Padic.coefficientExtensionRing l E (n + 1))).functor.obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor (scalarReductionTarget l E Y n) 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) :=
  (sfIntrinsicDerivedEquivalence Y
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
      (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((sfIntrinsicModuleEquivalence Y
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapDerivedCategorySingleFunctor
        0).app _ ≪≫
    (DerivedCategory.singleFunctor (scalarReductionTarget l E Y n) 0).mapIso
      (finiteDualizingIntrinsicUnit_existsUnique l E Y n).choose

/-- The site-unit-normalized identification of the etale and intrinsic dualizing objects.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingOrigin (n : ℕ) :
    (finiteDualizingRealization l E X n).obj (finiteDualizingEtaleTerm l E D X n) ≅
      integralDualizingFiniteTerm l E D X n :=
  letI := (finiteDualizingCompactification D X).hasCompactification
  (sfIntrinsicDerivedEquivalence X
    (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
    (Etale.boundaryDualizingComparisonIso (finiteDualizingCoeff l E n)
        (X ↘ Spec (.of D.k)) ≪≫
      (ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1))
        (finiteDualizingCompactification D X)).mapIso
          ((sfIntrinsicDerivedEquivalence (Spec (.of D.k))
            (Padic.coefficientExtensionRing l E (n + 1))).unitIso.app (𝟙_ _) ≪≫
            (sfIntrinsicDerivedEquivalence (Spec (.of D.k))
            (Padic.coefficientExtensionRing l E (n + 1))).inverse.mapIso
              (finiteDualizingIntrinsicUnit l E (Spec (.of D.k)) n)))

/-- Constant-ring realization of a scalar homomorphism, with commutativity forgotten.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingIntrinsicRingMap (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y A) ⟶
      (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y B) :=
  (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ)))

/-- Actual restriction along the constant-sheaf image of the scalar homomorphism.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingIntrinsicRes (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :=
  SheafOfModules.restrictScalars.{u + 1} (finiteDualizingIntrinsicRingMap Y φ)

/-- Additivity of the actual underlying restriction functor.
Source: blueprint coefficient restriction (blueprint: lem-coef-finite-dualizing). -/
instance finiteDualizingIntrinsicRes_additive (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    (finiteDualizingIntrinsicRes Y φ).Additive where
  map_add := by
    intro M N f g
    ext W x
    rfl

private def dualizingEmbedding (Y : Scheme.{u}) (A : Type u) [CommRing A] :=
  sheafToPresheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
    ProEtale.finiteCoefficientModulePresheaf Y.ProEt (ULift.{u + 1, u} A)

private def dualizingFixedRestriction (Y : Scheme.{u}) (A : Type u) [CommRing A] :=
  SheafOfModules.forget.{u + 1} _ ⋙ PresheafOfModules.restrictScalars.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap Y A)

private def dualizingRealizationUnitIso (Y : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    dualizingEmbedding Y A ≅
      (sfIntrinsicModuleEquivalence Y A).functor ⋙ dualizingFixedRestriction Y A := by
  let η := Functor.whiskerLeft (dualizingEmbedding Y A)
    (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap Y A)).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    change IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap Y A)).unit.app
        ((dualizingEmbedding Y A).obj M))
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology Y)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj M).property
  exact asIso η

private def dualizingFixedScalarMap (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    (Functor.const Y.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)) ⟶
      (Functor.const Y.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)) :=
  (Functor.const Y.ProEtᵒᵖ).map (RingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ))

private theorem dualizingScalarSquare (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    ProEtale.finiteCoefficientIntrinsicScalarMap Y A ≫
        (finiteDualizingIntrinsicRingMap Y φ).hom =
      dualizingFixedScalarMap Y φ ≫ ProEtale.finiteCoefficientIntrinsicScalarMap Y B := by
  exact congrArg (fun z ↦ Functor.whiskerRight z
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    (toSheafify_naturality (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ)))).symm

private def dualizingRestrictionSquare (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    finiteDualizingIntrinsicRes Y φ ⋙ dualizingFixedRestriction Y A ≅
      dualizingFixedRestriction Y B ⋙
        PresheafOfModules.restrictScalars (dualizingFixedScalarMap Y φ) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let L := (finiteDualizingIntrinsicRes Y φ ⋙ dualizingFixedRestriction Y A).obj M
    let R := (dualizingFixedRestriction Y B ⋙
      PresheafOfModules.restrictScalars (dualizingFixedScalarMap Y φ)).obj M
    change L ≅ R
    refine PresheafOfModules.isoMk (fun W ↦ ?_) ?_
    · let e : L.obj W ≃ₗ[ULift.{u + 1, u} A] R.obj W :=
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            have h := congrArg (fun z ↦ (z.app W).hom a) (dualizingScalarSquare Y φ)
            exact congrArg (fun b ↦ b • (show M.val.obj W from x)) h }
      exact e.toModuleIso
    · intro W V f
      ext x
      rfl
  · intro M N f
    ext W x
    rfl

/-- Scalar restriction commutes with intrinsic realization, on the same scalar-unit
sections. The generic scalar parameters keep the normalization independent of the
presentation of a finite quotient. Source: blueprint order 2484
(blueprint: lem-coef-finite-dualizing).
Proof: both sides extend the same fixed scalar action along locally bijective
constant-scalar units. The identity on their generating sections extends uniquely,
and its inverse is specified by the same sections. Naturality follows on generators. -/
theorem finiteDualizingRestriction_existsUnique (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    ∃! e : (sfIntrinsicModuleEquivalence Y B).functor ⋙
        finiteDualizingIntrinsicRes Y φ ≅
      Sheaf.restrictScalars (ProEt.topology Y) (RingHom.ulift.{u + 1, u + 1} φ) ⋙
        (sfIntrinsicModuleEquivalence Y A).functor,
      ∀ (M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
        (W : Y.ProEtᵒᵖ) (x : M.obj.obj W),
        HEq ((e.hom.app M).val.app W (sfIntrinsicRealizationUnit Y B M W x))
          (sfIntrinsicRealizationUnit Y A
            ((Sheaf.restrictScalars (ProEt.topology Y)
              (RingHom.ulift.{u + 1, u + 1} φ)).obj M) W x) := by
  let P := PresheafOfModules.restrictScalars (dualizingFixedScalarMap Y φ)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap Y A)
  have : (dualizingFixedRestriction Y A).Full := adj.fullyFaithfulROfIsIsoCounit.full
  have : (dualizingFixedRestriction Y A).Faithful := adj.fullyFaithfulROfIsIsoCounit.faithful
  let e : ((sfIntrinsicModuleEquivalence Y B).functor ⋙
        finiteDualizingIntrinsicRes Y φ) ⋙ dualizingFixedRestriction Y A ≅
      (Sheaf.restrictScalars (ProEt.topology Y) φ.ulift ⋙
        (sfIntrinsicModuleEquivalence Y A).functor) ⋙ dualizingFixedRestriction Y A :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (dualizingRestrictionSquare Y φ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (dualizingRealizationUnitIso Y B).symm P ≪≫
      (Iso.refl _ : dualizingEmbedding Y B ⋙ P ≅
        Sheaf.restrictScalars (ProEt.topology Y) φ.ulift ⋙ dualizingEmbedding Y A) ≪≫
      Functor.isoWhiskerLeft (Sheaf.restrictScalars (ProEt.topology Y) φ.ulift)
        (dualizingRealizationUnitIso Y A) ≪≫
      (Functor.associator _ _ _).symm
  let c := Functor.fullyFaithfulCancelRight (dualizingFixedRestriction Y A) e
  have hc : ∀ M W x, HEq ((c.hom.app M).val.app W
      (sfIntrinsicRealizationUnit Y B M W x))
      (sfIntrinsicRealizationUnit Y A
        ((Sheaf.restrictScalars (ProEt.topology Y) φ.ulift).obj M) W x) := by
    intro M W x
    have h := (dualizingFixedRestriction Y A).map_preimage (e.hom.app M)
    have h' := congrArg (fun k ↦ k.app W (sfIntrinsicRealizationUnit Y B M W x)) h
    change (c.hom.app M).val.app W _ = _ at h'
    rw [h']
    change HEq (((dualizingRealizationUnitIso Y A).hom.app
      ((Sheaf.restrictScalars (ProEt.topology Y) φ.ulift).obj M)).app W
      (((dualizingRealizationUnitIso Y B).inv.app M).app W
        (((dualizingRealizationUnitIso Y B).hom.app M).app W x))) _
    have hu := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app W)
      ((dualizingRealizationUnitIso Y B).hom_inv_id_app M)) x
    exact heq_of_eq (congrArg (fun z ↦ ((dualizingRealizationUnitIso Y A).hom.app
      ((Sheaf.restrictScalars (ProEt.topology Y) φ.ulift).obj M)).app W z) hu)
  refine ⟨c, hc, ?_⟩
  intro d hd
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  let η := ((dualizingRealizationUnitIso Y B).hom.app M).app W
  let η' := ((dualizingRealizationUnitIso Y B).inv.app M).app W
  have hη : η (η' x) = x := by
    change (((dualizingRealizationUnitIso Y B).inv.app M ≫
      (dualizingRealizationUnitIso Y B).hom.app M).app W) x = x
    rw [Iso.inv_hom_id_app]
    rfl
  have h := (hd M W (η' x)).trans (hc M W (η' x)).symm
  change HEq ((d.hom.app M).val.app W (η (η' x)))
    ((c.hom.app M).val.app W (η (η' x))) at h
  rw [hη] at h
  exact eq_of_heq h

private def finiteDualizingQuotientDiagram : ℕᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj n := .of (finiteDualizingCoeff l E n.unop)
  map f := CommRingCat.ofHom (finiteDualizingQuotient l E (leOfHom f.unop))
  map_id n := by
    apply CommRingCat.hom_ext
    exact finiteDualizingQuotient_id l E n.unop
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact finiteDualizingQuotient_comp l E (leOfHom f.unop) (leOfHom g.unop)

/-- The tower quotient restriction is restriction along the actual quotient map.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing).
Proof: consecutive tower maps are sheafifications of the quotient maps. Induction
on the distance between the levels identifies their composite with the single
quotient factor, by its value on residue representatives. Functoriality of constant
sheafification gives equality of ring maps and therefore of restriction functors. -/
theorem finiteDualizingRestriction_eq (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E Y h =
      finiteDualizingIntrinsicRes Y (finiteDualizingQuotientBase l E h) := by
  let Q := finiteDualizingQuotientDiagram l E ⋙
    constantSheaf (ProEt.topology Y) CommRingCat.{u + 1} ⋙
      sheafCompose _ (forget₂ CommRingCat RingCat)
  let e : integralCoefficientSheafSystem l E Y ⟶ Q :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun k ↦ by
      simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp]
      rfl)
  have he := (Category.comp_id _).symm.trans
    ((e.naturality (homOfLE h).op).trans (Category.id_comp _))
  exact congrArg (fun f ↦ SheafOfModules.restrictScalars.{u + 1} f) he

/-- Restriction keeps underlying abelian sheaves, hence is exact.
Source: blueprint coefficient restriction, Stacks 03DA
(blueprint: lem-coef-finite-dualizing).
Proof: kernels are the same sectionwise kernels with restricted action; cokernels
are the same sheafified abelian cokernels. Their scalar actions are precomposed with
phi. Thus this additive functor preserves kernels and cokernels, hence finite limits
and finite colimits. No flatness or characteristic hypothesis is used. -/
theorem finiteDualizingGenericRestriction_exact (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (finiteDualizingIntrinsicRes Y φ) ∧
      PreservesFiniteColimits (finiteDualizingIntrinsicRes Y φ) := by
  let R := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)
  let U := SheafOfModules.toSheaf.{u + 1} R
  have : PreservesFiniteLimits (finiteDualizingIntrinsicRes Y φ ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u + 1} _))
  have : PreservesFiniteColimits (finiteDualizingIntrinsicRes Y φ ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} _))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩

/-- Finite-limit preservation from exact scalar restriction.
Source: blueprint coefficient restriction (blueprint: lem-coef-finite-dualizing). -/
instance finiteDualizingGenericRestriction_limits (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (finiteDualizingIntrinsicRes Y φ) :=
  (finiteDualizingGenericRestriction_exact Y φ).1

/-- Finite-colimit preservation from exact scalar restriction.
Source: blueprint coefficient restriction (blueprint: lem-coef-finite-dualizing). -/
instance finiteDualizingGenericRestriction_colimits (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteColimits (finiteDualizingIntrinsicRes Y φ) :=
  (finiteDualizingGenericRestriction_exact Y φ).2

/-- Derive the scalar-unit-normalized comparison before specializing the coefficients.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingGenericDerivedRestriction (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    (sfIntrinsicDerivedEquivalence Y B).functor ⋙
        (finiteDualizingIntrinsicRes Y φ).mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars (ProEt.topology Y) (RingHom.ulift.{u + 1, u + 1} φ) ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor :=
  letI := (finiteDualizingGenericRestriction_exact Y φ).1
  letI := (finiteDualizingGenericRestriction_exact Y φ).2
  letI := sfIntrinsicModuleEquivalence_functor_additive B Y
  letI := sfIntrinsicModuleEquivalence_functor_additive A Y
  Functor.mapDerivedCategorySquareIso (finiteDualizingRestriction_existsUnique Y φ).choose

/-- The derived comparison is uniquely fixed by the generic section normalization.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing).
Proof: finiteDualizingRestriction_eq identifies the actual tower restriction with
restriction along the single quotient. Exact functor localization respects this
equality, by mapDerivedCategoryNatIso applied to eqToIso. Transport the generic
section-normalized comparison along that equality. It has the displayed HEq, and
any two isomorphisms with that HEq are equal. Thus the theorem determines the
isomorphism itself, including its components, with no choice of automorphism. -/
theorem finiteDualizingIntrinsicRestriction_existsUnique
    (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    ∃! e :
    (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
        normalizedDVRRes l E Y h ≅
      Sheaf.derivedRestrictScalars (ProEt.topology Y) (finiteDualizingQuotient l E h) ⋙
        (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (m + 1))).functor,
      HEq e (finiteDualizingGenericDerivedRestriction Y
        (finiteDualizingQuotientBase l E h)) := by
  have hr : normalizedDVRRes l E Y h =
      (finiteDualizingIntrinsicRes Y (finiteDualizingQuotientBase l E h)).mapDerivedCategory := by
    unfold normalizedDVRRes
    congr 1
    exact finiteDualizingRestriction_eq l E Y h
  rw [hr]
  exact ⟨finiteDualizingGenericDerivedRestriction Y (finiteDualizingQuotientBase l E h),
    HEq.rfl, fun _ he ↦ eq_of_heq he⟩

/-- Exact localization of the section-normalized restriction comparison. Its unique
characterization fixes all components to the generic derived comparison.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingIntrinsicRestriction (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
        normalizedDVRRes l E Y h ≅
      Sheaf.derivedRestrictScalars (ProEt.topology Y) (finiteDualizingQuotient l E h) ⋙
        (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (m + 1))).functor :=
  (finiteDualizingIntrinsicRestriction_existsUnique l E Y h).choose

/-- The canonical restriction square for the full comparison-site realization.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingRealizationRestriction (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    finiteDualizingRealization l E Y n ⋙ normalizedDVRRes l E Y h ≅
      Sheaf.derivedRestrictScalars Y.smallEtaleTopology (finiteDualizingQuotient l E h) ⋙
        finiteDualizingRealization l E Y m :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (finiteDualizingIntrinsicRestriction l E Y h) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ProEtale.pbcDerivedComparisonRestrict Y (finiteDualizingQuotient l E h)) _ ≪≫
    Functor.associator _ _ _

/-- The finite transition is the actual comparison-site image of the scalar adjunct
of the counit-defined u, conjugated by the normalized dualizing origins.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def integralDualizingExceptionalTransition (_hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :
    integralDualizingFiniteTerm l E D X m ⟶
      (normalizedDVRRes l E X h).obj (integralDualizingFiniteTerm l E D X n) :=
  (finiteDualizingOrigin l E D X m).inv ≫
    (finiteDualizingRealization l E X m).map (finiteDualizingEtaleTransition l E D X h) ≫
    (finiteDualizingRealizationRestriction l E X h).inv.app
      (finiteDualizingEtaleTerm l E D X n) ≫
    (normalizedDVRRes l E X h).map (finiteDualizingOrigin l E D X n).hom

/-- Derived extension exists for the actual finite quotient restriction.
Source: blueprint order 2484, derived coefficient extension
(blueprint: lem-coef-finite-dualizing).
Proof: apply derived change of rings on the same small ringed site to the actual
quotient. K-flat resolutions compute the left adjoint, and exact restriction gives
its right adjoint. The universal property fixes the derived adjunction. -/
@[instance]
theorem finiteDualizingRestriction_isRightAdjoint
    (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (normalizedDVRRes l E Y h).IsRightAdjoint := by
  let eB := sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))
  have : (eB.functor ⋙ normalizedDVRRes l E Y h).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso (finiteDualizingIntrinsicRestriction l E Y h).symm
  exact (Functor.isRightAdjoint_comp_iff_right eB.functor _).mp inferInstance

/-- Actual derived finite extension, fixed by its adjunction to normalizedDVRRes.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingExtension (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRDerived l E Y m ⥤ normalizedDVRDerived l E Y n :=
  (normalizedDVRRes l E Y h).leftAdjoint

/-- The intrinsic u is the adjunct of the specified semilinear transition. Thus its
transition is the adjunct of u under derived extension adjoint normalizedDVRRes.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def integralDualizingFiniteComparison (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :
    (finiteDualizingExtension l E X h).obj (integralDualizingFiniteTerm l E D X m) ⟶
      integralDualizingFiniteTerm l E D X n :=
  ((Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _).symm
    (integralDualizingExceptionalTransition l E D X hl h)

end WeilConjectures
