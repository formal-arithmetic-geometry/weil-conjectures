/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Derived pullback and derived tensor comparison

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: def-pur-finite-pullback-tensor-comparison).

## Main definitions

* `canonicalFinitePullbackTensor` is the prescribed comparison.
* The helper declarations fix its representative normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField

/-! The comparison families below are fixed by canonical constructions. The
compatibilities are stated as equations on those same comparison maps. -/
/-- Finite unbounded tensor/pullback isomorphism families.
Source: Stacks 07A4 and the blueprint coefficient conventions
(blueprint: def-pur-finite-pullback-tensor-comparison). -/
abbrev FinitePullbackTensorComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [_hX : ∀ x : X, Invertible (l : X.residueField x)]
    [_hY : ∀ y : Y, Invertible (l : Y.residueField y)] :=
  ∀ (M N : proEtaleDerivedCategory Y
      (finiteCoefficientRing l E (n + 1))),
    (finiteDerivedPullback l E n f).obj
        ((finiteIntrinsicDerivedTensor l E Y n).obj (M, N)) ≅
      (finiteIntrinsicDerivedTensor l E X n).obj
        ((finiteDerivedPullback l E n f).obj M,
          (finiteDerivedPullback l E n f).obj N)

/-- Completed integral constructible tensor/pullback isomorphism families.
Source: Stacks 07A4 and the blueprint coefficient conventions
(blueprint: def-pur-finite-pullback-tensor-comparison). -/
abbrev IntegralPullbackTensorComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :=
  ∀ (M N : sfIntegralConstructibleCategory l E Y),
    ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
        (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M, N)) ≅
      ((@constructibleIntegralTensor l _ E _ _ _ X hX)).obj
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M,
          ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)

/-- Rational constructible tensor/pullback isomorphism families.
Source: Stacks 07A4 and the blueprint coefficient conventions
(blueprint: def-pur-finite-pullback-tensor-comparison). -/
abbrev RationalPullbackTensorComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :=
  ∀ (M N : sfRationalConstructibleCategory l E Y),
    ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj
        (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (M, N)) ≅
      ((@rationalDerivedTensor l _ E _ _ _ X hX)).obj
        (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M,
          ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj N)

/-- Common-stage algebraically closed tensor/pullback isomorphism families.
Source: Stacks 07A4 and the blueprint coefficient conventions
(blueprint: def-pur-finite-pullback-tensor-comparison). -/
abbrev CommonStagePullbackTensorComparison
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
      [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :=
  ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
    ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj
        (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (M, N)) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).obj
        (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M,
          ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)

/-- Essential smallness with the site morphism and object sizes retained.
Source: Stacks 00YW (blueprint: def-pur-finite-pullback-tensor-comparison). -/
instance (priority := 3000) pullbackTensorSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _

section FiniteCanonical

open CategoryTheory.Functor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finiteness of the existing positive coefficient quotient.
Source: Serre, Local Fields II.2 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
noncomputable instance pullbackTensorCoefficientFinite (n : ℕ) :
    Finite (finiteCoefficientRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)


/-- The canonical constant-ring identification, with coefficient exponent n + 1.
Source: Stacks 0H7J and 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def pullbackTensorCoefficientIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  letI : Finite (finiteCoefficientRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  asIso (proEtaleCoefficientInverseImageMap f (finiteCoefficientRing l E (n + 1)))


/-- The two recorded K-flat interfaces agree at the small-site coefficient size.
Source: Stacks 06YN (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: apply isKFlatIndependentCoefficients_iff_isKFlat at object size u + 1
and morphism size u. Its right side is the first flat-representative property. -/
theorem pullbackTensorIndependent (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (P : (proEtaleFlatRepresentatives W R).FullSubcategory) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      W.ProEt (inferInstance : Category.{u} W.ProEt) (essentiallySmallSelf.{0, u, u + 1} W.ProEt)
      (ProEt.topology W) R P.obj := by
  exact P.property.1

/-- Restriction of the recorded K-flat model is unique with its component equations.
Source: Stacks 06YS and 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: restrict the model's comparison along the inclusion of flat-term K-flat
representatives. Every component is prescribed in the displayed formula, so
natural-transformation extensionality proves uniqueness. -/
theorem pullbackTensorFiniteRepresentative_existsUnique (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (S : CoefficientClosedStructure
      (CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology W) R))
    (T : CoefficientTensorModels.{u, u + 1, u} (ProEt.topology W) R S) :
    ∃! a : ProEtaleTensorModel W R,
      a.tensor = S.tensor ∧
      ∀ P Q : (proEtaleFlatRepresentatives W R).FullSubcategory,
        HEq (a.representative.hom.app (P,Q))
          (T.comparison.hom.app
            (⟨P.obj, pullbackTensorIndependent W R P⟩,
             ⟨Q.obj, pullbackTensorIndependent W R Q⟩)) := by
  let i := ObjectProperty.ιOfLE
    (P := proEtaleFlatRepresentatives W R)
    (P' := CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology W) (R := R))
    (fun P hP ↦ pullbackTensorIndependent W R ⟨P, hP⟩)
  let e := Functor.isoWhiskerLeft (i.prod i)
    (CoefficientTensorModels.comparison.{u, u + 1, u, u + 2} T)
  let a : ProEtaleTensorModel W R :=
    { tensor := S.tensor
      representative := e }
  refine ⟨a, ⟨rfl, ?_⟩, ?_⟩
  · intro P Q
    rfl
  · intro b hb
    rcases b with ⟨tensor, representative⟩
    rcases hb with ⟨ht, he⟩
    dsimp at ht
    subst tensor
    have hr : representative = a.representative := by
      apply Iso.ext
      apply NatTrans.ext
      funext P
      exact eq_of_heq (he P.1 P.2)
    exact congrArg (fun r ↦ ProEtaleTensorModel.mk S.tensor r) hr

/-- The unique restriction of the prescribed finite tensor model.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def pullbackTensorFiniteModel (W : Scheme.{u}) (n : ℕ) :
    ProEtaleTensorModel W (integralCoefficientCommRingSheaf l E W n) :=
  (pullbackTensorFiniteRepresentative_existsUnique W
    (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n)
    (finiteIntrinsicTensorModels l E W n)).exists.choose

/-- The equality of tensor functors in the preceding normalized restriction.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def pullbackTensorFiniteModelIso (W : Scheme.{u}) (n : ℕ) :
    (pullbackTensorFiniteModel l E W n).tensor ≅ finiteIntrinsicDerivedTensor l E W n :=
  eqToIso (pullbackTensorFiniteRepresentative_existsUnique W
    (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n)
    (finiteIntrinsicTensorModels l E W n)).exists.choose_spec.1


/-- The two finite module presentations have a unique comparison preserving the
actual adjunction-unit sections. Source: Stacks 00YV, 03D2 and 07A4
(blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: identify their right adjoints on sections using the constant-section ring
map. Conjugating this identification by the two normalized adjunctions gives the
comparison. The adjunction unit equation is the displayed section equation.
Taking adjuncts of any second comparison with that equation makes its components
identical on every section, so the comparison is unique. -/
theorem pullbackTensorFiniteRealization_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! e : proEtaleRingModulePullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n) ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f,
      ∀ (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
        (x : M.val.obj (Opposite.op U)),
        (e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          (((proEtaleRingModuleAdjunction f
            (integralCoefficientCommRingSheaf l E Y n)
            (integralCoefficientCommRingSheaf l E X n)
            (pullbackTensorCoefficientIso l E f n)).unit.app M).val.app (Opposite.op U) x) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (Opposite.op U) x := by
  exact openSquarePullbackModel_existsUnique (finiteCoefficientRing l E (n + 1)) f

/-- The uniquely unit-normalized finite module realization.
Source: Stacks 00YV, 03D2 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def pullbackTensorFiniteRealization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorFiniteRealization_existsUnique l E f n).exists.choose


/-- The canonical finite tensor comparison, using the small-site specialization of
ringedTopoiCanonicalDerivedTensorComparison and the prescribed unit-normalized
realization. Its K-flat square is proEtaleCanonicalTensorPullback; the tensor
representative comparisons are exactly finiteIntrinsicTensorModels.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def canonicalFinitePullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@FinitePullbackTensorComparison l _ E _ _ _ X Y f n hX hY) := by
  letI : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  exact fun M N ↦
    ((Functor.mapDerivedCategoryNatIso
      (pullbackTensorFiniteRealization l E f n)).app
        ((finiteIntrinsicDerivedTensor l E Y n).obj (M, N))).symm ≪≫
    (proEtaleRingDerivedPullback f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)).mapIso
        ((pullbackTensorFiniteModelIso l E Y n).app (M,N)).symm ≪≫
    (proEtaleCanonicalTensorComparison f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
      (pullbackTensorFiniteModel l E Y n) (pullbackTensorFiniteModel l E X n)).app (M, N) ≪≫
    (pullbackTensorFiniteModelIso l E X n).app
      ((proEtaleRingDerivedPullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)).obj M,
      (proEtaleRingDerivedPullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)).obj N) ≪≫
    (finiteIntrinsicDerivedTensor l E X n).mapIso
      (Iso.prod ((Functor.mapDerivedCategoryNatIso
        (pullbackTensorFiniteRealization l E f n)).app M)
        ((Functor.mapDerivedCategoryNatIso
          (pullbackTensorFiniteRealization l E f n)).app N))

/-- Associativity is the tensor-functor square for the actual comparison μ.
Source: Stacks 07A4, signed-total proof (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: choose simultaneous flat K-flat representatives for the three inputs.
Both routes carry the pullback of (x tensor y) tensor z to
f*x tensor (f*y tensor f*z), with the same total differential. Localize the
strict equality and use the recorded representative comparisons. -/
theorem canonicalFinitePullbackTensor_associativity {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N P : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finiteDerivedPullback l E n f).map
      ((finiteIntrinsicClosed l E Y n).monoidal.associator M N P).hom ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M
        ((finiteIntrinsicDerivedTensor l E Y n).obj (N,P))).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (𝟙 _) ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) N P).hom) =
    ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
      ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) P).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom (𝟙 _)) ≫
      ((finiteIntrinsicClosed l E X n).monoidal.associator
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)
        ((finiteDerivedPullback l E n f).obj P)).hom := by
  sorry

/-- The unit comparison is uniquely determined by the two unit squares on μ.
Source: Stacks 03EL and 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: on module representatives the unit map identifies f*O_Y with O_X by
sending the inverse-image unit to 1. The two squares hold on pure tensors;
localization gives the displayed squares. For uniqueness, take M to be the
unit, and cancel the unitors and the invertible tensor comparison. -/
theorem canonicalFinitePullbackTensor_unit {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! ε : (finiteDerivedPullback l E n f).obj
        (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit ≅
      (finiteIntrinsicClosed l E X n).monoidal.tensorUnit,
      ∀ M : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)),
        (((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
          (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit M).hom ≫
          (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((finiteIntrinsicClosed l E X n).monoidal.leftUnitor
            ((finiteDerivedPullback l E n f).obj M)).hom =
          (finiteDerivedPullback l E n f).map
            ((finiteIntrinsicClosed l E Y n).monoidal.leftUnitor M).hom) ∧
        (((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M
          (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit).hom ≫
          (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((finiteIntrinsicClosed l E X n).monoidal.rightUnitor
            ((finiteDerivedPullback l E n f).obj M)).hom =
          (finiteDerivedPullback l E n f).map
            ((finiteIntrinsicClosed l E Y n).monoidal.rightUnitor M).hom) := by
  sorry

/-- Composition of pullbacks acts on the same canonical tensor comparison.
Source: Stacks 07A4 and 00YV (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: on flat K-flat representatives both sides are the sheaf pullback tensor
map for h followed by that for f, with the canonical adjunction composition
inserted. The unit formulas for the inverse images agree on every local
section. Totalize and localize this equality. -/
theorem canonicalFinitePullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    ((@canonicalFinitePullbackTensor l _ E _ _ _ Z Y (h ≫ f) n hZ hY) M N).hom ≫
      (finiteIntrinsicDerivedTensor l E Z n).map
        (Prod.mkHom
          ((sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app M)
          ((sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app N)) =
    (sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app
        ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) ≫
      (finiteDerivedPullback l E n h).map
        ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ Z X h n hZ hX)
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)).hom := by
  sorry

/-- Proposition form of the finite associativity equation, for use by the main statement.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def canonicalFinitePullbackTensor_associativity_condition
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
    (finiteDerivedPullback l E n f).map
      ((finiteIntrinsicClosed l E Y n).monoidal.associator M N P).hom ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M
        ((finiteIntrinsicDerivedTensor l E Y n).obj (N,P))).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (𝟙 _) ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
          N P).hom) =
    ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
      ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) P).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
          M N).hom (𝟙 _)) ≫
      ((finiteIntrinsicClosed l E X n).monoidal.associator
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)
        ((finiteDerivedPullback l E n f).obj P)).hom

/-- Proposition form of the finite unit equation, for use by the main statement.
Source: Stacks 03EL, 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def canonicalFinitePullbackTensor_unit_condition
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : (finiteDerivedPullback l E n f).obj
      (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit ≅
      (finiteIntrinsicClosed l E X n).monoidal.tensorUnit,
    ∀ M : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)),
      (((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
        (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit M).hom ≫
        (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((finiteIntrinsicClosed l E X n).monoidal.leftUnitor
          ((finiteDerivedPullback l E n f).obj M)).hom =
      (finiteDerivedPullback l E n f).map
        ((finiteIntrinsicClosed l E Y n).monoidal.leftUnitor M).hom) ∧
      (((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M
        (finiteIntrinsicClosed l E Y n).monoidal.tensorUnit).hom ≫
        (finiteIntrinsicDerivedTensor l E X n).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((finiteIntrinsicClosed l E X n).monoidal.rightUnitor
          ((finiteDerivedPullback l E n f).obj M)).hom =
      (finiteDerivedPullback l E n f).map
        ((finiteIntrinsicClosed l E Y n).monoidal.rightUnitor M).hom)

/-- Proposition form of finite pullback composition, for use by the main statement.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def canonicalFinitePullbackTensor_composition_condition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] : Prop :=
  ∀ (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
    ((@canonicalFinitePullbackTensor l _ E _ _ _ Z Y (h ≫ f) n hZ hY) M N).hom ≫
      (finiteIntrinsicDerivedTensor l E Z n).map
        (Prod.mkHom
          ((sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app M)
          ((sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app N)) =
    (sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app
        ((finiteIntrinsicDerivedTensor l E Y n).obj (M,N)) ≫
      (finiteDerivedPullback l E n h).map
        ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ Z X h n hZ hX)
        ((finiteDerivedPullback l E n f).obj M)
        ((finiteDerivedPullback l E n f).obj N)).hom

end FiniteCanonical

section SignedBraiding
universe a b
/-- The ordinary swap functor on a product category.
Source: Stacks 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def pullbackTensorSwap (D : Type a) [Category.{b} D] : D × D ⥤ D × D where
  obj P := (P.2,P.1)
  map a := Prod.mkHom a.2 a.1

variable {C : Type (u + 1)} [Category.{u} C]
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (A : Sheaf J CommRingCat.{u + 1})

set_option maxHeartbeats 400000 in
-- The two sheafification calculations and the signed summand calculation are checked together.
/-- The signed symmetry is fixed on every pure tensor by (-1)^(pq).
Source: Stacks 06YS (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: swap the two tensor factors in each total summand and multiply by
(-1)^(pq). The two differential identities follow from the Koszul sign rule.
Swapping twice gives the identity. Tensor generators, sheafification and the
coproduct injections uniquely determine the chain map, hence the isomorphism. -/
theorem pullbackTensorSignedTotal_existsUnique
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ) :
    ∃! e : (coefficientTotalTensor.{u, u + 1, u} J A).obj (P,Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} J A).obj (Q,P),
      ∀ (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (e.hom.f k).val.app U (coefficientTensorGenerator.{u, u + 1, u}
          J A P Q p q k h U x y) =
        (p*q).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
          J A Q P q p k ((add_comm q p).trans h) U y x := by
  have sheaf_tensor_braiding
      {C' : Type (u + 1)} [Category.{u} C']
      (J : GrothendieckTopology C') [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
      (A : Sheaf J CommRingCat.{u + 1}) (M N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) :
      letI := SheafOfModules.isMonoidal_W_independentCoefficients A
      letI := SheafOfModules.monoidalCategory A
      letI := SheafOfModules.symmetricCategory A
      (SheafOfModules.tensorObjIsoSheafification M N).inv ≫ (β_ M N).hom =
        (PresheafOfModules.sheafification (𝟙 _)).map (β_ M.val N.val).hom ≫
          (SheafOfModules.tensorObjIsoSheafification N M).inv := by
    let := SheafOfModules.isMonoidal_W_independentCoefficients A
    let := SheafOfModules.monoidalCategory A
    let := SheafOfModules.symmetricCategory A
    simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_inv, Iso.symm_inv,
      MonoidalCategory.tensorIso_hom,
      Functor.Monoidal.μIso_inv]
    erw [Category.assoc, BraidedCategory.braiding_naturality]
    erw [← Category.assoc, Functor.map_braiding]
    simp
    rfl
  -- Apply sheafification naturality to the pure tensor sections.
  have sheaf_tensor_braiding_apply
      {C' : Type (u + 1)} [Category.{u} C']
      (J : GrothendieckTopology C') [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
      (A : Sheaf J CommRingCat.{u + 1}) (M N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
      (U : C'ᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
      letI := SheafOfModules.isMonoidal_W_independentCoefficients A
      letI := SheafOfModules.monoidalCategory A
      letI := SheafOfModules.symmetricCategory A
      (β_ M N).hom.val.app U
        ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
          (((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).unit.app
            (MonoidalCategoryStruct.tensorObj M.val N.val)).app U (x ⊗ₜ[A.obj.obj U] y))) =
      (SheafOfModules.tensorObjIsoSheafification N M).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).unit.app
          (MonoidalCategoryStruct.tensorObj N.val M.val)).app U (y ⊗ₜ[A.obj.obj U] x)) := by
    let := SheafOfModules.isMonoidal_W_independentCoefficients A
    let := SheafOfModules.monoidalCategory A
    let := SheafOfModules.symmetricCategory A
    let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj)
    have hb := congrArg (fun t ↦ t.val.app U
      ((adj.unit.app (MonoidalCategoryStruct.tensorObj M.val N.val)).app U (x ⊗ₜ[A.obj.obj U] y)))
        (sheaf_tensor_braiding J A M N)
    have hn := congrArg (fun t ↦ t.app U (x ⊗ₜ[A.obj.obj U] y))
      (adj.unit.naturality (β_ M.val N.val).hom)
    change (adj.unit.app (MonoidalCategoryStruct.tensorObj N.val M.val)).app U
      (y ⊗ₜ[A.obj.obj U] x) =
      ((PresheafOfModules.sheafification (𝟙 _)).map (β_ M.val N.val).hom).val.app U
        ((adj.unit.app (MonoidalCategoryStruct.tensorObj M.val N.val)).app U
          (x ⊗ₜ[A.obj.obj U] y)) at hn
    exact hb.trans (congrArg ((SheafOfModules.tensorObjIsoSheafification N M).inv.val.app U)
      hn.symm)
  let := SheafOfModules.isMonoidal_W_independentCoefficients A
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.symmetricCategory A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
  let e := CochainComplex.Monoidal.braiding P Q
  have he : ∀ (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      (e.hom.f k).val.app U (coefficientTensorGenerator.{u, u + 1, u}
        J A P Q p q k h U x y) =
      (p*q).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
        J A Q P q p k ((add_comm q p).trans h) U y x := by
    intro p q k h U x y
    change (e.hom.f k).val.app U
      ((HomologicalComplex.ιTensorObj P Q p q k h).val.app U _) = _
    have hb := CochainComplex.Monoidal.ι_braiding_hom (K := P) (L := Q) p q k h
    have hv := congrArg (fun t ↦ t.val.app U
      ((SheafOfModules.tensorObjIsoSheafification (P.X p) (Q.X q)).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).unit.app
          (MonoidalCategoryStruct.tensorObj (P.X p).val (Q.X q).val)).app U
            (x ⊗ₜ[A.obj.obj U] y)))) hb
    change (e.hom.f k).val.app U
      ((HomologicalComplex.ιTensorObj P Q p q k h).val.app U _) = _ at hv
    simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply]
    refine hv.trans ?_
    change ((((SheafOfModules.forget _) ⋙ (PresheafOfModules.evaluation _ U)).map
      (((p*q).negOnePow : ℤ) • ((β_ (P.X p) (Q.X q)).hom ≫
        HomologicalComplex.ιTensorObj Q P q p k ((add_comm q p).trans h)))) _) = _
    rw [Functor.map_zsmul]
    change ((p*q).negOnePow : ℤ) • ((HomologicalComplex.ιTensorObj Q P q p k
      ((add_comm q p).trans h)).val.app U ((β_ (P.X p) (Q.X q)).hom.val.app U _)) = _
    rw [sheaf_tensor_braiding_apply J A]
    rfl
  refine ⟨e, he, ?_⟩
  · intro b hb
    apply Iso.ext
    apply HomologicalComplex.Hom.ext
    funext k
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (P.X p) (Q.X q)).inv).1
    apply (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).homEquiv _ _ |>.injective
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    exact (hb p q k hpq U x y).trans (he p q k hpq U x y).symm

/-- The chain-level Koszul braiding, including its prescribed sign.
Source: Stacks 06YS (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def pullbackTensorSignedTotal
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ) :=
  (pullbackTensorSignedTotal_existsUnique J A P Q).exists.choose

variable [EssentiallySmall.{u + 1} C]
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u + 1, u, u, u + 2} J A))
  (T : CoefficientTensorModels.{u, u + 1, u, u + 2} J A S)

/-- The derived braiding is the descent of the signed total symmetry, fixed on
the full K-flat representative comparison.
Source: Stacks 06YS and 06YU (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: the generator formula is natural in both cochain inputs and preserves
quasi-isomorphisms between K-flat pairs. Localize that natural isomorphism.
The displayed representative square fixes every component by K-flat resolution
and hence gives uniqueness. -/
theorem pullbackTensorBraiding_existsUnique :
    ∃! e : S.tensor ≅ pullbackTensorSwap _ ⋙ S.tensor,
      ∀ (P Q : CochainComplex (SheafOfModules.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := J) (R := A) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := J) (R := A) Q),
        DerivedCategory.Q.map (pullbackTensorSignedTotal J A P Q).hom ≫
          (CoefficientTensorModels.iso.{u, u + 1, u, u + 2} J A S T Q P hQ hP).hom =
        (CoefficientTensorModels.iso.{u, u + 1, u, u + 2} J A S T P Q hP hQ).hom ≫
          e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
  sorry

/-- The signed derived braiding prescribed by the recorded tensor models.
Source: Stacks 06YS and 06YU (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def pullbackTensorBraiding :=
  (pullbackTensorBraiding_existsUnique J A S T).exists.choose
end SignedBraiding

section FiniteSymmetry
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical finite comparison commutes with the signed derived braiding.
Source: Stacks 07A4 and 06YS (blueprint: def-pur-finite-pullback-tensor-comparison).
Proof: on homogeneous generators of degrees p,q both composites send the
pullback of x tensor y to (-1)^(pq) f*y tensor f*x. The representative
normalizations and K-flat descent give the displayed equation for all inputs. -/
theorem canonicalFinitePullbackTensor_braiding {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finiteDerivedPullback l E n f).map
      ((pullbackTensorBraiding (ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)
        (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)).hom.app (M,N)) ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) N M).hom =
    ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom ≫
      (pullbackTensorBraiding (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
        (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)).hom.app
          ((finiteDerivedPullback l E n f).obj M,(finiteDerivedPullback l E n f).obj N) := by
  sorry
end FiniteSymmetry


/-- Proposition form of finite signed braiding, for use by the main statement.
Source: Stacks 06YS, 07A4 (blueprint: def-pur-finite-pullback-tensor-comparison). -/
def canonicalFinitePullbackTensor_braiding_condition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
    (finiteDerivedPullback l E n f).map
      ((pullbackTensorBraiding (ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)
        (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)).hom.app (M,N)) ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) N M).hom =
    ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N).hom ≫
      (pullbackTensorBraiding (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
        (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)).hom.app
          ((finiteDerivedPullback l E n f).obj M,(finiteDerivedPullback l E n f).obj N)

end WeilConjectures
