/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-!
# Models for completed-coefficient direct image and its strict quotient tower

This file records the data used to compare the derived direct image of completed-coefficient
modules with the derived limit of the direct images of its finite quotient tower.

## Main definitions

- `RightImage`, `ExactImage`, and `Square`: derived models and their normalized comparisons.
- `SiteData`: exact scalar restrictions, strict coefficient systems, and derived tower limits.
- `ComparisonData`: coefficient coherence, strict diagrams, and complete reconstruction.

## Implementation details

All sites retain their object and morphism universes. The records store universal derived
units and representative normalizations; their existence is proved elsewhere. The interface is
re-exported by `CompletedCoefficientPushforwardComparison`; keeping it in a separate file lets
the independent proof lemmas use it without an import cycle.

## References

* Zheng, Construction 4.1.
* Bhatt–Scholze, Definition 3.5.2.
* Stacks Project, Tags 03CO, 03DA, 03EK, 05RU, 099N (1), (4), 0A07, 0D6E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b av bv c cv z zv d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward

section DerivedModels
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  (F : A ⥤ B) [F.PreservesZeroMorphisms]

/-- A total right derived functor of `F` with its universal unit, computed on K-injective
complexes. -/
structure RightImage where
  functor : DerivedCategory A ⥤ DerivedCategory B
  unit : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor unit (HomologicalComplex.quasiIso A (.up ℤ))
  computes : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (unit.app I)

/-- A derived functor of an exact functor `F`, computed termwise on all complexes. -/
structure ExactImage where
  functor : DerivedCategory A ⥤ DerivedCategory B
  factors : DerivedCategory.Q ⋙ functor ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
/-- An identification of an exact functor `G` with the identity, together with the induced
identification of its derived functor, compatible on complexes. -/
structure ExactIdentity (G : A ⥤ A) [G.PreservesZeroMorphisms] (DG : ExactImage G) where
  ordinary : G ≅ 𝟭 A
  comparison : DG.functor ≅ 𝟭 (DerivedCategory A)
  normalization : ∀ K : CochainComplex A ℤ,
    comparison.hom.app (DerivedCategory.Q.obj K) = DG.factors.hom.app K ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K)
end DerivedModels

section Squares
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{d} C]
  {D : Type z} [Category.{zv} D] [Abelian D] [HasDerivedCategory.{d} D]
  (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [U.PreservesZeroMorphisms]
    [V.PreservesZeroMorphisms]
  (RF : RightImage F) (RG : RightImage G) (DU : ExactImage U) (DV : ExactImage V)

/-- A comparison of the two derived factorizations of a commutative square `F ⋙ V ≅ U ⋙ G`,
normalized on underived complexes by the universal units. -/
structure Square where
  ordinary : F ⋙ V ≅ U ⋙ G
  comparison : RF.functor ⋙ DV.functor ≅ DU.functor ⋙ RG.functor
  normalization : ∀ K : CochainComplex A ℤ,
    DV.functor.map (RF.unit.app K) ≫ comparison.hom.app (DerivedCategory.Q.obj K) ≫
        RG.functor.map (DU.factors.hom.app K) =
      DV.factors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K) ≫
        RG.unit.app ((U.mapHomologicalComplex (.up ℤ)).obj K)
/-- A composition law `F ⋙ V ≅ H` for exact functors together with the induced comparison
of derived functors, compatible on complexes. -/
structure ExactComposition (H : A ⥤ D) [H.PreservesZeroMorphisms]
    (DH : ExactImage H) (E₁ : ExactImage F) (E₂ : ExactImage V) where
  ordinary : F ⋙ V ≅ H
  comparison : E₁.functor ⋙ E₂.functor ≅ DH.functor
  normalization : ∀ K : CochainComplex A ℤ,
    comparison.hom.app (DerivedCategory.Q.obj K) ≫ DH.factors.hom.app K =
      E₂.functor.map (E₁.factors.hom.app K) ≫
        E₂.factors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K)
end Squares

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The category of sheaves of `B`-modules on the small pro-étale site of `W`. -/
abbrev Mod (W : Scheme.{t}) (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :=
  ringedSiteModules.{max u (t + 1)} B

/-- A natural map of module sheaves is the identity on the underlying sections (as a
heterogeneous equality, forgetting the possibly different scalar actions). -/
def IsSectionwiseIdentity (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)})
    {C : Type c} [Category.{cv} C] {F G : C ⥤ Mod W B} (η : F ⟶ G) : Prop :=
  ∀ (M : C) (U : W.ProEtᵒᵖ) (x : (F.obj M).val.obj U),
    HEq ((η.app M).val.app U x) x

/-- The abelian structure on `Mod W B`, with both sheafification universes specified. -/
instance (priority := 20000) modAbelian (W : Scheme.{t})
    (B : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) : Abelian (Mod W B) :=
  { @SheafOfModules.instAbelian.{max u (t + 1), t, max u (t + 1), t + 1}
      W.ProEt inferInstance (ProEt.topology W) B
      (integralCoefficientAbSheafify.{t, u} W)
      (integralCoefficientAbLocallyBijective.{t, u} W) with
    toPreadditive := inferInstance }

/-- The standard derived category, selected uniformly for derived models. -/
instance (priority := 10000) hasDerived {A : Type a} [Category.{av} A] [Abelian A] :
    HasDerivedCategory.{max a av} A := HasDerivedCategory.standard A

/-- Pushforward of ring sheaves along `f` in the coefficient universe. -/
abbrev ringPush {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{max u (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)

/-- The structural map from the constant ring sheaf on `Y` to the pushforward of the constant
ring sheaf on `X`, obtained by sheafification of constant sections. -/
def constantPush {X Y : Scheme.{t}} (f : X ⟶ Y) (A : CommRingCat.{max u (t + 1)}) :
    (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj A) ⟶
    (ringPush.{t, u} f).obj ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t
      + 1)})).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A)) :=
  let B := (proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)
  let h := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A)
    (B.obj ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A))).symm
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  ⟨Functor.whiskerRight h.hom
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- Direct image of module sheaves along `f`, the sectionwise pushforward along the
structural map `c`. -/
abbrev push {X Y : Scheme.{t}} (f : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    {S : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    (c : R ⟶ (ringPush.{t, u} f).obj S) : Mod X S ⥤ Mod Y R :=
  SheafOfModules.pushforward.{max u (t + 1)} c

/-- The coefficient ring of strict coefficient systems: the integers of `E`, lifted. -/
abbrev systemRing := ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)

/-- The uniformizer generating the ideal that defines strict coefficient systems. -/
abbrev systemUniformizer : systemRing.{t, u} l E :=
  ULift.up (Padic.coefficientExtensionUniformizer l E)

/-- Strict semilinear coefficient systems on the pro-étale site of `W`. -/
abbrev Systems (W : Scheme.{t}) :=
  SheafOfModules.CoefficientSystem.{t + 1, t, max u (t + 1)} (J := ProEt.topology W)
    (systemRing.{t, u} l E) (systemUniformizer.{t, u} l E)

/-- The completed integral coefficient ring sheaf on `W`. -/
abbrev R (W : Scheme.{t}) := completedIntegralCoefficientSheafUnrestricted l E W

/-- The constant integral coefficient ring sheaf on `W`. -/
abbrev A (W : Scheme.{t}) := integralConstantRingOfUniverses l E W

/-- The finite coefficient ring sheaf at exponent `n + 1`. -/
abbrev N (W : Scheme.{t}) (n : ℕ) := integralCoefficientSheaf l E W n

/-- The transition map `N W m ⟶ N W n` of the finite coefficient tower, for `n ≤ m`. -/
def quotientMap (W : Scheme.{t}) {m n : ℕ} (h : n ≤ m) : N l E W m ⟶ N l E W n :=
  (integralCoefficientSheafSystem l E W).map (homOfLE h).op

/-- The limit projection from the completed ring to the finite ring at exponent `n + 1`. -/
abbrev projection (W : Scheme.{t}) (n : ℕ) : R l E W ⟶ N l E W n :=
  limit.π (integralCoefficientSheafSystem l E W) (op n)

/-- The finite quotient ring sheaf used by strict systems, as a sheaf of rings. -/
abbrev modelRing (W : Scheme.{t}) (n : ℕ) :
    Sheaf (ProEt.topology W) RingCat.{max u (t + 1)} :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (SheafOfModules.coefficientQuotientSheaf.{t + 1, t, max u (t + 1)} (J := ProEt.topology W)
        (systemRing.{t, u} l E) (systemUniformizer.{t, u} l E) n)

/-- Transport of modules from the strict-system finite quotient ring to `N W n` along a ring
isomorphism `e`: restriction of scalars along `e.inv`. -/
abbrev model (W : Scheme.{t}) (n : ℕ) (e : modelRing l E W n ≅ N l E W n) :=
  SheafOfModules.restrictScalars.{max u (t + 1)} e.inv

/-- The ordinary limit of towers of completed-coefficient module sheaves. -/
abbrev ordinaryTowerLimit (W : Scheme.{t}) :
    (ℕᵒᵖ ⥤ Mod W (R l E W)) ⥤ Mod W (R l E W) := lim

set_option genSizeOf false in
set_option genInjectivity false in
/-- Exact coefficient restrictions on `W` and their quotient composition laws. -/
structure SiteCoefficientData (W : Scheme.{t}) where
  U : ExactImage (SheafOfModules.restrictScalars.{max u (t + 1)}
    (integralConstantToCompletionOfUniverses l E W))
  V : ∀ n, ExactImage (SheafOfModules.restrictScalars.{max u (t + 1)} (projection l E W n))
  restriction : ∀ {m n : ℕ} (h : n ≤ m), ExactImage
    (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W h))
  finiteIso : ∀ n, modelRing l E W n ≅ N l E W n
  finiteIso_generator : ∀ (n : ℕ) (U : W.ProEtᵒᵖ) (a : systemRing.{t, u} l E),
    ((finiteIso n).hom.hom.app U)
        ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (systemRing.{t, u} l E ⧸
            (Ideal.span ({systemUniformizer.{t, u} l E} : Set (systemRing.{t, u} l E))) ^
              (n + 1))))).app U (Ideal.Quotient.mk _ a)) =
      (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U
          (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down))
  restrictionComposition : ∀ {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m),
    ExactComposition
      (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W hmn))
      (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W hkm))
      (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W (hmn.trans hkm)))
      (restriction (hmn.trans hkm)) (restriction hmn) (restriction hkm)
  restrictionComposition_identity : ∀ {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m),
    IsSectionwiseIdentity W (N l E W k) (restrictionComposition hkm hmn).ordinary.hom
  restrictionIdentity : ∀ n, ExactIdentity
    (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W (le_refl n)))
    (restriction (le_refl n))
  restrictionIdentity_sections : ∀ n,
    IsSectionwiseIdentity W (N l E W n) (restrictionIdentity n).ordinary.hom
  projectionComposition : ∀ {m n : ℕ} (h : n ≤ m),
    ExactComposition
      (SheafOfModules.restrictScalars.{max u (t + 1)} (quotientMap l E W h))
      (SheafOfModules.restrictScalars.{max u (t + 1)} (projection l E W m))
      (SheafOfModules.restrictScalars.{max u (t + 1)} (projection l E W n))
      (V n) (restriction h) (V m)
  projectionComposition_identity : ∀ {m n : ℕ} (h : n ≤ m),
    IsSectionwiseIdentity W (R l E W) (projectionComposition h).ordinary.hom

set_option genSizeOf false in
set_option genInjectivity false in
/-- The restriction of semilinear coefficient systems to towers of completed-coefficient
modules, with its evaluations. -/
structure SystemRestrictionData (W : Scheme.{t}) extends SiteCoefficientData l E W where
  systemRestriction : Systems l E W ⥤ (ℕᵒᵖ ⥤ Mod W (R l E W))
  [systemRestrictionAdditive : systemRestriction.Additive]
  systemEvaluation : ∀ n, systemRestriction ⋙ (evaluation ℕᵒᵖ (Mod W (R l E W))).obj (op n) ≅
    SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology W)
      (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
        model l E W n (finiteIso n) ⋙
          SheafOfModules.restrictScalars.{max u (t + 1)} (projection l E W n)
  systemEvaluation_identity : ∀ n,
    IsSectionwiseIdentity W (R l E W) (systemEvaluation n).hom
  systemTransition : ∀ (M : Systems l E W) (n : ℕ) (U : W.ProEtᵒᵖ),
    HEq (fun x ↦ (((systemRestriction.obj M).map (homOfLE (Nat.le_succ n)).op).val.app U) x)
      (fun x ↦ ((M.transition n).val.app U) x)
  systemMap : ∀ (M M' : Systems l E W) (h : M ⟶ M') (n : ℕ) (U : W.ProEtᵒᵖ),
    HEq (fun x ↦ (((systemRestriction.map h).app (op n)).val.app U) x)
      (fun x ↦ ((h.app n).val.app U) x)
  systemFactors : ExactImage systemRestriction

attribute [instance] SystemRestrictionData.systemRestrictionAdditive

set_option genSizeOf false in
set_option genInjectivity false in
/-- The ordinary tower limit, its total derived functor and the normalized limit
projections. -/
structure SiteLimitData (W : Scheme.{t}) where
  [limitAdditive : (ordinaryTowerLimit l E W).Additive]
  limit : RightImage (ordinaryTowerLimit l E W)
  evaluation : ∀ n, ExactImage ((CategoryTheory.evaluation ℕᵒᵖ (Mod W (R l E W))).obj (op n))
  limitProjection : ∀ n, limit.functor ⟶ (evaluation n).functor
  limitProjection_normalization : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ Mod W (R l E W)) ℤ) n,
    limit.unit.app M ≫ (limitProjection n).app (DerivedCategory.Q.obj M) ≫
        (evaluation n).factors.hom.app M =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (lim.π (op n) : (ordinaryTowerLimit l E W) ⟶
          (CategoryTheory.evaluation ℕᵒᵖ (Mod W (R l E W))).obj (op n)) (.up ℤ)).app M)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Site-side coefficient restrictions, strict systems, and total derived limits on `W`. -/
structure SiteData (W : Scheme.{t}) extends
    SystemRestrictionData l E W, SiteLimitData l E W where

variable {X Y : Scheme.{t}} (f : X ⟶ Y)

/-- The structural map for the finite coefficient ring at exponent `n + 1`. -/
abbrev finiteStructure (n : ℕ) :=
  constantPush.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The structural map for the constant integral coefficient ring. -/
abbrev constantStructure :=
  constantPush.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

/-- A map `a` from `P` into the ordinary limit of a reduction tower `C` of `P` is the
augmentation: in every degree and at every level it is `x ↦ x ⊗ 1`. -/
def IsReductionAugmentation (W : Scheme.{t})
    (P : CochainComplex (Mod W (R l E W)) ℤ)
    (C : CochainComplex (ℕᵒᵖ ⥤ Mod W (R l E W)) ℤ)
    (e : C.asFunctor ≅ unrestrictedIntegralComplexTower l E W P)
    (a : P ⟶ ((ordinaryTowerLimit l E W).mapHomologicalComplex
      (.up ℤ)).obj C) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X i).val.obj U),
    ((a.f i ≫ limit.π (C.X i) (op n) ≫ (e.hom.app (op n)).f i).val.app U) x =
      unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x

set_option genSizeOf false in
set_option genInjectivity false in
/-- The direct images along `f` and the normalized constant and finite coefficient
squares. -/
structure CoefficientImageData where
  source : SiteData l E X
  target : SiteData l E Y
  structureMap : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X)
  structureProjection : ∀ n, structureMap ≫ (ringPush.{t, u} f).map (projection l E X n) =
    projection l E Y n ≫ finiteStructure l E f n
  [completedAdditive : (push f structureMap).Additive]
  [constantAdditive : (push f (constantStructure l E f)).Additive]
  [finiteAdditive : ∀ n, (push f (finiteStructure l E f n)).Additive]
  completedImage : RightImage (push f structureMap)
  constantImage : RightImage (push f (constantStructure l E f))
  finiteImage : ∀ n, RightImage (push f (finiteStructure l E f n))
  constantSquare : Square (push f structureMap) (push f (constantStructure l E f))
    (SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses l E X))
    (SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses l E Y))
    completedImage constantImage source.U target.U
  finiteSquare : ∀ n, Square (push f (finiteStructure l E f n)) (push f structureMap)
    (SheafOfModules.restrictScalars (projection l E X n))
    (SheafOfModules.restrictScalars (projection l E Y n))
    (finiteImage n) completedImage (source.V n) (target.V n)
  quotientSquare : ∀ {m n : ℕ} (h : n ≤ m),
    Square (push f (finiteStructure l E f n)) (push f (finiteStructure l E f m))
      (SheafOfModules.restrictScalars (quotientMap l E X h))
      (SheafOfModules.restrictScalars (quotientMap l E Y h))
      (finiteImage n) (finiteImage m) (source.restriction h) (target.restriction h)

attribute [instance] CoefficientImageData.completedAdditive

set_option genSizeOf false in
set_option genInjectivity false in
/-- The section identities, restriction coherence, and completion-projection compatibility. -/
structure CoefficientComparisonData extends CoefficientImageData l E f where
  constantOrdinary_identity :
    IsSectionwiseIdentity Y (A l E Y) constantSquare.ordinary.hom
  finiteOrdinary_identity : ∀ n,
    IsSectionwiseIdentity Y (R l E Y) (finiteSquare n).ordinary.hom
  quotientOrdinary_identity : ∀ {m n : ℕ} (h : n ≤ m),
    IsSectionwiseIdentity Y (N l E Y m) (quotientSquare h).ordinary.hom
  quotientIdentity : ∀ n (K : DerivedCategory (Mod X (N l E X n))),
    (quotientSquare (le_refl n)).comparison.hom.app K ≫
        (finiteImage n).functor.map ((source.restrictionIdentity n).comparison.hom.app K) =
      (target.restrictionIdentity n).comparison.hom.app ((finiteImage n).functor.obj K)
  quotientCoherence : ∀ {k m n : ℕ} (hkm : m ≤ k) (hmn : n ≤ m)
    (K : DerivedCategory (Mod X (N l E X n))),
    (quotientSquare (hmn.trans hkm)).comparison.hom.app K ≫
        (finiteImage k).functor.map ((source.restrictionComposition hkm hmn).comparison.inv.app K) =
      (target.restrictionComposition hkm hmn).comparison.inv.app ((finiteImage n).functor.obj K) ≫
        (target.restriction hkm).functor.map ((quotientSquare hmn).comparison.hom.app K) ≫
        (quotientSquare hkm).comparison.hom.app ((source.restriction hmn).functor.obj K)
  projectionCoherence : ∀ {m n : ℕ} (h : n ≤ m) (K : DerivedCategory (Mod X (N l E X n))),
    (finiteSquare n).comparison.hom.app K =
      (target.projectionComposition h).comparison.inv.app ((finiteImage n).functor.obj K) ≫
        (target.V m).functor.map ((quotientSquare h).comparison.hom.app K) ≫
        (finiteSquare m).comparison.hom.app ((source.restriction h).functor.obj K) ≫
        completedImage.functor.map ((source.projectionComposition h).comparison.hom.app K)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The comparison on derived strict coefficient diagrams and its normalized limit projections. -/
structure DiagramComparisonData extends CoefficientComparisonData l E f where
  systemPush : Systems l E X ⥤ Systems l E Y
  [systemPushAdditive : systemPush.Additive]
  systemPushEvaluation : ∀ n,
    systemPush ⋙
      SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology Y)
      (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
        model l E Y n (target.finiteIso n) ≅
      SheafOfModules.coefficientEvaluation.{t + 1, t, max u (t + 1)} (J := ProEt.topology X)
        (O := systemRing.{t, u} l E) (ell := systemUniformizer.{t, u} l E) n ⋙
          model l E X n (source.finiteIso n) ⋙ push f (finiteStructure l E f n)
  systemPushEvaluation_identity : ∀ n,
    IsSectionwiseIdentity Y (N l E Y n) (systemPushEvaluation n).hom
  systemImage : RightImage systemPush
  towerImage : RightImage ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f structureMap))
  diagramSquare : Square systemPush
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f structureMap))
    source.systemRestriction target.systemRestriction systemImage towerImage
    source.systemFactors target.systemFactors
  diagramOrdinary_identity : ∀ (M : Systems l E X) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((target.systemRestriction.obj (systemPush.obj M)).obj (op n)).val.obj U),
      HEq ((((diagramSquare.ordinary.hom.app M).app (op n)).val.app U) x) x
  towerEvaluation : ∀ n, Square
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f structureMap)) (push f structureMap)
    ((evaluation ℕᵒᵖ (Mod X (R l E X))).obj (op n))
    ((evaluation ℕᵒᵖ (Mod Y (R l E Y))).obj (op n))
    towerImage completedImage (source.evaluation n) (target.evaluation n)
  towerEvaluation_identity : ∀ n,
    IsSectionwiseIdentity Y (R l E Y) (towerEvaluation n).ordinary.hom
  ordinaryLimit :
    (ordinaryTowerLimit l E X) ⋙ push f structureMap ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f structureMap) ⋙
        (ordinaryTowerLimit l E Y)
  ordinaryLimit_projections : ∀ M, ordinaryLimit.hom.app M = limit.post M (push f structureMap)
  limitComparison : source.limit.functor ⋙ completedImage.functor ≅
    towerImage.functor ⋙ target.limit.functor
  limitNormalization : ∀ C : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ,
    completedImage.unit.app
        (((ordinaryTowerLimit l E X).mapHomologicalComplex
          (.up ℤ)).obj C) ≫
      completedImage.functor.map (source.limit.unit.app C) ≫
        limitComparison.hom.app (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinaryLimit (.up ℤ)).hom.app C) ≫
        target.limit.unit.app
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (push f structureMap)).mapHomologicalComplex
            (.up ℤ)).obj C) ≫ target.limit.functor.map (towerImage.unit.app C)
  limitProjection : ∀ (M : DerivedCategory (ℕᵒᵖ ⥤ Mod X (R l E X))) n,
    limitComparison.hom.app M ≫ (target.limitProjection n).app (towerImage.functor.obj M) ≫
        (towerEvaluation n).comparison.hom.app M =
      completedImage.functor.map ((source.limitProjection n).app M)

set_option genSizeOf false in
set_option genInjectivity false in
/-- All coefficient comparisons, strict derived diagrams, and the reconstruction of derived
complete objects from their reduction towers. -/
structure ComparisonData extends DiagramComparisonData l E f where
  preservesComplete : ∀ K : DerivedCategory (Mod X (R l E X)),
    IsDerivedCompleteUnrestricted l E X K →
      IsDerivedCompleteUnrestricted l E Y (completedImage.functor.obj K)
  strictReductionExists : ∀ P : CochainComplex (Mod X (R l E X)) ℤ,
    ∃ C : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ,
      Nonempty (C.asFunctor ≅ unrestrictedIntegralComplexTower l E X P)
  reductionAugmentation : ∀ (P : CochainComplex (Mod X (R l E X)) ℤ)
    (C : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ)
    (e : C.asFunctor ≅ unrestrictedIntegralComplexTower l E X P),
    ∃! a : P ⟶ ((ordinaryTowerLimit l E X).mapHomologicalComplex
      (.up ℤ)).obj C, IsReductionAugmentation l E X P C e a
  reconstruction : ∀ (K : DerivedCategory (Mod X (R l E X)))
    (P : CochainComplex (Mod X (R l E X)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E X) P →
    (∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} X.ProEt
      inferInstance (ProEt.topology X) inferInstance
      (integralCoefficientAbLocallyBijective.{t, u} X)
      (integralCoefficientAbSheafify.{t, u} X).isRightAdjoint
      (completedIntegralCommRingSheafUnrestricted l E X) (P.X i)) →
    ∀ (r : DerivedCategory.Q.obj P ≅ K)
      (C : CochainComplex (ℕᵒᵖ ⥤ Mod X (R l E X)) ℤ)
      (e : C.asFunctor ≅ unrestrictedIntegralComplexTower l E X P)
      (a : P ⟶ ((ordinaryTowerLimit l E X).mapHomologicalComplex
        (.up ℤ)).obj C),
    IsReductionAugmentation l E X P C e a → IsDerivedCompleteUnrestricted l E X K →
      IsIso (completedImage.functor.map (r.inv ≫ DerivedCategory.Q.map a ≫ source.limit.unit.app C)
        ≫
        limitComparison.hom.app (DerivedCategory.Q.obj C))

end WeilConjectures.CompletedCoefficientPushforward
