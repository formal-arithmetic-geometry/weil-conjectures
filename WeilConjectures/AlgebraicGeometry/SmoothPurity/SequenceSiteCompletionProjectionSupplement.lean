/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import all WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import all WeilConjectures.CategoryTheory.Constant.ConstantTowerNormalization
import all WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.SequenceSiteCompletionProjection

/-! # The constant/limit ringed sequence projection

Source: Stacks, sites-cohomology.tex, Tags 0940 and 06YY; Zheng, Construction 4.1,
printed p. 21 (blueprint: lem-pur-sequence-site-completion-projection).

The index `n : ℕ` denotes the positive level `n+1`. All systems retain their actual
horizontal section maps. The record below specifies the geometric morphism, its
ordinary module adjunction, and its simultaneous K-flat derived comparison.

## Main definitions

- `CategoryTheory.RingedToposMorphismOfUniverses`: the same ringed-topos fields
  as the recorded interface, with independent site universes.
- `completionSystemEquivalence`: the equivalence in the recorded systems realization.
- `SequenceSetProjection`: the constant/limit geometric morphism and ring map.
- `SequenceModuleRestriction`: exact scalar restriction with the actual transitions.
- `SequenceOrdinaryPullback`: the normalized simultaneous ordinary tensor model.
- `SequenceDerivedPullback`: the unbounded derived functor and representative comparison.
- `SequenceCompletionProjection`: the preceding compatible canonical data.

## Main statements

- `sequenceSiteCompletionProjection`: exactness of the canonical equivalence and
  existence of the compatible constant/limit projection data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 11000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe c d v w r
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [-instance] ringedToposRingForgetCompose
scoped[CategoryTheory] attribute [instance 1100] ringedToposRingForgetCompose

attribute [-instance] ringedToposAbelianForgetCompose
scoped[CategoryTheory] attribute [instance 1100] ringedToposAbelianForgetCompose

attribute [-instance] ringedToposCommRingForgetCompose
scoped[CategoryTheory] attribute [instance 1100] ringedToposCommRingForgetCompose

attribute [instance] RingedToposMorphismOfUniverses.additive

end CategoryTheory

open scoped CategoryTheory

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  (B : ℕ → Sheaf J CommRingCat.{r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The sequence-site realization of strict systems used by the recorded model.
Source: Zheng, Construction 4.1, p. 21; Stacks 0940
(blueprint: lem-pur-sequence-site-completion-projection).

`def-coef-semilinear-system-models` defines `Systems` as these very module sheaves.
Thus the canonical equivalence in this realization is the identity on the actual
objects, horizontal restrictions, scalar actions and morphisms. -/
def completionSystemEquivalence :
    Mod.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J B τ) ≌
      Systems.{c, v, r} J B τ :=
  CategoryTheory.Equivalence.refl

/-- The underlying sheaf of sets of the existing module category.
Source: Stacks 03D1 and 03D6
(blueprint: lem-pur-sequence-site-completion-projection). -/
abbrev completionUnderlying (R : Sheaf J CommRingCat.{r}) :
    Mod.{c, v, r} J R ⥤ Sheaf J (Type r) :=
  SheafOfModules.toSheaf (ring.{c, v, r} J R) ⋙
    sheafCompose J (forget AddCommGrpCat.{r})

/-- The existing ordinary localization, with the recorded size instance explicit.
Source: Stacks 05RU and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
abbrev completionLocalization (R : Sheaf J CommRingCat.{r}) :
    CochainComplex (Mod.{c, v, r} J R) ℤ ⥤ D.{c, v, r} J R :=
  @DerivedCategory.Q (Mod.{c, v, r} J R) _ _ (hasDerived.{c, v, r} J R)

/-- A sheafified pure scalar-extension tensor, in the dependency's actual ordinary model.
Source: Stacks 03CZ and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
def completionScalarSection {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    (A : ScalarData.{c, v, r} φ) (M : Mod.{c, v, r} J R) (U : Cᵒᵖ)
    (a : S.obj.obj U) (x : M.val.obj U) : (A.model.E.obj M).val.obj U :=
  @SMul.smul ((ring.{c, v, r} J S).obj.obj U) ((A.model.E.obj M).val.obj U)
    ((A.model.E.obj M).val.obj U).isModule.toSMul a
      ((eqToHom (C := Mod.{c, v, r} J S) (A.model.obj_eq M).symm).val.app U
        (extensionUnit.{c, v, r} φ M U x))

/-- The constant/limit geometric morphism with its canonical structural ring map.
The section equations fix the coordinate-wise adjunction and ring projection.
No condition on coefficient flatness or transition surjectivity is imposed.
Source: Stacks 0940, 03D6, 03D7 and 06YY; Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-sequence-site-completion-projection). -/
structure SequenceSetProjection (b : Cone (rings.{c, v, r} J B τ)) where
  /-- The ringed geometric morphism, with the induced action on module direct image. -/
  π : RingedToposMorphismOfUniverses
    (ring.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J B τ))
    (ring.{c, v, r} J b.pt)
  /-- Inverse image is the actual constant sequence, on presheaves and their maps. -/
  inverseUnderlying : π.inverse ⋙ sheafToPresheaf (coefficientSequenceTopology J) (Type r) ≅
    sheafToPresheaf J (Type r) ⋙
      (Functor.whiskeringLeft (ℕ × C)ᵒᵖ Cᵒᵖ (Type r)).obj (CategoryTheory.Prod.snd ℕ C).op
  /-- The structural map has exactly the prescribed inverse-limit projections. -/
  ring_section : ∀ (n : ℕ) (U : Cᵒᵖ) (a : b.pt.obj.obj U),
    π.ringMap.hom.app (op (n, U.unop))
      (((inverseUnderlying.inv.app
        ((sheafCompose J (forget RingCat.{r})).obj (ring.{c, v, r} J b.pt))).app
          (op (n, U.unop))) a) = (b.π.app (op n)).hom.app U a
  /-- The actual set-sheaf tower obtained by restriction to vertical slices. -/
  setsTower : Sheaf (coefficientSequenceTopology J) (Type r) ⥤
    (ℕᵒᵖ ⥤ Sheaf J (Type r))
  /-- The vertical component is restriction, with the identity section identification. -/
  setsTower_obj : ∀ (F : Sheaf (coefficientSequenceTopology J) (Type r)) (n : ℕ),
    (setsTower.obj F).obj (op n) =
      ((Prod.sectR n C).sheafPushforwardContinuous (Type r)
        J (coefficientSequenceTopology J)).obj F
  /-- Horizontal maps remain the actual presheaf restrictions. -/
  setsTower_transition : ∀ (F : Sheaf (coefficientSequenceTopology J) (Type r))
    (m n : ℕ) (h : n ≤ m) (U : Cᵒᵖ),
    HEq (fun x ↦ (((setsTower.obj F).map (homOfLE h).op).hom.app U) x)
      (fun x : F.obj.obj (op (m, U.unop)) ↦
        F.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
  /-- Morphisms are restricted without modifying their section maps. -/
  setsTower_map : ∀ {F G : Sheaf (coefficientSequenceTopology J) (Type r)}
    (f : F ⟶ G) (n : ℕ) (U : Cᵒᵖ),
    HEq (fun x ↦ (((setsTower.map f).app (op n)).hom.app U) x)
      (fun x : F.obj.obj (op (n, U.unop)) ↦ f.hom.app (op (n, U.unop)) x)
  /-- Direct image is inverse limit in sheaves of sets. -/
  directLimit : π.direct ≅ setsTower ⋙ lim
  /-- The geometric adjunction is the coordinate-wise constant/limit correspondence. -/
  adjunction_section : ∀ (H : Sheaf J (Type r))
    (F : Sheaf (coefficientSequenceTopology J) (Type r)) (a : π.inverse.obj H ⟶ F)
    (n : ℕ) (U : Cᵒᵖ) (x : H.obj.obj U),
    (eqToHom (setsTower_obj F n)).hom.app U
      ((limit.π (setsTower.obj F) (op n)).hom.app U
        ((directLimit.hom.app F).hom.app U (((π.adj.homEquiv H F) a).hom.app U x))) =
      a.hom.app (op (n, U.unop)) ((inverseUnderlying.inv.app H).app (op (n, U.unop)) x)

/-- Exact restriction to the limit ring, with actual transitions.
Source: Stacks 0940, 03D7 and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
structure SequenceModuleRestriction (b : Cone (rings.{c, v, r} J B τ))
    (g : SequenceSetProjection.{c, v, r} J B τ b) where
  /-- Restrict each component along the actual projection rho_n. -/
  restriction : Systems.{c, v, r} J B τ ⥤ (ℕᵒᵖ ⥤ Mod.{c, v, r} J b.pt)
  /-- Its object formula uses the existing evaluation and scalar restriction. -/
  restriction_obj : ∀ (M : Systems.{c, v, r} J B τ) (n : ℕ),
    (restriction.obj M).obj (op n) = (res.{c, v, r} (b.π.app (op n))).obj
      ((evaluation.{c, v, r} J B τ n).obj M)
  /-- The underlying additive transitions are unchanged. -/
  restriction_transition : ∀ (M : Systems.{c, v, r} J B τ)
    (m n : ℕ) (h : n ≤ m) (U : Cᵒᵖ),
    HEq (fun x ↦ (((restriction.obj M).map (homOfLE h).op).val.app U) x)
      (fun x : M.val.obj (op (m, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
  /-- System morphisms keep their original component maps. -/
  restriction_map : ∀ {M N : Systems.{c, v, r} J B τ} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
    HEq (fun x ↦ (((restriction.map f).app (op n)).val.app U) x)
      (fun x : M.val.obj (op (n, U.unop)) ↦ f.val.app (op (n, U.unop)) x)
  /-- Additivity and exactness, without a surjectivity condition on transitions. -/
  restriction_additive : restriction.Additive
  /-- Preservation of finite limits. -/
  restriction_limits : PreservesFiniteLimits restriction
  /-- Preservation of finite colimits. -/
  restriction_colimits : PreservesFiniteColimits restriction
  /-- The induced module direct image is the inverse limit of the restricted system. -/
  moduleDirect : g.π.modules ≅ restriction ⋙ lim
  /-- The module-limit identification is the coordinate map of the underlying set limit. -/
  moduleDirect_section : ∀ (M : Systems.{c, v, r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (x : (g.π.modules.obj M).val.obj U),
    HEq ((limit.π (restriction.obj M) (op n)).val.app U
      ((moduleDirect.hom.app M).val.app U x))
      ((eqToHom (g.setsTower_obj
        ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, r} J B τ)).obj M) n)).hom.app U
        ((limit.π (g.setsTower.obj
          ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
            (systemRing.{c, v, r} J B τ)).obj M)) (op n)).hom.app U
          ((g.directLimit.hom.app
            ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
              (systemRing.{c, v, r} J B τ)).obj M)).hom.app U
            ((g.π.underlying.hom.app M).hom.app U x))))

/-- The normalized simultaneous ordinary pullback.
Source: Stacks 0940, 03D7 and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
structure SequenceOrdinaryPullback (b : Cone (rings.{c, v, r} J B τ))
    (g : SequenceSetProjection.{c, v, r} J B τ b)
    (u : SequenceModuleRestriction.{c, v, r} J B τ b g) where
  /-- Ordinary ringed module pullback. -/
  extension : Mod.{c, v, r} J b.pt ⥤ Systems.{c, v, r} J B τ
  /-- Additivity of ordinary pullback. -/
  [extension_additive : extension.Additive]
  /-- This identifies extension with pi-star, by its defining module adjunction. -/
  moduleAdjunction : extension ⊣ g.π.modules
  /-- The recorded derived scalar-extension model at every actual rho_n. -/
  level : ∀ n : ℕ, ScalarData.{c, v, r} (b.π.app (op n))
  /-- The ordinary pullback evaluates to the sheafified change of rings. -/
  ordinaryEvaluation : ∀ n : ℕ,
    extension ⋙ evaluation.{c, v, r} J B τ n ≅ (level n).model.E
  /-- The comparison uses the ordinary tensor-insertion unit, fixing its normalization. -/
  ordinary_unit : ∀ (M : Mod.{c, v, r} J b.pt) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U),
    HEq ((limit.π (u.restriction.obj (extension.obj M)) (op n)).val.app U
      ((u.moduleDirect.hom.app (extension.obj M)).val.app U
        ((moduleAdjunction.unit.app M).val.app U x)))
      (((ordinaryEvaluation n).inv.app M).val.app U
        (completionScalarSection.{c, v, r} J (b.π.app (op n)) (level n) M U 1 x))
  /-- The one strict pullback system has transition 1 tensor q on pure tensors. -/
  ordinary_transition : ∀ (M : Mod.{c, v, r} J b.pt) (m n : ℕ) (h : n ≤ m)
    (U : Cᵒᵖ) (a : (B m).obj.obj U) (x : M.val.obj U),
    (((ordinaryEvaluation m).inv.app M ≫
      (transition.{c, v, r} J B τ h).app (extension.obj M) ≫
        (res.{c, v, r} (coefficientMap.{c, v, r} J B τ h)).map
          ((ordinaryEvaluation n).hom.app M)).val.app U)
            (completionScalarSection.{c, v, r} J (b.π.app (op m)) (level m) M U a x) =
      completionScalarSection.{c, v, r} J (b.π.app (op n)) (level n) M U
        ((coefficientMap.{c, v, r} J B τ h).hom.app U a) x

attribute [instance] SequenceOrdinaryPullback.extension_additive

/-- The normalized simultaneous unbounded derived pullback.
Source: Stacks 0940, 03D7 and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
structure SequenceDerivedPullback (b : Cone (rings.{c, v, r} J B τ))
    (g : SequenceSetProjection.{c, v, r} J B τ b)
    (u : SequenceModuleRestriction.{c, v, r} J B τ b g)
    (p : SequenceOrdinaryPullback.{c, v, r} J B τ b g u) where
  /-- The single unbounded derived pullback, before evaluating at any level. -/
  derived : D.{c, v, r} J b.pt ⥤ DS.{c, v, r} J B τ
  /-- The natural left-derived comparison on all complexes. -/
  ε : completionLocalization.{c, v, r} J b.pt ⋙ derived ⟶
    p.extension.mapHomologicalComplex (.up ℤ) ⋙
      completionLocalization.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, r} J B τ)
  /-- The universal left-derived property of pi-star. -/
  universal : derived.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ))
  /-- Triangulated exactness on ordinary unbounded derived categories. -/
  triangulated : ∃ (_ : derived.CommShift ℤ), derived.IsTriangulated
  /-- The comparison is invertible on each flat-term K-flat complex, simultaneously. -/
  computes : ∀ (P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, r} (J := J) (R := b.pt) P →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, r, r} (J := J) (R := b.pt) (P.X i)) →
      IsIso (ε.app P)
  /-- Invariance of the entire strict complex under a quasi-isomorphism of resolutions. -/
  preserves : ∀ {P Q : CochainComplex (Mod.{c, v, r} J b.pt) ℤ} (f : P ⟶ Q),
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, r} (J := J) (R := b.pt) P →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, r, r} (J := J) (R := b.pt) (P.X i)) →
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, r} (J := J) (R := b.pt) Q →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, r, r} (J := J) (R := b.pt) (Q.X i)) →
    QuasiIso f → QuasiIso ((p.extension.mapHomologicalComplex (.up ℤ)).map f)
  /-- Evaluation comparison on all derived morphisms, not just object values. -/
  derivedEvaluation : ∀ n : ℕ, derived ⋙ e.{c, v, r} J B τ n ≅ (p.level n).T
  /-- Termwise form of the ordinary evaluation comparison. -/
  complexEvaluation : ∀ n : ℕ,
    p.extension.mapHomologicalComplex (.up ℤ) ⋙
      (evaluation.{c, v, r} J B τ n).mapHomologicalComplex (.up ℤ) ≅
        (p.level n).model.E.mapHomologicalComplex (.up ℤ)
  /-- The complex comparison has exactly the ordinary comparison in every degree. -/
  complexEvaluation_f : ∀ (n : ℕ) (P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ) (i : ℤ),
    ((complexEvaluation n).hom.app P).f i = (p.ordinaryEvaluation n).hom.app (P.X i)
  /-- The derived comparison is the localization of the specified simultaneous model. -/
  representative_square : ∀ (n : ℕ) (P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, r} (J := J) (R := b.pt) P)
    (_flatP : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, r, r} (J := J) (R := b.pt) (P.X i)),
    (derivedEvaluation n).hom.app ((completionLocalization.{c, v, r} J b.pt).obj P) ≫
        (p.level n).model.ε.app P =
      (e.{c, v, r} J B τ n).map (ε.app P) ≫
        (Functor.mapDerivedCategoryFactors (evaluation.{c, v, r} J B τ n)).hom.app
          ((p.extension.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (completionLocalization.{c, v, r} J (B n)).map ((complexEvaluation n).hom.app P)

/-- The constant/limit projection with its ordinary and derived module models.
Source: Stacks 0940, 03D7 and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
structure SequenceCompletionProjection (b : Cone (rings.{c, v, r} J B τ)) where
  /-- Constant/limit geometric morphism and the projection ring map. -/
  geometric : SequenceSetProjection.{c, v, r} J B τ b
  /-- The exact functor retaining all additive transitions. -/
  restriction : SequenceModuleRestriction.{c, v, r} J B τ b geometric
  /-- One ordinary strict extension system, normalized on sheafified tensors. -/
  ordinary : SequenceOrdinaryPullback.{c, v, r} J B τ b geometric restriction
  /-- One derived functor, normalized before evaluation at any level. -/
  derived : SequenceDerivedPullback.{c, v, r} J B τ b geometric restriction ordinary

attribute [local instance 30000] CategoryTheory.ringedToposRingForgetCompose
  CategoryTheory.ringedToposAbelianForgetCompose CategoryTheory.ringedToposCommRingForgetCompose

private instance seqSetHasLimit (F : ℕᵒᵖ ⥤ Sheaf J (Type r)) : HasLimit F :=
  inferInstance

private instance seqModHasLimit (R : Sheaf J CommRingCat.{r})
    (F : ℕᵒᵖ ⥤ Mod.{c, v, r} J R) : HasLimit F := inferInstance

attribute [local instance 30000] seqSetHasLimit seqModHasLimit

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem seqSheafOfSlices {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ Type r)
    (hP : ∀ n : ℕ, Presieve.IsSheaf J ((Prod.sectR n C).op ⋙ P)) :
    Presieve.IsSheaf (coefficientSequenceTopology J) P := by
  intro X S hS x hx
  let xv : Presieve.FamilyOfElements ((Prod.sectR X.1 C).op ⋙ P)
      (S.functorPullback (Prod.sectR X.1 C)).arrows :=
    fun Y f hf ↦ x ((Prod.sectR X.1 C).map f) hf
  have hxv : xv.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ he
    exact hx ((Prod.sectR X.1 C).map g₁) ((Prod.sectR X.1 C).map g₂)
      hf₁ hf₂ (by simpa only [← Functor.map_comp] using
        (congrArg (fun f ↦ (Prod.sectR X.1 C).map f) he))
  obtain ⟨a, ha, hua⟩ := hP X.1 _ hS xv hxv
  refine ⟨a, ?_, ?_⟩
  · intro Y f hf
    apply ((hP Y.1).isSeparated _ (J.pullback_stable f.2 hS)).ext
    intro Z g hg
    let v : (X.1, Z) ⟶ X := (Prod.sectR X.1 C).map (g ≫ f.2)
    let k : (Y.1, Z) ⟶ (X.1, Z) := Prod.mkHom f.1 (𝟙 Z)
    have hv : S v := hg
    have he : k ≫ v = (Prod.sectR Y.1 C).map g ≫ f := by
      ext <;> simp [k, v]
    have hc := hx k ((Prod.sectR Y.1 C).map g) hv hf he
    have hag := congrArg (P.map k.op) (ha (g ≫ f.2) hv)
    change P.map ((Prod.sectR Y.1 C).map g).op (P.map f.op a) = _
    erw [← P.map_comp_apply, ← op_comp, ← he]
    have hp : P.map (k ≫ v).op a = P.map k.op (P.map v.op a) := by
      rw [op_comp, P.map_comp]
      rfl
    exact hp.trans (hag.trans hc)
  · intro b hb
    apply hua b
    intro Y f hf
    exact hb ((Prod.sectR X.1 C).map f) hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def seqSetsTower : Sheaf (coefficientSequenceTopology J) (Type r) ⥤
    (ℕᵒᵖ ⥤ Sheaf J (Type r)) where
  obj F :=
    { obj n := ⟨(Prod.sectR n.unop C).op ⋙ F.obj,
        (((Prod.sectR n.unop C).sheafPushforwardContinuous (Type r)
          J (coefficientSequenceTopology J)).obj F).property⟩
      map {m n} h :=
        ⟨{ app := fun U ↦ F.obj.map (Prod.mkHom h.unop (𝟙 U.unop)).op
           naturality := by
             intro U V f
             change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
             rw [← F.obj.map_comp, ← F.obj.map_comp]
             congr 1
             apply Quiver.Hom.unop_inj
             ext <;> simp }⟩
      map_id n := by
        ext U x
        change F.obj.map (𝟙 _) x = x
        simp
      map_comp h k := by
        ext U x
        change F.obj.map _ x = F.obj.map _ (F.obj.map _ x)
        rw [← Functor.map_comp_apply]
        congr 3
        apply Quiver.Hom.unop_inj
        ext <;> simp }
  map f :=
    { app := fun n ↦ ⟨Functor.whiskerLeft (Prod.sectR n.unop C).op f.hom⟩
      naturality := by
        intro m n h
        ext U x
        exact CategoryTheory.congr_fun
          (f.hom.naturality (Prod.mkHom h.unop (𝟙 U.unop)).op) x }

private def seqConstant : Sheaf J (Type r) ⥤
    Sheaf (coefficientSequenceTopology J) (Type r) where
  obj H :=
    ⟨(CategoryTheory.Prod.snd ℕ C).op ⋙ H.obj, by
      rw [isSheaf_iff_isSheaf_of_type]
      apply seqSheafOfSlices
      intro n
      exact (isSheaf_iff_isSheaf_of_type J H.obj).mp H.property⟩
  map f := ⟨Functor.whiskerLeft (CategoryTheory.Prod.snd ℕ C).op f.hom⟩

private abbrev seqCone (H : Sheaf J (Type r))
    (F : Sheaf (coefficientSequenceTopology J) (Type r))
    (a : (seqConstant J).obj H ⟶ F) : Cone ((seqSetsTower J).obj F) where
  pt := H
  π :=
    { app := fun n ↦
        ⟨{ app := fun U ↦ a.hom.app (op (n.unop, U.unop))
           naturality := by
             intro U V f
             exact a.hom.naturality (Prod.mkHom (𝟙 n.unop) f.unop).op }⟩
      naturality := by
        intro m n h
        ext U x
        have ha := CategoryTheory.congr_fun
          (a.hom.naturality (Prod.mkHom h.unop (𝟙 U.unop)).op) x
        change a.hom.app (op (n.unop, U.unop)) (H.obj.map (𝟙 U) x) = _ at ha
        rw [H.obj.map_id] at ha
        exact ha }

private def seqUntranspose (H : Sheaf J (Type r))
    (F : Sheaf (coefficientSequenceTopology J) (Type r))
    (a : H ⟶ limit ((seqSetsTower J).obj F)) : (seqConstant J).obj H ⟶ F :=
  ⟨{ app := fun X ↦ (a ≫ limit.π ((seqSetsTower J).obj F) (op X.unop.1)).hom.app
        (op X.unop.2)
     naturality := by
       intro X Y f
       ext x
       let v : op (X.unop.1, Y.unop.2) ⟶ Y :=
         (Prod.mkHom f.unop.1 (𝟙 Y.unop.2)).op
       let w : X ⟶ op (X.unop.1, Y.unop.2) :=
         (Prod.mkHom (𝟙 X.unop.1) f.unop.2).op
       have hw := CategoryTheory.congr_fun ((a ≫ limit.π ((seqSetsTower J).obj F)
         (op X.unop.1)).hom.naturality f.unop.2.op) x
       have hv := congrArg (fun g ↦ g.hom.app (op Y.unop.2)
         (a.hom.app (op Y.unop.2) (H.obj.map f.unop.2.op x)))
         (limit.w ((seqSetsTower J).obj F) f.unop.1.op)
       have he : w ≫ v = f := by
         apply Quiver.Hom.unop_inj
         ext <;> simp [w, v]
       change (a ≫ limit.π ((seqSetsTower J).obj F) (op Y.unop.1)).hom.app
           (op Y.unop.2) (H.obj.map f.unop.2.op x) = F.obj.map f _
       conv_rhs => rw [← he, F.obj.map_comp]
       change (limit.π ((seqSetsTower J).obj F) (op Y.unop.1)).hom.app (op Y.unop.2)
           (a.hom.app (op Y.unop.2) (H.obj.map f.unop.2.op x)) =
         F.obj.map v (F.obj.map w
           ((a ≫ limit.π ((seqSetsTower J).obj F) (op X.unop.1)).hom.app
             (op X.unop.2) x))
       exact hv.symm.trans (congrArg (F.obj.map v) hw) }⟩

private def seqHomEquiv (H : Sheaf J (Type r))
    (F : Sheaf (coefficientSequenceTopology J) (Type r)) :
    ((seqConstant J).obj H ⟶ F) ≃ (H ⟶ limit ((seqSetsTower J).obj F)) where
  toFun a := limit.lift _ (seqCone J H F a)
  invFun := seqUntranspose J H F
  left_inv a := by
    ext X x
    exact congrFun (congrArg (fun f ↦ f.hom.app (op X.unop.2))
      (limit.lift_π (seqCone J H F a) (op X.unop.1))) x
  right_inv a := by
    apply limit.hom_ext
    intro n
    rw [limit.lift_π]
    rfl

private def seqAdjunction : seqConstant.{c, v, r} J ⊣ seqSetsTower J ⋙ lim :=
  Adjunction.mkOfHomEquiv
    { homEquiv := seqHomEquiv J
      homEquiv_naturality_left_symm := by
        intros
        ext X x
        rfl
      homEquiv_naturality_right := by
        intro H F G a f
        apply limit.hom_ext
        intro n
        change limit.lift _ (seqCone J H G (a ≫ f)) ≫ _ =
          limit.lift _ (seqCone J H F a) ≫ lim.map ((seqSetsTower J).map f) ≫ _
        dsimp only [seqCone, lim_map]
        rw [limMap_π, limit.lift_π_assoc, limit.lift_π]
        rfl }

omit [EssentiallySmall.{r} C] in
private theorem seqAdjunction_homEquiv (H : Sheaf J (Type r))
    (F : Sheaf (coefficientSequenceTopology J) (Type r)) :
    (seqAdjunction J).homEquiv H F = seqHomEquiv J H F := by
  simp only [seqAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

attribute [irreducible] seqAdjunction

private instance seqConstant_limits :
    PreservesFiniteLimits (seqConstant.{c, v, r} J) := by
  let T := sheafToPresheaf (coefficientSequenceTopology J) (Type r)
  have : PreservesFiniteLimits (seqConstant J ⋙ T) := by
    change PreservesFiniteLimits (sheafToPresheaf J (Type r) ⋙
      (Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.snd ℕ C).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

private theorem seqEval_ringMap (n : ℕ) :
    eqToHom (evaluation_ring.{c, v, r} J B τ n).symm =
      SheafOfModules.systemSequenceVerticalRingMap (rings J B τ) n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private theorem seqEval_eq (n : ℕ) :
    evaluation J B τ n = SheafOfModules.systemSequenceEvaluation (rings J B τ) n :=
  congrArg (fun φ ↦ SheafOfModules.pushforward (F := Prod.sectR n C) φ)
    (seqEval_ringMap J B τ n)

private def seqEvaluationIso (n : ℕ) :
    evaluation J B τ n ≅ SheafOfModules.systemSequenceEvaluation (rings J B τ) n :=
  SheafOfModules.pushforwardCongr (seqEval_ringMap J B τ n)

private def seqRestriction (b : Cone (rings.{c, v, r} J B τ)) :
    Systems.{c, v, r} J B τ ⥤ (ℕᵒᵖ ⥤ Mod.{c, v, r} J b.pt) :=
  (SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).inverse ⋙
    SheafOfModules.SequenceProjection.restrictedDiagrams b.pt (rings J B τ) b.π

private theorem seqRestrictionObjEq (b : Cone (rings.{c, v, r} J B τ))
    (M : Systems.{c, v, r} J B τ) (n : ℕ) :
    ((seqRestriction J B τ b).obj M).obj (op n) =
      (res (b.π.app (op n))).obj ((evaluation J B τ n).obj M) := by
  rw [seqEval_eq]
  rfl

private def seqRestrictionEval (b : Cone (rings.{c, v, r} J B τ)) (n : ℕᵒᵖ) :
    seqRestriction J B τ b ⋙ (CategoryTheory.evaluation _ _).obj n ≅
      evaluation J B τ n.unop ⋙ res (b.π.app n) := by
  rw [seqEval_eq]
  exact NatIso.ofComponents (fun M ↦ Iso.refl _) (by intros; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private instance seqRestriction_limits (b : Cone (rings.{c, v, r} J B τ)) :
    PreservesFiniteLimits (seqRestriction J B τ b) where
  preservesFiniteLimits := by
    intro K _ _
    apply preservesLimitsOfShape_of_evaluation
    intro n
    exact preservesLimitsOfShape_of_natIso (seqRestrictionEval J B τ b n).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private instance seqRestriction_colimits (b : Cone (rings.{c, v, r} J B τ)) :
    PreservesFiniteColimits (seqRestriction J B τ b) where
  preservesFiniteColimits := by
    intro K _ _
    apply preservesColimitsOfShape_of_evaluation
    intro n
    exact preservesColimitsOfShape_of_natIso (seqRestrictionEval J B τ b n).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private instance seqRestriction_additive (b : Cone (rings.{c, v, r} J B τ)) :
    (seqRestriction J B τ b).Additive where
  map_add := by
    intro M N f g
    ext n U x
    change ((res (b.π.app n)).map
      ((SheafOfModules.systemSequenceEvaluation (rings J B τ) n.unop).map (f + g))).val.app U x = _
    have h := (evaluation J B τ n.unop).map_add (f := f) (g := g)
    rw [seqEval_eq] at h
    rw [h, Functor.map_add]
    rfl

private instance seqDirect_additive (b : Cone (rings.{c, v, r} J B τ)) :
    (seqRestriction J B τ b ⋙ lim).Additive where
  map_add := by
    intro M N f g
    apply limit.hom_ext
    intro n
    change lim.map ((seqRestriction J B τ b).map (f + g)) ≫ _ = _
    simp only [lim_map, limMap_π, (seqRestriction J B τ b).map_add,
      Preadditive.add_comp, Preadditive.comp_add, NatTrans.app_add, Functor.comp_map]

private instance underlyingTowerLimits (R : Sheaf J CommRingCat.{r}) :
    PreservesLimitsOfShape ℕᵒᵖ (completionUnderlying J R) := by
  let T := sheafToPresheaf J (Type r)
  have : PreservesLimitsOfShape ℕᵒᵖ (completionUnderlying J R ⋙ T) := by
    change PreservesLimitsOfShape ℕᵒᵖ
      (SheafOfModules.forget (ring J R) ⋙ PresheafOfModules.toPresheaf (ring J R).obj ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{r}))
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ T

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def seqUnderlyingTower (b : Cone (rings.{c, v, r} J B τ)) :
    seqRestriction J B τ b ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (completionUnderlying J b.pt) ≅
      completionUnderlying (coefficientSequenceTopology J) (systemRing J B τ) ⋙
        seqSetsTower J :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun n ↦ Iso.refl _)
    (by intros; ext U x; rfl)) (by intros; ext n U x; rfl)

private def seqUnderlyingDirect (b : Cone (rings.{c, v, r} J B τ)) :
    (seqRestriction J B τ b ⋙ lim) ⋙ completionUnderlying J b.pt ≅
      completionUnderlying (coefficientSequenceTopology J) (systemRing J B τ) ⋙
        (seqSetsTower J ⋙ lim) :=
  Functor.isoWhiskerLeft (seqRestriction J B τ b)
    (preservesLimitNatIso (completionUnderlying J b.pt)) ≪≫
      Functor.isoWhiskerRight (seqUnderlyingTower J B τ b) lim

private theorem completionUnderlying_map_apply {R : Sheaf J CommRingCat.{r}}
    {M N : Mod.{c, v, r} J R} (f : M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (((completionUnderlying J R).map f).hom.app U) x = (f.val.app U) x := rfl

private theorem seqUnderlyingDirect_projection (b : Cone (rings.{c, v, r} J B τ))
    (M : Systems.{c, v, r} J B τ) (n : ℕ) :
    (seqUnderlyingDirect J B τ b).hom.app M ≫
      limit.π ((seqSetsTower J).obj
        ((completionUnderlying (coefficientSequenceTopology J) (systemRing J B τ)).obj M))
          (op n) =
      (completionUnderlying J b.pt).map
        (limit.π ((seqRestriction J B τ b).obj M) (op n)) ≫
          ((seqUnderlyingTower J B τ b).hom.app M).app (op n) := by
  let F := (seqRestriction J B τ b).obj M
  let α := (seqUnderlyingTower J B τ b).hom.app M
  have hα := limMap_π α (op n)
  have hp := preservesLimitIso_hom_π (completionUnderlying J b.pt) F (op n)
  have h := congrArg
    (fun f ↦ (preservesLimitIso (completionUnderlying J b.pt) F).hom ≫ f) hα
  calc
    _ = (preservesLimitIso (completionUnderlying J b.pt) F).hom ≫
        (limMap α ≫ limit.π _ (op n)) := by
      exact Category.assoc _ _ _
    _ = (preservesLimitIso (completionUnderlying J b.pt) F).hom ≫
        (limit.π _ (op n) ≫ α.app (op n)) := h
    _ = ((preservesLimitIso (completionUnderlying J b.pt) F).hom ≫
        limit.π _ (op n)) ≫ α.app (op n) := (Category.assoc _ _ _).symm
    _ = (completionUnderlying J b.pt).map (limit.π F (op n)) ≫ α.app (op n) :=
      congrArg (fun f ↦ f ≫ α.app (op n)) hp
private theorem seqUnderlyingTower_component (b : Cone (rings.{c, v, r} J B τ))
    (M : Systems.{c, v, r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (x : (((seqRestriction J B τ b).obj M).obj (op n)).val.obj U) :
    ((((seqUnderlyingTower J B τ b).hom.app M).app (op n)).hom.app U) x = x := rfl

attribute [irreducible] seqUnderlyingTower seqUnderlyingDirect

private def seqRingMap (b : Cone (rings.{c, v, r} J B τ)) :
    (seqConstant J).obj
        ((sheafCompose J (forget RingCat.{r})).obj (ring J b.pt)) ⟶
      (sheafCompose (coefficientSequenceTopology J) (forget RingCat.{r})).obj
        (ring (coefficientSequenceTopology J) (systemRing J B τ)) :=
  ⟨{ app := fun X ↦ ↾fun a ↦
        (b.π.app (op X.unop.1)).hom.app (op X.unop.2) a
     naturality := by
       intro X Y f
       ext a
       have hv := CategoryTheory.congr_fun
         ((b.π.app (op Y.unop.1)).hom.naturality f.unop.2.op) a
       have hh := congrArg (fun g ↦ g.hom.app (op X.unop.2) a) (b.w f.unop.1.op)
       change (b.π.app (op Y.unop.1)).hom.app (op Y.unop.2)
           (b.pt.obj.map f.unop.2.op a) =
         (B Y.unop.1).obj.map f.unop.2.op
           (((rings J B τ).map f.unop.1.op).hom.app (op X.unop.2)
             ((b.π.app (op X.unop.1)).hom.app (op X.unop.2) a))
       change (((rings J B τ).map f.unop.1.op).hom.app (op X.unop.2))
           ((b.π.app (op X.unop.1)).hom.app (op X.unop.2) a) =
         (b.π.app (op Y.unop.1)).hom.app (op X.unop.2) a at hh
       change (b.π.app (op Y.unop.1)).hom.app (op Y.unop.2)
           (b.pt.obj.map f.unop.2.op a) =
         (B Y.unop.1).obj.map f.unop.2.op
           ((b.π.app (op Y.unop.1)).hom.app (op X.unop.2) a) at hv
       exact hv.trans (congrArg ((B Y.unop.1).obj.map f.unop.2.op) hh.symm) }⟩

omit [EssentiallySmall.{r} C] in
private theorem seqAdjunction_component (H : Sheaf J (Type r))
    (F : Sheaf (coefficientSequenceTopology J) (Type r))
    (a : (seqConstant J).obj H ⟶ F) (n : ℕ) (U : Cᵒᵖ) (x : H.obj.obj U) :
    (limit.π ((seqSetsTower J).obj F) (op n)).hom.app U
      (((seqAdjunction J).homEquiv H F a).hom.app U x) =
        a.hom.app (op (n, U.unop)) x := by
  rw [seqAdjunction_homEquiv]
  change ((limit.lift _ (seqCone J H F a)) ≫ _).hom.app U x = _
  rw [limit.lift_π]
  rfl

private theorem seqAdjunction_inverse_component (H : Sheaf J (Type r))
    (M : Systems.{c, v, r} J B τ)
    (b : Cone (rings.{c, v, r} J B τ))
    (a : H ⟶ (completionUnderlying J b.pt).obj ((seqRestriction J B τ b ⋙ lim).obj M))
    (n : ℕ) (U : Cᵒᵖ) (x : H.obj.obj U) :
    (((seqAdjunction J).homEquiv H _).symm
        (a ≫ (seqUnderlyingDirect J B τ b).hom.app M)).hom.app (op (n, U.unop)) x =
      (limit.π ((seqRestriction J B τ b).obj M) (op n)).val.app U (a.hom.app U x) := by
  rw [seqAdjunction_homEquiv]
  change ((a ≫ (seqUnderlyingDirect J B τ b).hom.app M) ≫
    limit.π _ (op n)).hom.app U x = _
  have h := congrArg (fun f ↦ (a ≫ f).hom.app U x)
    (seqUnderlyingDirect_projection J B τ b M n)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply] at h
  exact h.trans ((seqUnderlyingTower_component J B τ b M n U _).trans
    (completionUnderlying_map_apply J _ U _))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def seqGeometric (b : Cone (rings.{c, v, r} J B τ)) :
    RingedToposMorphismOfUniverses
      (ring (coefficientSequenceTopology J) (systemRing J B τ)) (ring J b.pt) where
  inverse := seqConstant J
  direct := seqSetsTower J ⋙ lim
  adj := seqAdjunction J
  leftExact := inferInstance
  ringMap := seqRingMap J B τ b
  ring_zero := by
    intro T z hz U t
    change T.obj.obj (op U.unop.2) at t
    change (b.π.app (op U.unop.1)).hom.app (op U.unop.2)
      (z.hom.app (op U.unop.2) t) = 0
    rw [hz]
    exact map_zero _
  ring_one := by
    intro T z hz U t
    change T.obj.obj (op U.unop.2) at t
    change (b.π.app (op U.unop.1)).hom.app (op U.unop.2)
      (z.hom.app (op U.unop.2) t) = 1
    rw [hz]
    exact map_one _
  ring_add := by
    intro T x y z hz U t
    change T.obj.obj (op U.unop.2) at t
    change (b.π.app (op U.unop.1)).hom.app (op U.unop.2)
      (z.hom.app (op U.unop.2) t) = _
    rw [hz]
    exact map_add _ _ _
  ring_mul := by
    intro T x y z hz U t
    change T.obj.obj (op U.unop.2) at t
    change (b.π.app (op U.unop.1)).hom.app (op U.unop.2)
      (z.hom.app (op U.unop.2) t) = _
    rw [hz]
    exact map_mul _ _ _
  modules := seqRestriction J B τ b ⋙ lim
  additive := inferInstance
  underlying := seqUnderlyingDirect J B τ b
  module_linear := by
    intro M T a x y z hz U t
    obtain ⟨⟨n, U⟩⟩ := U
    change T.obj.obj (op U) at t
    change _ = (b.π.app (op n)).hom.app (op U) (a.hom.app (op U) t) •
      (_ : M.val.obj (op (n, U))) + (_ : M.val.obj (op (n, U)))
    let p := (limit.π ((seqRestriction J B τ b).obj M) (op n)).val.app (op U)
    let av : (ring J b.pt).obj.obj (op U) := a.hom.app (op U) t
    let xv : ((seqRestriction J B τ b ⋙ lim).obj M).val.obj (op U) :=
      x.hom.app (op U) t
    let yv : ((seqRestriction J B τ b ⋙ lim).obj M).val.obj (op U) :=
      y.hom.app (op U) t
    have hz0 := seqAdjunction_inverse_component J B τ T M b z n (op U) t
    have hx0 := seqAdjunction_inverse_component J B τ T M b x n (op U) t
    have hy0 := seqAdjunction_inverse_component J B τ T M b y n (op U) t
    have hlin := (p.hom.map_add (av • xv) yv).trans
      (congrArg (fun z ↦ z + p.hom yv) (p.hom.map_smul av xv))
    exact hz0.trans ((congrArg p.hom (hz (op U) t)).trans
      (hlin.trans (congrArg₂
        (fun (x y : M.val.obj (op (n, U))) ↦
          (b.π.app (op n)).hom.app (op U) av • x + y) hx0.symm hy0.symm)))

private def seqSetProjection (b : Cone (rings.{c, v, r} J B τ)) :
    SequenceSetProjection J B τ b where
  π := seqGeometric J B τ b
  inverseUnderlying := Iso.refl _
  ring_section := by intros; rfl
  setsTower := seqSetsTower J
  setsTower_obj := by intros; rfl
  setsTower_transition := by intros; exact HEq.rfl
  setsTower_map := by intros; exact HEq.rfl
  directLimit := Iso.refl _
  adjunction_section := by
    intro H F a n U x
    exact seqAdjunction_component J H F a n U x

private theorem seqModuleSection (b : Cone (rings.{c, v, r} J B τ))
    (M : Systems.{c, v, r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (x : ((seqRestriction J B τ b ⋙ lim).obj M).val.obj U) :
    HEq ((limit.π ((seqRestriction J B τ b).obj M) (op n)).val.app U x)
    ((limit.π ((seqSetsTower J).obj
      ((completionUnderlying (coefficientSequenceTopology J) (systemRing J B τ)).obj M))
        (op n)).hom.app U (((seqUnderlyingDirect J B τ b).hom.app M).hom.app U x)) := by
  have h := congrArg (fun f ↦ f.hom.app U x)
    (seqUnderlyingDirect_projection J B τ b M n)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  have h' := h.trans ((seqUnderlyingTower_component J B τ b M n U _).trans
    (completionUnderlying_map_apply J _ U _))
  exact heq_of_eq h'.symm

private def seqModuleRestriction (b : Cone (rings.{c, v, r} J B τ)) :
    SequenceModuleRestriction J B τ b (seqSetProjection J B τ b) where
  restriction := seqRestriction J B τ b
  restriction_obj := seqRestrictionObjEq J B τ b
  restriction_transition := by intros; exact HEq.rfl
  restriction_map := by intros; exact HEq.rfl
  restriction_additive := inferInstance
  restriction_limits := inferInstance
  restriction_colimits := inferInstance
  moduleDirect := Iso.refl _
  moduleDirect_section := seqModuleSection J B τ b

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev seqScalar (b : Cone (rings.{c, v, r} J B τ)) (n : ℕ) :=
  SheafOfModules.SequenceProjection.scalar.{c, v, r} b.pt (rings J B τ) b.π n

private def seqScalarData (b : Cone (rings.{c, v, r} J B τ)) (n : ℕ) :
    ScalarData.{c, v, r} (b.π.app (op n)) where
  model := (seqScalar J B τ b n).model
  ordinaryAdjunction := (seqScalar J B τ b n).ordinaryAdj
  unit_section := by
    intro M U x
    rw [(seqScalar J B τ b n).unit_normalized]
    dsimp only [SheafOfModules.systemModelTmul]
    rw [one_smul]
    change (eqToHom (C := Mod J (B n)) _).val.app U
      ((eqToHom (C := Mod J (B n)) _).val.app U _) = _
    rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
      ← SheafOfModules.comp_val, eqToHom_trans]
    rfl
  adjunction := (seqScalar J B τ b n).adjunction
  transpose_model := by
    intro P Q hP f
    rw [(seqScalar J B τ b n).transpose]
    simp

private def seqExtension (b : Cone (rings.{c, v, r} J B τ)) :
    Mod.{c, v, r} J b.pt ⥤ Systems.{c, v, r} J B τ :=
  SheafOfModules.SequenceProjection.extension.{c, v, r} b.pt (rings J B τ) b.π ⋙
    SheafOfModules.strictSystemToSequenceFunctor (rings J B τ)

private instance seqExtension_additive (b : Cone (rings.{c, v, r} J B τ)) :
    (seqExtension J B τ b).Additive := by
  let F := SheafOfModules.SequenceProjection.extension.{c, v, r} b.pt (rings J B τ) b.π
  let G := SheafOfModules.strictSystemToSequenceFunctor (rings J B τ)
  have : G.Additive := ⟨by
    intro M N f g
    ext U x
    exact congrArg (fun f ↦ f.val.app (op U.unop.2) x)
      ((SheafOfModules.systemEvaluation (rings J B τ) U.unop.1).map_add (f := f) (g := g))⟩
  exact inferInstanceAs (F ⋙ G).Additive

private def seqOrdinaryEvaluation (b : Cone (rings.{c, v, r} J B τ)) (n : ℕ) :
    seqExtension J B τ b ⋙ evaluation J B τ n ≅ (seqScalarData J B τ b n).model.E :=
  Functor.isoWhiskerLeft (seqExtension J B τ b) (seqEvaluationIso J B τ n) ≪≫
    NatIso.ofComponents (fun M ↦ (SheafOfModules.strictSystemSequenceUnitLevel
      (rings J B τ) ((SheafOfModules.SequenceProjection.extension.{c, v, r}
        b.pt (rings J B τ) b.π).obj M) n).symm) (by intros; ext U x; rfl)

private theorem seqOrdinaryEvaluation_hom (b : Cone (rings.{c, v, r} J B τ))
    (n : ℕ) (M : Mod.{c, v, r} J b.pt) (U : Cᵒᵖ)
    (x : (((seqExtension J B τ b ⋙ evaluation J B τ n).obj M).val.obj U)) :
    (((seqOrdinaryEvaluation J B τ b n).hom.app M).val.app U) x = x := by
  simp only [seqOrdinaryEvaluation, Iso.trans_hom, NatTrans.comp_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rfl

private theorem seqOrdinaryEvaluation_inv (b : Cone (rings.{c, v, r} J B τ))
    (n : ℕ) (M : Mod.{c, v, r} J b.pt) (U : Cᵒᵖ)
    (x : ((seqScalarData J B τ b n).model.E.obj M).val.obj U) :
    (((seqOrdinaryEvaluation J B τ b n).inv.app M).val.app U) x = x := by
  simp only [seqOrdinaryEvaluation, Iso.trans_inv, NatTrans.comp_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  rfl

attribute [irreducible] seqOrdinaryEvaluation

private def seqModuleAdjunction (b : Cone (rings.{c, v, r} J B τ)) :
    seqExtension J B τ b ⊣ seqRestriction J B τ b ⋙ lim :=
  (SheafOfModules.SequenceProjection.ordinaryAdjunction.{c, v, r} b.pt (rings J B τ) b.π).comp
    (SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).toAdjunction

private theorem seqStrictUnitProjection (b : Cone (rings.{c, v, r} J B τ))
    (M : Mod.{c, v, r} J b.pt) (n : ℕ) :
    (SheafOfModules.SequenceProjection.ordinaryAdjunction.{c, v, r}
      b.pt (rings J B τ) b.π).unit.app M ≫
      SheafOfModules.SequenceProjection.projection.{c, v, r} b.pt (rings J B τ) b.π
        ((SheafOfModules.SequenceProjection.extension.{c, v, r} b.pt (rings J B τ) b.π).obj M) n =
      (seqScalar J B τ b n).ordinaryAdj.unit.app M := by
  have ht := SheafOfModules.SequenceProjection.transpose_projection.{c, v, r}
    b.pt (rings J B τ) b.π
    (𝟙 ((SheafOfModules.SequenceProjection.extension.{c, v, r}
      b.pt (rings J B τ) b.π).obj M)) n
  have hu : (SheafOfModules.SequenceProjection.ordinaryAdjunction.{c, v, r}
      b.pt (rings J B τ) b.π).unit.app M =
      SheafOfModules.SequenceProjection.transpose.{c, v, r}
        b.pt (rings J B τ) b.π (𝟙 _) := by
    rw [← Adjunction.homEquiv_id]
    unfold SheafOfModules.SequenceProjection.ordinaryAdjunction
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  rw [hu]
  exact ht.trans (Adjunction.homEquiv_id _ _)

private theorem seqUnitMorphism (b : Cone (rings.{c, v, r} J B τ))
    (M : Mod.{c, v, r} J b.pt) (n : ℕ) :
    (seqModuleAdjunction J B τ b).unit.app M ≫
      limit.π ((seqRestriction J B τ b).obj ((seqExtension J B τ b).obj M)) (op n) =
    (seqScalar J B τ b n).ordinaryAdj.unit.app M ≫
      (SheafOfModules.SequenceProjection.restriction.{c, v, r}
        b.pt (rings J B τ) b.π n).map
        (((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).unitIso.hom.app
          ((SheafOfModules.SequenceProjection.extension.{c, v, r}
            b.pt (rings J B τ) b.π).obj M)).app n) := by
  rw [seqModuleAdjunction, Adjunction.comp_unit_app]
  change (_ ≫ _ ) ≫ SheafOfModules.SequenceProjection.projection.{c, v, r}
    b.pt (rings J B τ) b.π _ n = _
  rw [Category.assoc,
    SheafOfModules.SequenceProjection.projection_natural.{c, v, r},
    ← Category.assoc, seqStrictUnitProjection]
  rfl

private theorem seqUnitProjection (b : Cone (rings.{c, v, r} J B τ))
    (M : Mod.{c, v, r} J b.pt) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U) :
    HEq ((limit.π ((seqRestriction J B τ b).obj ((seqExtension J B τ b).obj M))
      (op n)).val.app U (((seqModuleAdjunction J B τ b).unit.app M).val.app U x))
      (((seqOrdinaryEvaluation J B τ b n).inv.app M).val.app U
        (completionScalarSection J (b.π.app (op n)) (seqScalarData J B τ b n) M U 1 x)) := by
  have h := congrArg (fun f ↦ f.val.app U x) (seqUnitMorphism J B τ b M n)
  apply HEq.trans (heq_of_eq h)
  apply heq_of_eq
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [seqOrdinaryEvaluation_inv]
  change ((seqScalar J B τ b n).ordinaryAdj.unit.app M).val.app U x = _
  erw [(seqScalar J B τ b n).unit_normalized]
  rfl

attribute [irreducible] seqModuleAdjunction

private theorem seqTransition_apply (M : Systems.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ)
    (x : ((evaluation J B τ m).obj M).val.obj U) :
    ((transition J B τ h).app M).val.app U x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x := by
  have he := (transition_exists J B τ h).exists.choose_spec M U
  exact congrFun (eq_of_heq he) x

private theorem seqTransitionMorphism (b : Cone (rings.{c, v, r} J B τ))
    (M : Mod.{c, v, r} J b.pt) (m n : ℕ) (h : n ≤ m) :
    (seqOrdinaryEvaluation J B τ b m).inv.app M ≫
      (transition J B τ h).app ((seqExtension J B τ b).obj M) ≫
        (res (coefficientMap J B τ h)).map
          ((seqOrdinaryEvaluation J B τ b n).hom.app M) =
      SheafOfModules.SequenceProjection.transition.{c, v, r}
        b.pt (rings J B τ) b.π M h := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change ((seqOrdinaryEvaluation J B τ b n).hom.app M).val.app U
    (((transition J B τ h).app ((seqExtension J B τ b).obj M)).val.app U
      (((seqOrdinaryEvaluation J B τ b m).inv.app M).val.app U x)) = _
  rw [seqOrdinaryEvaluation_inv, seqOrdinaryEvaluation_hom, seqTransition_apply]
  change ((SheafOfModules.SequenceProjection.extensionObj.{c, v, r}
    b.pt (rings J B τ) b.π M).level n).val.map (𝟙 U) _ = _
  rw [PresheafOfModules.map_id]
  rfl

private theorem seqOrdinaryTransition (b : Cone (rings.{c, v, r} J B τ))
    (M : Mod.{c, v, r} J b.pt) (m n : ℕ) (h : n ≤ m) (U : Cᵒᵖ)
    (a : (B m).obj.obj U) (x : M.val.obj U) :
    (((seqOrdinaryEvaluation J B τ b m).inv.app M ≫
      (transition J B τ h).app ((seqExtension J B τ b).obj M) ≫
        (res (coefficientMap J B τ h)).map
          ((seqOrdinaryEvaluation J B τ b n).hom.app M)).val.app U)
            (completionScalarSection J (b.π.app (op m))
              (seqScalarData J B τ b m) M U a x) =
      completionScalarSection J (b.π.app (op n)) (seqScalarData J B τ b n) M U
        ((coefficientMap J B τ h).hom.app U a) x := by
  have ht := congrArg (fun f ↦ f.val.app U
    (completionScalarSection J (b.π.app (op m)) (seqScalarData J B τ b m) M U a x))
      (seqTransitionMorphism J B τ b M m n h)
  exact ht.trans (SheafOfModules.SequenceProjection.transition_tmul.{c, v, r}
    b.pt (rings J B τ) b.π M h U a x)

private def seqOrdinary (b : Cone (rings.{c, v, r} J B τ)) :
    SequenceOrdinaryPullback J B τ b (seqSetProjection J B τ b)
      (seqModuleRestriction J B τ b) where
  extension := seqExtension J B τ b
  moduleAdjunction := seqModuleAdjunction J B τ b
  level := seqScalarData J B τ b
  ordinaryEvaluation := seqOrdinaryEvaluation J B τ b
  ordinary_unit := seqUnitProjection J B τ b
  ordinary_transition := seqOrdinaryTransition J B τ b

private abbrev seqGood (b : Cone (rings.{c, v, r} J B τ))
    (P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ) :=
  P.IsKFlatIndependentCoefficients ∧ ∀ i : ℤ, (P.X i).IsFlatOnSite

private theorem seqResolution (b : Cone (rings.{c, v, r} J B τ))
    (P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ) :
    ∃ (Q : CochainComplex (Mod.{c, v, r} J b.pt) ℤ) (f : Q ⟶ P),
      seqGood J B τ b Q ∧ QuasiIso f :=
  SheafOfModules.SequenceProjection.flatResolution b.pt P

private theorem seqMapCompQuasiIso
    {A D' E' : Type*} [Category A] [Category D'] [Category E']
    [Abelian A] [Abelian D'] [Abelian E']
    (F : A ⥤ D') (G : D' ⥤ E') [F.Additive] [G.Additive] [G.IsEquivalence]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q)
    (hf : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map f) := by
  let := hf
  exact inferInstanceAs (QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map
    ((F.mapHomologicalComplex (.up ℤ)).map f)))

private theorem seqExtensionPreserves (b : Cone (rings.{c, v, r} J B τ))
    {P Q : CochainComplex (Mod.{c, v, r} J b.pt) ℤ} (f : P ⟶ Q)
    (hP : seqGood J B τ b P) (hQ : seqGood J B τ b Q) (hf : QuasiIso f) :
    QuasiIso (((seqExtension J B τ b).mapHomologicalComplex (.up ℤ)).map f) := by
  let G := SheafOfModules.strictSystemToSequenceFunctor (rings J B τ)
  have : G.IsEquivalence :=
    inferInstanceAs (SheafOfModules.strictSystemSequenceEquivalence
      (rings J B τ)).functor.IsEquivalence
  have : G.Additive :=
    { map_add := by
        intro M N f g
        ext U x
        exact congrArg (fun f ↦ f.val.app (op U.unop.2) x)
          ((SheafOfModules.systemEvaluation (rings J B τ) U.unop.1).map_add (f := f) (g := g)) }
  exact seqMapCompQuasiIso
    (SheafOfModules.SequenceProjection.extension.{c, v, r} b.pt (rings J B τ) b.π)
    G f (SheafOfModules.SequenceProjection.extension_preserves
      b.pt (rings J B τ) b.π f hP.1 hQ.1 hf)

private theorem seqDerivedFromClass
    {A D' : Type*} [Category A] [Category D'] [Abelian A] [Abelian D']
    [HasDerivedCategory.{r} A] [HasDerivedCategory.{r} D']
    (E : A ⥤ D') [E.Additive] (good : CochainComplex A ℤ → Prop)
    (hresolve : ∀ K, ∃ (L : CochainComplex A ℤ) (f : L ⟶ K), good L ∧ QuasiIso f)
    (hpreserve : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L),
      good K → good L → QuasiIso f →
        QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) :
    ∃ (L : DerivedCategory A ⥤ DerivedCategory D')
      (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
      (∃ (_ : L.CommShift ℤ), L.IsTriangulated) ∧
      ∀ K, good K → IsIso (ε.app K) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let H := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := D')
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, good K ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, hf⟩ := hresolve K
    exact ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (H.map s) := by
    rintro X Y s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hg := hpreserve f hK hL hf
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient D' (.up ℤ)).map ((E.mapHomologicalComplex (.up ℤ)).map f)))
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso D' (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨_, L, εh, hL, htri, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory D') H P hres hinv
  let := hL
  obtain ⟨ε, hε, he⟩ := CategoryTheory.leftDerivedOnComplexes E (𝟭 (DerivedCategory D')) L εh
  refine ⟨L, ε, hε, htri, ?_⟩
  intro K hK
  rw [he]
  exact hcomp (q.obj K) ⟨K, hK, rfl⟩

private theorem seqDerivedOfPair (b : Cone (rings.{c, v, r} J B τ))
    (g : SequenceSetProjection J B τ b) (u : SequenceModuleRestriction J B τ b g)
    (p : SequenceOrdinaryPullback J B τ b g u)
    (hres : ∀ P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ,
      ∃ (Q : CochainComplex (Mod.{c, v, r} J b.pt) ℤ) (f : Q ⟶ P),
        seqGood J B τ b Q ∧ QuasiIso f)
    (hpres : ∀ {P Q : CochainComplex (Mod.{c, v, r} J b.pt) ℤ} (f : P ⟶ Q),
      seqGood J B τ b P → seqGood J B τ b Q → QuasiIso f →
        QuasiIso (p.extension.mapHomologicalComplex (.up ℤ) |>.map f))
    (L : D.{c, v, r} J b.pt ⥤ DS.{c, v, r} J B τ)
    (ε : completionLocalization J b.pt ⋙ L ⟶
      p.extension.mapHomologicalComplex (.up ℤ) ⋙
        completionLocalization (coefficientSequenceTopology J) (systemRing J B τ))
    (huniv : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)))
    (htri : ∃ (_ : L.CommShift ℤ), L.IsTriangulated)
    (hcomp : ∀ P, seqGood J B τ b P → IsIso (ε.app P)) :
    Nonempty (SequenceDerivedPullback J B τ b g u p) := by
  classical
  let c (n : ℕ) :=
    Functor.mapHomologicalComplexCompIso (p.ordinaryEvaluation n) (.up ℤ)
  let η (n : ℕ) : completionLocalization J b.pt ⋙ L ⋙ e J B τ n ⟶
      (p.level n).model.E.mapHomologicalComplex (.up ℤ) ⋙
        completionLocalization J (B n) :=
    Functor.whiskerRight ε (e J B τ n) ≫
      Functor.whiskerLeft (p.extension.mapHomologicalComplex (.up ℤ))
        (Functor.mapDerivedCategoryFactors (evaluation J B τ n)).hom ≫
      Functor.whiskerRight (c n).hom (completionLocalization J (B n))
  have hη (n : ℕ) (P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ)
      (hP : seqGood J B τ b P) : IsIso ((η n).app P) := by
    have := hcomp P hP
    dsimp [η]
    infer_instance
  have hθ (n : ℕ) (P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ)
      (hP : seqGood J B τ b P) : IsIso ((p.level n).model.ε.app P) :=
    (p.level n).model.computes P hP.1
  choose δ hδ using fun n ↦
    (comparison_from_resolutions (seqGood J B τ b) hres
      (L ⋙ e J B τ n) (p.level n).T _ (η n)
      (p.level n).model.ε (hη n) (hθ n)).exists
  refine ⟨{ derived := L
            ε := ε
            universal := huniv
            triangulated := htri
            computes := fun P hk hf ↦ hcomp P ⟨hk, hf⟩
            preserves := fun f hk hf hq hqf hqi ↦
              hpres f ⟨hk, hf⟩ ⟨hq, hqf⟩ hqi
            derivedEvaluation := δ
            complexEvaluation := c
            complexEvaluation_f := by intros; rfl
            representative_square := by
              intro n P hk hf
              exact hδ n P ⟨hk, hf⟩ }⟩

private theorem seqDerivedForOrdinary (b : Cone (rings.{c, v, r} J B τ))
    (g : SequenceSetProjection J B τ b) (u : SequenceModuleRestriction J B τ b g)
    (p : SequenceOrdinaryPullback J B τ b g u)
    (hres : ∀ P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ,
      ∃ (Q : CochainComplex (Mod.{c, v, r} J b.pt) ℤ) (f : Q ⟶ P),
        seqGood J B τ b Q ∧ QuasiIso f)
    (hpres : ∀ {P Q : CochainComplex (Mod.{c, v, r} J b.pt) ℤ} (f : P ⟶ Q),
      seqGood J B τ b P → seqGood J B τ b Q → QuasiIso f →
        QuasiIso ((p.extension.mapHomologicalComplex (.up ℤ)).map f)) :
    Nonempty (SequenceDerivedPullback J B τ b g u p) := by
  obtain ⟨L, ε, hu, ht, hc⟩ := seqDerivedFromClass p.extension
    (seqGood J B τ b) hres hpres
  exact seqDerivedOfPair J B τ b g u p hres hpres L ε hu ht hc

private theorem seqDerived (b : Cone (rings.{c, v, r} J B τ)) :
    Nonempty (SequenceDerivedPullback J B τ b (seqSetProjection J B τ b)
      (seqModuleRestriction J B τ b) (seqOrdinary J B τ b)) :=
  seqDerivedForOrdinary J B τ b (seqSetProjection J B τ b)
    (seqModuleRestriction J B τ b) (seqOrdinary J B τ b)
    (seqResolution J B τ b) (seqExtensionPreserves J B τ b)

private theorem seqAssemble (b : Cone (rings.{c, v, r} J B τ))
    (g : SequenceSetProjection J B τ b) (u : SequenceModuleRestriction J B τ b g)
    (p : SequenceOrdinaryPullback J B τ b g u)
    (hd : Nonempty (SequenceDerivedPullback J B τ b g u p)) :
    Nonempty (SequenceCompletionProjection J B τ b) := by
  obtain ⟨d⟩ := hd
  exact ⟨⟨g, u, p, d⟩⟩

/-- The canonical sequence-site equivalence is exact, and the limit cone defines the
constant/limit ringed projection with the simultaneous K-flat reduction model.
Source: Stacks 0940, 06YY, 03D6, 03D7 and 03DB; Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-sequence-site-completion-projection).

Proof:
1. The recorded completion equivalence is the identity, hence preserves finite
   limits and colimits.
2. Restrict a set sheaf to each vertical slice. Conversely, the product-site
   covering sieves test sheafness on each slice. Constant sequences are therefore
   sheaves; their coordinate maps identify morphisms to a sequence with cones,
   giving the constant/limit adjunction. Reflection through presheaves proves
   finite-limit preservation.
3. Restrict the strict-system equivalence along the cone's ring maps. Evaluation
   detects finite limits and colimits, so this restriction is additive and exact.
   Forgetting modules commutes with tower limits. The resulting comparison and
   its coordinate equations identify the induced module direct image.
4. Use the existing strict ordinary extension, scalar models and adjunction.
   Transport them through the strict-system/sequence-site equivalence. The
   composite-adjunction unit projects to the scalar unit; the strict transition
   formula gives the required sheafified pure-tensor formula.
5. Flat-term K-flat resolutions form a resolving class. The strict extension
   preserves quasi-isomorphisms on this class, as does the sequence equivalence.
   Derive it on the homotopy category and normalize the resulting counit on
   complexes. This constructs a single triangulated derived functor before
   evaluating at any level.
6. Exact evaluation and the ordinary evaluation comparison give a transformation
   which is invertible on the same resolutions. Comparison from resolutions
   supplies the level derived isomorphisms and exactly their representative
   squares. -/
theorem sequenceSiteCompletionProjection (b : Cone (rings.{c, v, r} J B τ))
    (_hb : IsLimit b) :
    PreservesFiniteLimits
      (completionSystemEquivalence.{c, v, r} J B τ).inverse ∧
    PreservesFiniteColimits
      (completionSystemEquivalence.{c, v, r} J B τ).inverse ∧
    Nonempty (SequenceCompletionProjection.{c, v, r} J B τ b) := by
  refine ⟨?_, ?_, ?_⟩
  · change PreservesFiniteLimits (𝟭 _)
    infer_instance
  · change PreservesFiniteColimits (𝟭 _)
    infer_instance
  · exact seqAssemble J B τ b (seqSetProjection J B τ b)
      (seqModuleRestriction J B τ b) (seqOrdinary J B τ b) (seqDerived J B τ b)

end WeilConjectures.SemilinearSections

attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
