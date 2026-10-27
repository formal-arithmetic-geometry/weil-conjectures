/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.RingedSiteModules


/-! # Data of finite-free derived scalar calculus

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraphs 1-2; Stacks 03CZ, 06YY and 06YU.
(blueprint: lem-sf-finite-free-derived-scalar-calculus)

(blueprint: def-sf-finite-free-scalar-calculus-data)

The auxiliary structure packages the conclusions, with the ordinary functor fixed to
sheafified scalar extension and the derived functor fixed to its exact descent. Its
universal counit identifies this descent with derived change of rings. All comparison
maps are normalized, including on homogeneous summands of K-flat total tensor complexes.

## Main statements

* `FiniteFreeScalarCalculus`: the complete normalized conclusion package.
* `finiteFreeDerivedScalarCalculus`: existence of this package on each of the two sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

universe a v

/-- Compatibility of a derived tensor comparison with its specified balancing maps
on homogeneous summands of K-flat cochain models. All tensor and localization structures
are the existing canonical ones; the parameters merely abbreviate their categories.
Source: Stacks 06YU (blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
def finiteScalarTensorModelsCompatible
    {CA CB : Type a} [Category.{v} CA] [Category.{v} CB] [Abelian CA] [Abelian CB]
    [IsGrothendieckAbelian.{v} CA] [IsGrothendieckAbelian.{v} CB]
    [HasDerivedCategory.{v} CA] [HasDerivedCategory.{v} CB]
    [MonoidalCategory CA] [MonoidalCategory CB]
    [MonoidalPreadditive CA] [MonoidalPreadditive CB]
    [MonoidalClosed CA] [MonoidalClosed CB] [BraidedCategory CA] [BraidedCategory CB]
    [Abelian.HasFunctorialFlatResolution CA] [Abelian.HasFunctorialFlatResolution CB]
    [HasColimitsOfSize.{0, 0} CA] [HasColimitsOfSize.{0, 0} CB]
    (E : CA ⥤ CB) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U : CB ⥤ CA) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (β : ∀ (M : CA) (N : CB), U.obj (E.obj M ⊗ N) ≅ M ⊗ U.obj N)
    (δ : ∀ (K : DerivedCategory CA) (N : DerivedCategory CB),
      U.mapDerivedCategory.obj (E.mapDerivedCategory.obj K ⊗ N) ≅
        K ⊗ U.mapDerivedCategory.obj N) : Prop :=
  letI (P Q : CochainComplex CA ℤ) : HomologicalComplex.HasTensor P Q :=
    fun _n ↦ HasColimitsOfShape.has_colimit _
  letI (P Q : CochainComplex CB ℤ) : HomologicalComplex.HasTensor P Q :=
    fun _n ↦ HasColimitsOfShape.has_colimit _
  ∀ (P : CochainComplex CA ℤ) (Q : CochainComplex CB ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
    ∃ c : ((U.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.tensorObj
          ((E.mapHomologicalComplex (.up ℤ)).obj P) Q) ≅
      HomologicalComplex.tensorObj P
        ((U.mapHomologicalComplex (.up ℤ)).obj Q)),
      (∀ (i j n : ℤ) (h : i + j = n),
        U.map
            (HomologicalComplex.ιTensorObj (C := CB)
              ((E.mapHomologicalComplex (.up ℤ)).obj P)
              Q i j n h) ≫ c.hom.f n =
          (β (P.X i) (Q.X j)).hom ≫
            HomologicalComplex.ιTensorObj (C := CA) P
              ((U.mapHomologicalComplex (.up ℤ)).obj Q)
              i j n h) ∧
      U.mapDerivedCategory.map
          ((E.mapDerivedCategoryFactors.hom.app P ▷
              DerivedCategory.Q.obj Q) ≫ Functor.LaxMonoidal.μ
            (DerivedCategory.Q (C := CB))
            ((E.mapHomologicalComplex (.up ℤ)).obj P)
            Q) ≫
        U.mapDerivedCategoryFactors.hom.app
          (HomologicalComplex.tensorObj
            ((E.mapHomologicalComplex (.up ℤ)).obj P)
            Q) ≫ DerivedCategory.Q.map c.hom =
        (δ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
          (DerivedCategory.Q.obj P ◁
            U.mapDerivedCategoryFactors.hom.app Q) ≫
          Functor.LaxMonoidal.μ
            (DerivedCategory.Q (C := CA)) P
            ((U.mapHomologicalComplex (.up ℤ)).obj Q)


/-- The derived balancing isomorphism and its full cochain-model normalization.
This is a conclusion package over the existing tensor and localization structures.
Source: Stacks 06YU (blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
structure FiniteScalarDerivedTensorModels
    {CA CB : Type a} [Category.{v} CA] [Category.{v} CB] [Abelian CA] [Abelian CB]
    [IsGrothendieckAbelian.{v} CA] [IsGrothendieckAbelian.{v} CB]
    [HasDerivedCategory.{v} CA] [HasDerivedCategory.{v} CB]
    [MonoidalCategory CA] [MonoidalCategory CB]
    [MonoidalPreadditive CA] [MonoidalPreadditive CB]
    [MonoidalClosed CA] [MonoidalClosed CB] [BraidedCategory CA] [BraidedCategory CB]
    [Abelian.HasFunctorialFlatResolution CA] [Abelian.HasFunctorialFlatResolution CB]
    [HasColimitsOfSize.{0, 0} CA] [HasColimitsOfSize.{0, 0} CB]
    (E : CA ⥤ CB) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U : CB ⥤ CA) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (β : ∀ (M : CA) (N : CB), U.obj (E.obj M ⊗ N) ≅ M ⊗ U.obj N) where
  tensor_iso : ∀ (K : DerivedCategory CA) (N : DerivedCategory CB),
    U.mapDerivedCategory.obj (E.mapDerivedCategory.obj K ⊗ N) ≅
      K ⊗ U.mapDerivedCategory.obj N
  tensor_natural : ∀ {K K' : DerivedCategory CA} {N N' : DerivedCategory CB}
      (f : K ⟶ K') (g : N ⟶ N'),
    U.mapDerivedCategory.map (E.mapDerivedCategory.map f ⊗ₘ g) ≫
      (tensor_iso K' N').hom = (tensor_iso K N).hom ≫
        (f ⊗ₘ U.mapDerivedCategory.map g)
  tensor_normalized : finiteScalarTensorModelsCompatible E U β tensor_iso

end CategoryTheory

namespace AlgebraicGeometry

section Site
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  (φ : A →+* B)

/-- The ordinary scalar functor in the calculus: sheafified sectionwise extension.
Source: Stacks 03CZ (blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
def finiteScalarExtension :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

/-- The actual scalar adjunction, whose unit sends m to 1 tensor m.
Source: Stacks 03CZ (blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
def finiteScalarAdjunction : finiteScalarExtension J φ ⊣ Sheaf.restrictScalars J φ :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- Additivity of the fixed ordinary scalar functor, from its scalar adjunction.
Source: Stacks 03CZ (blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
instance finiteScalarExtension_additive : (finiteScalarExtension J φ).Additive :=
  (finiteScalarAdjunction J φ).left_adjoint_additive

/-- A local pure scalar tensor followed by module sheafification.
Mathlib orders its factors as b tensor m rather than m tensor b.
Source: Stacks 03CZ (blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
def finiteScalarPure (M : Sheaf J (ModuleCat.{u + 1} A)) (V : Cᵒᵖ)
    (b : B) (m : M.obj.obj V) : ((finiteScalarExtension J φ).obj M).obj.obj V :=
  ((sheafificationAdjunction J (ModuleCat.{u + 1} B)).unit.app
    (M.obj ⋙ ModuleCat.extendScalars φ)).app V (b ⊗ₜ[A] m)

/-- A local pure tensor in the canonical sheafified tensor product.
Source: Stacks 03EK (blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
def finiteScalarTensorPure (R : Type (u + 1)) [CommRing R]
    (M N : Sheaf J (ModuleCat.{u + 1} R)) (V : Cᵒᵖ)
    (m : M.obj.obj V) (n : N.obj.obj V) : (M ⊗ N).obj.obj V :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{u + 1} R)) M N).app V)
    (m ⊗ₜ[R] n)

/-- Exact descent, adjunction, conservativity and the finite-basis decomposition.
These fields package conclusions about the fixed ordinary scalar functors.
Source: Stacks 03CZ, 06YY and 05RT
(blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
structure FiniteFreeScalarDescent [Algebra A B] (r : ℕ)
    (basis : Module.Basis (Fin r) A B) where
  [extension_limits : PreservesFiniteLimits (finiteScalarExtension J (algebraMap A B))]
  [extension_colimits : PreservesFiniteColimits (finiteScalarExtension J (algebraMap A B))]
  [restriction_limits : PreservesFiniteLimits (Sheaf.restrictScalars J (algebraMap A B))]
  [restriction_colimits : PreservesFiniteColimits (Sheaf.restrictScalars J (algebraMap A B))]
  universal : (finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.IsLeftDerivedFunctor
    (finiteScalarExtension J (algebraMap A B)).mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ))
  adjunction : (finiteScalarExtension J (algebraMap A B)).mapDerivedCategory ⊣
    Sheaf.derivedRestrictScalars J (algebraMap A B)
  unit_normalized : ∀ P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ,
    adjunction.unit.app (DerivedCategory.Q.obj P) ≫
      (Sheaf.derivedRestrictScalars J (algebraMap A B)).map
        ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategoryFactors.hom.app P) ≫
      (Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategoryFactors.hom.app
        (((finiteScalarExtension J (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (finiteScalarAdjunction J (algebraMap A B)).unit (.up ℤ)).app P)
  counit_normalized : ∀ Q : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ,
    adjunction.counit.app (DerivedCategory.Q.obj Q) =
      (finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.map
        ((Sheaf.restrictScalars J (algebraMap A B)).mapDerivedCategoryFactors.hom.app Q) ≫
      (finiteScalarExtension J (algebraMap A B)).mapDerivedCategoryFactors.hom.app
        (((Sheaf.restrictScalars J (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (finiteScalarAdjunction J (algebraMap A B)).counit (.up ℤ)).app Q)
  reflects_iso : (Sheaf.derivedRestrictScalars J (algebraMap A B)).ReflectsIsomorphisms
  reflects_zero : ∀ N : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)),
    IsZero ((Sheaf.derivedRestrictScalars J (algebraMap A B)).obj N) → IsZero N
  basis_iso : ∀ K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)),
    (Sheaf.derivedRestrictScalars J (algebraMap A B)).obj
      ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.obj K) ≅
        ⨁ (fun _j : Fin r ↦ K)
  basis_natural : ∀ {K L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))} (f : K ⟶ L),
    (Sheaf.derivedRestrictScalars J (algebraMap A B)).map
        ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.map f) ≫
      (basis_iso L).hom = (basis_iso K).hom ≫ biproduct.map (fun _j : Fin r ↦ f)
  basis_inclusion : ∀ (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) (j : Fin r),
    biproduct.ι (fun _j : Fin r ↦ K) j ≫ (basis_iso K).inv =
      adjunction.unit.app K ≫ (Sheaf.derivedRestrictScalars J (algebraMap A B)).map
        (basis j • 𝟙 ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.obj K))
  kflat_extension : ∀ P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ,
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((finiteScalarExtension J (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj P)

/-- The normalized sheaf, total-complex and derived balancing comparisons.
Source: Stacks 05V4 and 06YU
(blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
structure FiniteFreeScalarTensorCalculus [Algebra A B] (r : ℕ)
    (basis : Module.Basis (Fin r) A B) extends FiniteFreeScalarDescent J r basis where
  sheaf_balance : ∀ (M : Sheaf J (ModuleCat.{u + 1} A))
      (N : Sheaf J (ModuleCat.{u + 1} B)),
    (Sheaf.restrictScalars J (algebraMap A B)).obj
        (((finiteScalarExtension J (algebraMap A B)).obj M) ⊗ N) ≅
      M ⊗ (Sheaf.restrictScalars J (algebraMap A B)).obj N
  balance_forward : ∀ (M : Sheaf J (ModuleCat.{u + 1} A))
      (N : Sheaf J (ModuleCat.{u + 1} B)) (V : Cᵒᵖ)
      (m : M.obj.obj V) (b : B) (n : N.obj.obj V),
    (sheaf_balance M N).hom.hom.app V
      (finiteScalarTensorPure J B _ N V
        (finiteScalarPure J (algebraMap A B) M V b m) n) =
      finiteScalarTensorPure J A M _ V m (b • n)
  balance_inverse : ∀ (M : Sheaf J (ModuleCat.{u + 1} A))
      (N : Sheaf J (ModuleCat.{u + 1} B)) (V : Cᵒᵖ)
      (m : M.obj.obj V) (n : N.obj.obj V),
    (sheaf_balance M N).inv.hom.app V (finiteScalarTensorPure J A M _ V m n) =
      finiteScalarTensorPure J B _ N V
        (finiteScalarPure J (algebraMap A B) M V 1 m) n
/-- The full scalar calculus, including constructibility and the unchanged Tor interval.
This packages conclusions, and assumes no scalar exactness or comparison isomorphism.
Source: blueprint finite-free-extension proof, paragraphs 1-2; Stacks 03CZ and 06YU
(blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
structure FiniteFreeScalarCalculus [Algebra A B] (r : ℕ)
    (basis : Module.Basis (Fin r) A B)
    (bcA : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))))
    (bcB : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))))
    extends FiniteFreeScalarTensorCalculus J r basis where
  derived_tensor : FiniteScalarDerivedTensorModels
    (finiteScalarExtension J (algebraMap A B)) (Sheaf.restrictScalars J (algebraMap A B))
    sheaf_balance
  bounded_constructible : ∀ K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)),
    bcA K → bcB ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.obj K)
  tor_amplitude : ∀ (a b : ℤ) (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))),
    DerivedCategory.torAmplitudeIn _ a b K →
    DerivedCategory.torAmplitudeIn _ a b
      ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.obj K)

end Site

/-- The canonical size witness of the small pro-etale site, with no universe lift.
Source: Mathlib `essentiallySmallSelf`; Stacks 098K
(blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
instance finiteScalarProEtaleSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _

end AlgebraicGeometry
