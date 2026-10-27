/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.AlgebraicGeometry.SchemeLiftClassificationData
public import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
public import Mathlib.RingTheory.EssentialFiniteness

/-! # The affine comparison in first-order deformation theory
Source: Stacks 0D0I, 08UW and 08UZ
(blueprint: def-sfb-affine-scheme-deformation-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Algebra.CotangentResolution
open scoped TensorProduct
namespace AlgebraicGeometry.SchemeDeformation
variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
  [∀ X : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]

/-- The actual affine structure morphism. Source: Stacks 01I1
(blueprint: def-sfb-affine-scheme-deformation-comparison). -/
def affineMorphism (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    Spec (.of A) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

/-- Its ring arrow. Source: Stacks 08UW
(blueprint: def-sfb-affine-scheme-deformation-comparison). -/
def affineArrow (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    Arrow CommRingCat.{u} := Arrow.mk (CommRingCat.ofHom (algebraMap k A))

/-- Associated sheafification in the shared raw module category. Source: Stacks 01HV
(blueprint: def-sfb-affine-scheme-deformation-comparison). -/
abbrev affineTilde (A : Type u) [CommRing A] : ModuleCat.{u} (CommRingCat.of A) ⥤
    SheafOfModules.{u} (Spec (.of A)).ringCatSheaf := tilde.functor (.of A)

/-- Additivity of associated sheafification in the shared category. Source: Stacks 01HV
(blueprint: def-sfb-affine-scheme-deformation-comparison). -/
instance affineTildeAdditive (A : Type u) [CommRing A] : (affineTilde A).Additive :=
  ⟨fun {_ _} f g ↦ tilde.map_add f g⟩

/-- Associated sheafification is a left adjoint. Source: Stacks 01HV
(blueprint: def-sfb-affine-scheme-deformation-comparison). -/
instance affineTildeColimits (A : Type u) [CommRing A] :
    PreservesColimits (affineTilde A) :=
  (tilde.adjunction (R := .of A)).leftAdjoint_preservesColimits

/-- Exactness of the actual associated-sheaf functor, from the recorded finite-limit
preservation theorem. Source: Stacks 01HV
(blueprint: def-sfb-affine-scheme-deformation-comparison). -/
instance affineTildeExact (A : Type u) [CommRing A] :
    PreservesFiniteLimits (affineTilde A) := tilde_preserves_finite_limits A

/-- The affine cotangent and coefficient comparisons, fixed on all local generators.
Source: Stacks 0D0I and 08UW
(blueprint: def-sfb-affine-scheme-deformation-comparison). -/
structure AffineComparison (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] where
  square (V : (Spec (.of A)).Opens) : affineArrow k A ⟶
    TopCat.SheafCotangent.sectionArrow
      (Arrow.mk (Scheme.Modules.tensorPullbackRingMap (affineMorphism k A))) (op V)
  left (V : (Spec (.of A)).Opens)
    (h : V ≤ (affineMorphism k A) ⁻¹ᵁ ⊤) (a : k) :
    (square V).left a = inverseSection (affineMorphism k A) ⊤ V h
      ((Scheme.ΓSpecIso (.of k)).inv a)
  right (V : (Spec (.of A)).Opens) (a : A) :
    (square V).right a = (Spec (.of A)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (.of A)).inv a)
  map : (CotangentPresentation.tildeComplexFunctor (.of A)).obj
    (standardComplex C (affineArrow k A)) ⟶ cotangentComplex C D (affineMorphism k A)
  comparison : DerivedCategory.Q.obj
    ((CotangentPresentation.tildeComplexFunctor (.of A)).obj
      (standardComplex C (affineArrow k A))) ≅
        DerivedCategory.Q.obj (cotangentComplex C D (affineMorphism k A))
  normalization : comparison.hom = DerivedCategory.Q.map map
  sections (V : (Spec (.of A)).Opens) (n : ℤ)
    (x : (standardComplex C (affineArrow k A)).X n) :
    (map.f n).val.app (op V)
      (tilde.toOpen (R := .of A) ((standardComplex C (affineArrow k A)).X n) V x) =
      TopCat.SheafCotangent.sectionElement
        (D.sheaves (Spec (.of A)).carrier
          (Arrow.mk (Scheme.Modules.tensorPullbackRingMap (affineMorphism k A)))).sections
        (op V) n ((standardComplexMap C (square V)).f n x)
  coefficient (M : ModuleCat.{u} k) : directionModule (affineMorphism k A) M ≅
    (affineTilde A).obj (ModuleCat.of A (A ⊗[k] M))
  coefficient_sections (M : ModuleCat.{u} k) (m : M) :
    ((coefficient M).hom.app ((affineMorphism k A) ⁻¹ᵁ ⊤))
      (Scheme.Modules.tensorPullbackSection (affineMorphism k A) _ ⊤
        (tilde.toOpen (R := .of k) M ⊤ m)) =
      tilde.toOpen (R := .of A) (ModuleCat.of A (A ⊗[k] M)) ((affineMorphism k A) ⁻¹ᵁ ⊤) (1 ⊗ₜ m)

/-- Transport a full affine cotangent Ext class using exact tilde and the normalized
comparisons, with the canonical shift and degree-zero identifications. Source: Stacks 0D0I
(blueprint: def-sfb-affine-scheme-deformation-comparison). -/
def AffineComparison.ext {C : Coherence.{u}} {D : TopCat.SheafCotangent.Comparison C}
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (a : AffineComparison C D k A) (M : ModuleCat.{u} k) (n : ℤ)
    (ξ : Algebra.CotangentResolution.cotangentComplex C (affineArrow k A) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj
        (ModuleCat.of A (A ⊗[k] M)))⟦n⟧) :
    Ext C D (affineMorphism k A) (directionModule (affineMorphism k A) M) n :=
  a.comparison.inv ≫
    (affineTilde A).mapDerivedCategoryFactors.inv.app _ ≫
    (affineTilde A).mapDerivedCategory.map ξ ≫
    ((affineTilde A).mapDerivedCategory.commShiftIso n).hom.app _ ≫
    ((affineTilde A).mapDerivedCategorySingleFunctor 0).hom.app _⟦n⟧' ≫
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (Spec (.of A)).ringCatSheaf) 0).map
      (a.coefficient M).inv)⟦n⟧'

/-- The canonical map from the Ext of the actual two-term presentation: precompose
with the recorded truncation projection, then apply the affine comparison.
Source: Stacks 08UW and 0D0I
(blueprint: def-sfb-affine-scheme-deformation-comparison). -/
def AffineComparison.naiveExt {C : Coherence.{u}}
    {D : TopCat.SheafCotangent.Comparison C} {k A : Type u}
    [Field k] [CommRing A] [Algebra k A] (a : AffineComparison C D k A)
    (κ : Naive.Comparison C) (P : Naive.Presentation (affineArrow k A))
    (hP : Naive.IsLocalizedPolynomial P) (M : ModuleCat.{u} k)
    (ξ : DerivedCategory.Q.obj (Naive.complex P) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj
        (ModuleCat.of A (A ⊗[k] M)))⟦(1 : ℤ)⟧) :
    Ext C D (affineMorphism k A) (directionModule (affineMorphism k A) M) 1 :=
  a.ext M 1 (κ.comparison P hP ≫ ξ)

/-- A coefficient restriction is the unique semilinear map on tensor generators.
Source: Stacks 08SF (blueprint: def-sfb-affine-scheme-deformation-comparison). -/
structure TensorCoefficientRestriction {k A B : Type u} [Field k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B]
    (q : affineArrow k A ⟶ affineArrow k B) (M : ModuleCat.{u} k) where
  map : ModuleCat.of A (A ⊗[k] M) ⟶
    (ModuleCat.restrictScalars q.right.hom).obj (ModuleCat.of B (B ⊗[k] M))
  tensors (a : A) (m : M) : map (a ⊗ₜ m) = TensorProduct.tmul k (M := B) (N := M) (q.right a) m

/-- The actual semilinear restriction relation on full cotangent Ext, expressed using
exact restriction of scalars, its shift comparison and the fixed cotangent square map.
Source: Stacks 08SF (blueprint: def-sfb-affine-scheme-deformation-comparison). -/
def IsAffineExtRestriction (C : Coherence.{u}) {k A B : Type u}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (q : affineArrow k A ⟶ affineArrow k B) (M : ModuleCat.{u} k)
    (r : TensorCoefficientRestriction q M)
    (ξ : Algebra.CotangentResolution.cotangentComplex C (affineArrow k A) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj
        (ModuleCat.of A (A ⊗[k] M)))⟦(1 : ℤ)⟧)
    (η : Algebra.CotangentResolution.cotangentComplex C (affineArrow k B) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of B)) 0).obj
        (ModuleCat.of B (B ⊗[k] M)))⟦(1 : ℤ)⟧) : Prop :=
  ξ ≫ ((DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).map r.map)⟦1⟧' =
    cotangentMap C q ≫ (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.map η ≫
      ((ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
      ((ModuleCat.restrictScalars q.right.hom).mapDerivedCategorySingleFunctor 0).hom.app _⟦1⟧'

end AlgebraicGeometry.SchemeDeformation
