/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.RingTheory.MarkedFlatAlgebraDeformations
public import Sheaf.RingTheory.NaiveCotangentComparison
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Continuous conormal coordinates for completed tangent classes

Source: Stacks Project, examples-defos.tex, Tags 0DYV and 0DZM;
More on Algebra, Tags 07ED and 07NJ; Deformation Theory, Tag 0GPZ
(blueprint: def-sfb-completed-scheme-tangent-data).

The complex is the completion of a localized polynomial conormal complex, so its
differential module is continuous. Ordinary differentials of the completed ring
are never substituted for it. Normalization on kernel classes fixes the sign.
## Main definitions

- `arrow`.
- `IsFiniteLocalizedPolynomial`.
- `Completion`.
- `complex`.
- `Ext`.
- `extMap`.
- `Classes`.
- `CompletionOf`.
- `Representative`.
- `Comparison`.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.CompletedSchemeTangent
open ArtinDeformation Algebra.CotangentResolution

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- The arrow of a coefficient algebra. Source: Stacks 08UP
(blueprint: def-sfb-completed-scheme-tangent-data). -/
abbrev arrow : Arrow CommRingCat.{u} := Arrow.mk (CommRingCat.ofHom (algebraMap k A))

/-- A localized polynomial presentation with finitely many variables. This makes
ordinary scalar completion of its differential module equal to continuous completion.
Source: Stacks 07ED and 07NJ (blueprint: def-sfb-completed-scheme-tangent-data). -/
def IsFiniteLocalizedPolynomial (P : Naive.Presentation (arrow (k := k) (A := A))) : Prop :=
  ∃ (E : Type u) (_hE : Finite E)
    (a : CommRingCat.of (MvPolynomial E k) ⟶ P.ring)
    (W : Submonoid (MvPolynomial E k)),
    (∀ x : k, a (MvPolynomial.C x) = P.base x) ∧
    (letI := a.hom.toAlgebra; IsLocalization W P.ring)

/-- The completed local ring, as the actual inverse limit. Source: Stacks 0DYV
(blueprint: def-sfb-completed-scheme-tangent-data). -/
abbrev Completion (A : Type u) [CommRing A] [IsLocalRing A] :=
  AdicCompletion (IsLocalRing.maximalIdeal A) A

/-- Completed two-term cotangent complex. Its degree-zero module is the completed
polynomial differential module. Source: Stacks 07ED, 07NJ and 0GPZ
(blueprint: def-sfb-completed-scheme-tangent-data). -/
def complex [IsLocalRing A] (P : Naive.Presentation (arrow (k := k) (A := A))) :=
  ((ModuleCat.extendScalars (algebraMap A (Completion A))).mapHomologicalComplex (.up ℤ)).obj
    (Naive.complex P)

/-- Continuous cotangent Ext-one, with the structure module in degree zero.
Source: Stacks 0GPZ (blueprint: def-sfb-completed-scheme-tangent-data). -/
abbrev Ext [IsLocalRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} (Completion A))]
    (P : Naive.Presentation (arrow (k := k) (A := A))) :=
  DerivedCategory.Q.obj (complex P) ⟶
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (Completion A)) 0).obj
      (ModuleCat.of (Completion A) (Completion A)))⟦(1 : ℤ)⟧

/-- Scalar extension on cotangent Ext, using exact scalar extension and its
canonical shift and single-object comparisons. Source: Stacks 0DYV
(blueprint: def-sfb-completed-scheme-tangent-data). -/
def extMap [IsLocalRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (Completion A))]
    (P : Naive.Presentation (arrow (k := k) (A := A)))
    (ξ : DerivedCategory.Q.obj
      (@id (CochainComplex (ModuleCat.{u} A) ℤ) (Naive.complex P)) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))⟦(1 : ℤ)⟧) :
    Ext P :=
  let E : ModuleCat.{u} A ⥤ ModuleCat.{u} (Completion A) :=
    ModuleCat.extendScalars (algebraMap A (Completion A))
  letI : PreservesFiniteLimits E := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  letI : E.Additive := Functor.additive_of_preserves_binary_products E
  E.mapDerivedCategoryFactors.inv.app _ ≫ E.mapDerivedCategory.map ξ ≫
    (E.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
    (E.mapDerivedCategorySingleFunctor 0).hom.app _⟦(1 : ℤ)⟧' ≫
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (Completion A)) 0).map
      (ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.rid A (Completion A)
        (Completion A)).toLinearMap))⟦(1 : ℤ)⟧'

/-- Tangent classes of the actual marked flat algebra groupoid. Source: Stacks 0DYV
(blueprint: def-sfb-completed-scheme-tangent-data). -/
def Classes (B : Type u) [CommRing B] [Algebra k B] :=
  Quotient (isIsomorphicSetoid
    (Algebra.FlatDeformation.Groupoid B (squareZeroTest (R := k) (k := k) k)))

/-- Completion of a marked tangent deformation, with canonical coefficient map and
finite-quotient marking. Source: Stacks 0DYV
(blueprint: def-sfb-completed-scheme-tangent-data). -/
structure CompletionOf [IsLocalRing A]
    (Q : Algebra.FlatDeformation.Groupoid A (squareZeroTest (R := k) (k := k) k)) where
  deformation : Algebra.FlatDeformation.Groupoid (Completion A)
    (squareZeroTest (R := k) (k := k) k)
  coordinate : Algebra.FlatDeformation.algebra deformation ≃ₐ[k]
    AdicCompletion (Algebra.FlatDeformation.ideal (IsLocalRing.maximalIdeal A) Q)
      (Algebra.FlatDeformation.algebra Q)
  scalar : ∀ a : ring (squareZeroTest (R := k) (k := k) k),
    coordinate (Algebra.FlatDeformation.scalar deformation a) =
      algebraMap _ _ (Algebra.FlatDeformation.scalar Q a)
  marking : Algebra.FlatDeformation.IsCompletionMap
    (Algebra.FlatDeformation.ideal (IsLocalRing.maximalIdeal A) Q)
    (IsLocalRing.maximalIdeal A) (Algebra.FlatDeformation.marking Q).toRingHom
    ((Algebra.FlatDeformation.marking deformation).toRingHom.comp coordinate.symm.toRingHom)

/-- A polynomial lift and its completed conormal cocycle. The equation says precisely
that the class of a relation is the coefficient of epsilon in that lifted relation.
It specifies the canonical tangent classification, including its sign.
Source: Stacks 0GPZ and 07NJ
(blueprint: def-sfb-completed-scheme-tangent-data). -/
structure Representative [IsLocalRing A]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (Completion A))]
    (P : Naive.Presentation (arrow (k := k) (A := A)))
    (Q : Algebra.FlatDeformation.Groupoid (Completion A)
      (squareZeroTest (R := k) (k := k) k)) (ξ : Ext P) where
  lift : P.ring →+* Algebra.FlatDeformation.algebra Q
  base : ∀ a : k, lift (P.base a) = algebraMap k _ a
  quotient : ∀ a : P.ring, Algebra.FlatDeformation.marking Q (lift a) =
    algebraMap A (Completion A) (P.augmentation a)
  cocycle : complex P ⟶
    (CochainComplex.singleFunctor (ModuleCat.{u} (Completion A)) (-1)).obj
      (ModuleCat.of (Completion A) (Completion A))
  relations : ∀ (j : RingHom.ker P.augmentation.hom)
    (t : Algebra.FlatDeformation.algebra Q),
    Algebra.FlatDeformation.scalar Q (TrivSqZeroExt.inr (1 : k)) * t = lift j.val →
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-1)
        (ModuleCat.of (Completion A) (Completion A))).hom
        ((cocycle.f (-1))
          ((((ModuleCat.extendScalars (algebraMap A (Completion A))).mapIso
            (Naive.conormalIso P)).inv) ((1 : Completion A) ⊗ₜ[A] Naive.kernelClass P j))) =
        Algebra.FlatDeformation.marking Q t
  class_eq : ξ = DerivedCategory.Q.map cocycle ≫
    ((DerivedCategory.singleFunctors (ModuleCat.{u} (Completion A))).shiftIso
      1 (-1) 0 (add_neg_cancel (1 : ℤ))).inv.app _

/-- The completed tangent equivalence, normalized on every representative, and the
actual completion map on tangent classes. Source: Stacks 0DYV, 0GPZ and 07NJ
(blueprint: def-sfb-completed-scheme-tangent-data). -/
structure Comparison [IsLocalRing A]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (Completion A))]
    (P : Naive.Presentation (arrow (k := k) (A := A))) where
  classify : Classes (k := k) (Completion A) ≃ Ext P
  representatives : ∀ Q : Algebra.FlatDeformation.Groupoid (Completion A)
    (squareZeroTest (R := k) (k := k) k), Nonempty (Representative P Q (classify ⟦Q⟧))
  normalized : ∀ (Q : Algebra.FlatDeformation.Groupoid (Completion A)
    (squareZeroTest (R := k) (k := k) k)) (ξ : Ext P),
    Nonempty (Representative P Q ξ) → classify ⟦Q⟧ = ξ
  completion : Classes (k := k) A → Classes (k := k) (Completion A)
  exists_completion : ∀ Q : Algebra.FlatDeformation.Groupoid A
    (squareZeroTest (R := k) (k := k) k), Nonempty (CompletionOf Q)
  completion_class : ∀ (Q : Algebra.FlatDeformation.Groupoid A
    (squareZeroTest (R := k) (k := k) k)) (Z : CompletionOf Q),
    completion ⟦Q⟧ = ⟦Z.deformation⟧

end AlgebraicGeometry.CompletedSchemeTangent
