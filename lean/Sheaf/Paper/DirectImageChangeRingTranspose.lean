/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations

/-!
# Restriction of the direct-image coefficient mate

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.proof.md, Step 1; Stacks Tags 0D6D, 0D6E, 07A6 and 07A4
(blueprint: lem-sp-direct-image-change-ring-transpose).

The fixed-coefficient tensor functor is written as scalar extension followed by
restriction. Thus its objects are K tensor_A^L B with B regarded as an A-module,
and its maps are v tensor_A^L id_B. All operations are ordinary and uncompleted.
The tensor/pullback comparison below is the canonical balancing comparison in
these coordinates, obtained from the published restriction and scalar comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The comparison b for the actual constant coefficient square. The coefficient
square commutes because both routes preserve constants and apply the same ring map.
Source: Stacks 0D6D, 07A6; blueprint direct-image proof, Step 1
(blueprint: lem-sp-direct-image-change-ring-transpose). -/
def directImageChangeRingRestrictionPullback
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantPullback (A := B) f ⋙ scalarRestriction φ X ≅
      scalarRestriction φ Y ⋙ constantPullback (A := A) f :=
  proEtaleRingRestrictionDerivedPullback f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (by
      simpa [proEtaleConstantRingComparison, proEtaleConstantRingMap] using
        (proEtaleConstantInverseImageMap_naturality f
          (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)

/-- The specified d: restrict after B-direct-image to A-direct-image after restriction.
It retains the published derived-unit normalization, including on unbounded objects.
Source: Stacks 0D6E, 07A6; blueprint direct-image proof, Step 1
(blueprint: lem-sp-direct-image-change-ring-transpose). -/
def directImageChangeRingRestrictionDirectImage
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y B)
        (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B) ⋙
      scalarRestriction φ Y ≅
    scalarRestriction φ X ⋙ proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) :=
  proEtaleRingRestrictionDerivedDirectImage f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (by
      simpa [proEtaleConstantRingComparison, proEtaleConstantRingMap] using
        (proEtaleConstantInverseImageMap_naturality f
          (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)

/-- The unique B-linear gamma with transpose theta followed by extension of the A-counit.
The adjunction Hom equivalence constructs the specified arrow directly.
Source: blueprint direct-image proof, Step 1; Stacks 07A6
(blueprint: lem-sp-direct-image-change-ring-transpose). -/
def directImageChangeRingGamma
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : proEtaleDerivedCategory X A) :
    (scalarExtensionFunctor φ Y).obj
        ((proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y A)
          (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)).obj N) ⟶
      (proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y B)
        (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).obj
          ((scalarExtensionFunctor φ X).obj N) :=
  (proEtaleRingDerivedAdjunction f (proEtaleConstantRing Y B)
    (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).homEquiv _ _
      ((tensorPullbackIso φ f).hom.app
        ((proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y A)
          (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)).obj N) ≫
        (scalarExtensionFunctor φ X).map
          ((proEtaleRingDerivedAdjunction f (proEtaleConstantRing Y A)
            (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)).counit.app N))

/-- The tensor/pullback identification tau at the coefficient B, in the presentation
K tensor_A^L B = r(T(K)). It is b inverse followed by r(theta). This is a concrete
comparison, with no freely chosen isomorphism. On a flat K-flat representative the
published theta is the balancing map on inverse-image pure tensors; b just forgets
the B-action on that same inverse image. The theorem below asserts the pure-tensor
formula and its derived localization square as a separate conjunct; the definition
alone does not assert that normalization.
Source: blueprint direct-image proof, Step 1; Stacks 03EL, 07A4
(blueprint: lem-sp-direct-image-change-ring-transpose). -/
def directImageChangeRingTensorPullback
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : proEtaleDerivedCategory Y A) :
    (constantPullback (A := A) f).obj
        ((scalarExtensionFunctor φ Y ⋙ scalarRestriction φ Y).obj K) ≅
      (scalarExtensionFunctor φ X ⋙ scalarRestriction φ X).obj
        ((constantPullback (A := A) f).obj K) :=
  (directImageChangeRingRestrictionPullback φ f).symm.app
      ((scalarExtensionFunctor φ Y).obj K) ≪≫
    (scalarRestriction φ X).mapIso ((tensorPullbackIso φ f).app K)

/-- Step 2's normalization of the concrete comparison on every flat K-flat model.
The first equation sends the pullback unit of `s tensor x` to the tensor of the
pulled-back scalar and the pullback unit of `x`, on each base-change object. These
local generators determine the sheaf map. The second equation identifies its
localization with the comparison defined above, using the actual scalar-derived
counits and exact-functor quotient factorizations. Thus this condition identifies
the comparison with the canonical tensor/pullback map, independently of adjunction
mate formalism. No flatness of B over A is required.
Source: blueprint direct-image proof, Step 2; Stacks 03EL and 07A4
(blueprint: lem-sp-direct-image-change-ring-transpose). -/
def IsDirectImageChangeRingTensorPullbackNormalized
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat.{u + 1, u} (R := proEtaleConstantRing Y A) P →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (P.X i)) →
    ∃ t : ((proEtaleConstantRingPullback A f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y)
            φ)).obj P)) ⟶
        ((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
            (((proEtaleConstantRingPullback A f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)),
      (∀ (i : ℤ) (U : Y.ProEt) (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op U))
        (x : (P.X i).val.obj (Opposite.op U)),
        (t.f i).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
            (((proEtaleConstantRingAdjunction A f).unit.app
              ((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).obj
                ((reductionChange Y (proEtaleConstantRingMap (T := Y) φ)).obj (P.X i)))).val.app
                (Opposite.op U)
                (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) (P.X i) (Opposite.op
                  U) s x)) =
          reductionTensorSection X (proEtaleConstantRingMap (T := X) φ)
            ((proEtaleConstantRingPullback A f).obj (P.X i))
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
              (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
                (Opposite.op U)) s)
            (((proEtaleConstantRingAdjunction A f).unit.app (P.X i)).val.app
              (Opposite.op U) x)) ∧
      (constantPullback (A := A) f).map
          ((scalarRestriction φ Y).map (scalarExtensionFunctorCounit φ Y P) ≫
            (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y)
              φ)).mapDerivedCategoryFactors.hom.app ((reductionChangeComplex Y
              (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
        (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app
          (((proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y)
            φ)).obj P)) ≫
        DerivedCategory.Q.map t =
      (directImageChangeRingTensorPullback φ f (DerivedCategory.Q.obj P)).hom ≫
        (scalarRestriction φ X).map
          ((scalarExtensionFunctor φ X).map ((proEtaleConstantRingPullback A
            f).mapDerivedCategoryFactors.hom.app P) ≫
            scalarExtensionFunctorCounit φ X (((proEtaleConstantRingPullback A
              f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X)
          φ)).mapDerivedCategoryFactors.hom.app ((reductionChangeComplex X (proEtaleConstantRingMap
          (T := X) φ)).obj (((proEtaleConstantRingPullback A f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P))

/-- The A-linear map d composed with r(gamma), with its canonical direct-image target.
Source: blueprint direct-image proof, Step 1; Stacks 0D6E
(blueprint: lem-sp-direct-image-change-ring-transpose). -/
def directImageChangeRingRestrictedGamma
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : proEtaleDerivedCategory X A) :
    (scalarExtensionFunctor φ Y ⋙ scalarRestriction φ Y).obj
        ((proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y A)
          (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)).obj N) ⟶
      (proEtaleRingDerivedDirectImage f (proEtaleConstantRing Y A)
        (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)).obj
          ((scalarExtensionFunctor φ X ⋙ scalarRestriction φ X).obj N) :=
  (scalarRestriction φ Y).map (directImageChangeRingGamma φ f N) ≫
    (directImageChangeRingRestrictionDirectImage φ f).hom.app
      ((scalarExtensionFunctor φ X).obj N)

/-- Restricting the proper B-linear coefficient mate gives exactly the pro-etale
projection map for B as an A-module, naturally in every unbounded N.
Source: blueprint main-20261015, direct-image proof, Step 1; Stacks 0D6D, 0D6E, 07A6, 07A4
(blueprint: lem-sp-direct-image-change-ring-transpose).

Proof, following the node's four steps:
1. Apply lem-weil-pbc-ring-sheaf-change-adjunction to the constant coefficient square.
   The square commutes by prop-weil-pbc-proetale-constant-ring-map: on constants
   both paths apply phi. Retain its canonical b and d, with their adjunction normalization.
2. On flat K-flat representatives, the scalar/pullback comparison theta sends the
   inverse image of x tensor s to inverse-image x tensor the image of s. After b
   forgets the B-action this is the tensor/pullback comparison tau. Local pure tensors
   generate the sheaf tensor by def-pur-sheaf-tensor-product. Apply the identity in
   every degree and descend using lem-weil-pbc-site-derived-tensor-descent and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The displayed tau uses exactly
   this restricted-scalar presentation. The first conjunct below states the full
   representative normalization as IsDirectImageChangeRingTensorPullbackNormalized.
   Construct t in each degree by the balanced pure-tensor formula in that predicate;
   sheafification extends it, and naturality in P makes it commute with differentials.
   The scalar-derived counits and exact-functor quotient factorizations identify its
   localization with tau, giving the predicate's second equation. These comparisons
   are isomorphisms on flat K-flat P and its pullback, so the square determines tau.
   This normalization is an assertion, not a consequence of the definition of tau.
3. The B-transpose of gamma is theta followed by T(epsilon_A). The precise adjunct
   clause of lem-weil-pbc-ring-sheaf-change-adjunction makes the A-transpose of
   d composed with r(gamma) equal to b inverse followed by its restricted transpose.
   Step 2 identifies this with tau followed by epsilon_A tensor id_B, proving the
   transpose equality. No invertibility of a projection map is claimed.
4. Counit naturality, tensor functoriality and naturality of tau give naturality of
   these transposes. The natural Hom equivalence carries it to the naturality equality.
   All steps hold on the ordinary unbounded categories, with no flatness or finite
   Tor dimension of B over A. -/
theorem directImageChangeRingTranspose
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (φ : A →+* B) (N : proEtaleDerivedCategory X.left A) :
    IsDirectImageChangeRingTensorPullbackNormalized φ f.left ∧
    ((proEtaleRingDerivedAdjunction f.left (proEtaleConstantRing Y.left A)
      (proEtaleConstantRing X.left A) (proEtaleConstantRingComparison f.left A)).homEquiv
        _ _).symm (directImageChangeRingRestrictedGamma φ f.left N) =
      (directImageChangeRingTensorPullback φ f.left
        ((proEtaleRingDerivedDirectImage f.left (proEtaleConstantRing Y.left A)
          (proEtaleConstantRing X.left A) (proEtaleConstantRingComparison f.left A)).obj N)).hom ≫
        (scalarExtensionFunctor φ X.left ⋙ scalarRestriction φ X.left).map
          ((proEtaleRingDerivedAdjunction f.left (proEtaleConstantRing Y.left A)
            (proEtaleConstantRing X.left A) (proEtaleConstantRingComparison f.left A)).counit.app
              N) ∧
    ∀ (N' : proEtaleDerivedCategory X.left A) (v : N ⟶ N'),
      (scalarExtensionFunctor φ Y.left ⋙ scalarRestriction φ Y.left).map
          ((proEtaleRingDerivedDirectImage f.left (proEtaleConstantRing Y.left A)
            (proEtaleConstantRing X.left A) (proEtaleConstantRingComparison f.left A)).map v) ≫
        directImageChangeRingRestrictedGamma φ f.left N' =
      directImageChangeRingRestrictedGamma φ f.left N ≫
        (proEtaleRingDerivedDirectImage f.left (proEtaleConstantRing Y.left A)
          (proEtaleConstantRing X.left A) (proEtaleConstantRingComparison f.left A)).map
            ((scalarExtensionFunctor φ X.left ⋙ scalarRestriction φ X.left).map v) := by
  sorry

end AlgebraicGeometry.ProEtale
