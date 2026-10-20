/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-! # Monoidal compatibility of degree-zero etale sheaves

Source: Stacks Project, Cohomology, Tags 06YQ and 06YU.
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X X' : AlgebraicGeometry.Scheme.{u}}

/-- The canonical degree-zero derived pairing computed on a flat left factor.
Source: Stacks Tag 06YQ; (blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
This explicit result type uses the same derived tensor bifunctor as its consumers. -/
@[irreducible]
noncomputable def singleFunctorFlatPairing
    (L M N : Sheaf X.smallEtaleTopology B) (hL : ObjectProperty.flat L)
    (f : L ⊗ M ⟶ N) :
    ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
        (DerivedCategory.singleFunctor _ 0).obj N :=
  (singleFunctorObjTensorIso (A := B) (X := X) L M hL).hom ≫
    (DerivedCategory.singleFunctor _ 0).map f

/-- Map a pair of arrows with the specified derived tensor bifunctor.
Source: Stacks Tag 06YU;
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
The coefficient category stays abstract when this composite is checked. -/
noncomputable def derivedTensorPairMap (X : AlgebraicGeometry.Scheme.{u})
    {K K' L L' : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensor B X).obj K).obj L ⟶ ((derivedTensor B X).obj K').obj L' :=
  ((derivedTensor B X).map f).app L ≫ ((derivedTensor B X).obj K').map g

/-- Apply an ordinary pullback arrow after the canonical single/pullback comparison.
Source: Stacks Tag 06YQ;
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
No resolution or inverse-image comparison is chosen here. -/
noncomputable def singleFunctorPullbackMap (v : X' ⟶ X)
    {L : Sheaf X.smallEtaleTopology B} {L' : Sheaf X'.smallEtaleTopology B}
    (f : (upperStar B v).obj L ⟶ L') :
    (upperStar B v).leftDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj L) ⟶
      (DerivedCategory.singleFunctor _ 0).obj L' :=
  (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L ≫
    (DerivedCategory.singleFunctor _ 0).map f

/-- The equations expressing the tensor compatibility of flat degree-zero models.
Source: Stacks Tags 06YQ and 06YU;
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).
The support sheaves and all ordinary multiplication or support maps are arbitrary inputs. -/
structure EtaleFlatSingleTensorCompatibility (v : X' ⟶ X)
    [(upperStar B v).PreservesFlat] : Prop where
  associativity {L M N P Q R T : Sheaf X.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hM : ObjectProperty.flat M)
      (hP : ObjectProperty.flat P)
      (f : L ⊗ M ⟶ P) (g : P ⊗ N ⟶ R) (h : M ⊗ N ⟶ Q)
      (k : L ⊗ Q ⟶ T) (a : R ⟶ T)
      (w : f ▷ N ≫ g ≫ a = (α_ L M N).hom ≫ L ◁ h ≫ k) :
      ((derivedTensor B X).map (singleFunctorFlatPairing L M P hL f)).app
          ((DerivedCategory.singleFunctor _ 0).obj N) ≫
        singleFunctorFlatPairing P N R hP g ≫ (DerivedCategory.singleFunctor _ 0).map a =
      (derivedTensorAssociator B X _ _ _).hom ≫
        ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).map
          (singleFunctorFlatPairing M N Q hM h) ≫ singleFunctorFlatPairing L Q T hL k
  symmetry {L M P Q : Sheaf X.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hM : ObjectProperty.flat M)
      (f : L ⊗ M ⟶ P) (g : M ⊗ L ⟶ Q) (a : Q ⟶ P)
      (w : (β_ L M).hom ≫ g ≫ a = f) :
      (((derivedTensorSymmetry B X).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj L)).app
          ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
        singleFunctorFlatPairing M L Q hM g ≫ (DerivedCategory.singleFunctor _ 0).map a =
          singleFunctorFlatPairing L M P hL f
  pullback {L M N : Sheaf X.smallEtaleTopology B}
      {L' M' N' : Sheaf X'.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hL' : ObjectProperty.flat L')
      (f : L ⊗ M ⟶ N) (g : L' ⊗ M' ⟶ N')
      (b : (upperStar B v).obj L ⟶ L') (c : (upperStar B v).obj M ⟶ M')
      (d : (upperStar B v).obj N ⟶ N')
      (w : (upperStar B v).map f ≫ d =
        Functor.OplaxMonoidal.δ (upperStar B v) L M ≫ (b ⊗ₘ c) ≫ g) :
      (upperStar B v).leftDerivedFunctor.map (singleFunctorFlatPairing L M N hL f) ≫
          (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app N ≫
            (DerivedCategory.singleFunctor _ 0).map d =
        ((leftDerivedUpperStarTensorComparison B v).app
            ((DerivedCategory.singleFunctor _ 0).obj L)).app
            ((DerivedCategory.singleFunctor _ 0).obj M) ≫
          ((derivedTensor B X').map
            ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L ≫
              (DerivedCategory.singleFunctor _ 0).map b)).app _ ≫
          ((derivedTensor B X').obj _).map
            ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app M ≫
              (DerivedCategory.singleFunctor _ 0).map c) ≫
          singleFunctorFlatPairing L' M' N' hL' g

/-- Canonical flat degree-zero pairings preserve associativity, symmetry and exact pullback.

Source: Stacks Project, Cohomology, Tags 06YQ and 06YU; the canonical tensor/counit
comparisons in `Derived.Invertible` and `Derived.UpperStarMonoidal.Comparison`.
(blueprint: lem-pur-etale-single-functor-monoidal-compatibility).

Proof: the degree-zero cochain functor has the single/total-tensor comparison as its
tensorator and the identity unit comparison. Naturality, associativity, units and braiding
are checked on the sole nonzero summand in bidegree (0,0), respectively tridegree (0,0,0).
Every other summand has a zero factor, and the Koszul sign on this summand is one.
Compose with the strong braided homotopy quotient and lax braided localization Qh.
The single/quotient comparison is the identity on objects and maps; its flat tensorator
expands to exactly singleFunctorObjTensorIso.hom. The ordinary associativity or symmetry
equality, functoriality and the corresponding lax braided coherence equation therefore
give the first two fields for arbitrary pairings.
For inverse image, the single/termwise-exact-functor comparison respects the same
nonzero tensor summand and the unit. The tensor/counit equation for derived inverse
image shows that its derived counit is monoidal, after cancelling the invertible oplax
tensorators. Whisker the monoidal comparisons and identify their composite with
singleFunctorCompLeftDerivedUpperStarIso.hom by the exact-functor counit factorization.
Its tensor equation, naturality, and the ordinary pullback square imply the final field.
All flat factors used in these computations are among the explicit flatness hypotheses;
no flatness of arbitrary sheaves or of the right-hand factor is required. The argument
also applies to zero objects, zero pairings and empty schemes. -/
theorem etaleSingleFunctor_monoidalCompatibility
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X X' : AlgebraicGeometry.Scheme.{u}} (v : X' ⟶ X)
    [(upperStar B v).PreservesFlat] :
    EtaleFlatSingleTensorCompatibility (B := B) v := by
  sorry

end AlgebraicGeometry.Etale
