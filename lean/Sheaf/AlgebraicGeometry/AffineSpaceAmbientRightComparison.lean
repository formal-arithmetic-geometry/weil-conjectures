/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpaceAmbientTower
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.SixFunctors.Etale.Derived.Invertible

/-! # The right functor of the affine-space tower

Source: blueprint cor-amb-affine-space-adjunction, proof steps 3--6.
(blueprint: lem-amb-affine-space-tower-right-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

open MonoidalCategory
open scoped CategoryTheory.Functor

attribute [local instance] Sheaf.monoidalCategory

private noncomputable def derivedTensorRightTensorIso
    (C : Type*) [Category.{u + 1} C] [CategoryTheory.Abelian C]
    [CategoryTheory.IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [CategoryTheory.Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (L M : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    derivedTensorRight C X L ⋙ derivedTensorRight C X M ≅
      derivedTensorRight C X ((derivedTensorRight C X M).obj L) :=
  (tensorRightTensor L M).symm

private noncomputable def derivedSingleTensorIso
    (C : Type*) [Category.{u + 1} C] [CategoryTheory.Abelian C]
    [CategoryTheory.IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [CategoryTheory.Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (L M K : Sheaf X.smallEtaleTopology C)
    (hL : CategoryTheory.Limits.PreservesFiniteLimits (tensorLeft L))
    (e : L ⊗ M ≅ K) :
    (derivedTensorRight C X ((DerivedCategory.singleFunctor _ 0).obj M)).obj
        ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (DerivedCategory.singleFunctor _ 0).obj K :=
  singleFunctorObjTensorIso L M
    ((ObjectProperty.flat_iff_preservesFiniteLimits L).2 hL) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

private noncomputable def derivedRightTensorShiftIso
    (C : Type*) [Category.{u + 1} C] [CategoryTheory.Abelian C]
    [CategoryTheory.IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [CategoryTheory.Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (L M K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (a b c : ℤ) (h : a + b = c)
    (e : (derivedTensorRight C X M).obj L ≅ K) :
    (derivedTensorRight C X (M⟦b⟧)).obj (L⟦a⟧) ≅ K⟦c⟧ :=
  derivedTensorShiftIso C L M a b ≪≫ (shiftFunctor _ _).mapIso e ≪≫
    eqToIso (congrArg (fun n : ℤ ↦ K⟦n⟧) h)

private noncomputable def twistedCompIso
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (g : X ⟶ Y)
    (L : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    ordinaryFiniteTwistedPullback A f L ⋙ ordinaryFiniteTwistedPullback A g M ≅
      ordinaryFiniteTwistedPullback A (g ≫ f)
        ((derivedTensorRight (ModuleCat.{u + 1} A) X M).obj
          ((ordinaryFinitePullback A g).obj L)) :=
  let F := ordinaryFinitePullback A f
  let G := ordinaryFinitePullback A g
  let T := derivedTensorRight (ModuleCat.{u + 1} A) Y L
  let U := derivedTensorRight (ModuleCat.{u + 1} A) X (G.obj L)
  let V := derivedTensorRight (ModuleCat.{u + 1} A) X M
  Functor.associator F T (G ⋙ V) ≪≫
    Functor.isoWhiskerLeft F (Functor.associator T G V).symm ≪≫
    Functor.isoWhiskerLeft F
      (Functor.isoWhiskerRight
        (derivedTensorRightCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) g L) V) ≪≫
    Functor.isoWhiskerLeft F (Functor.associator G U V) ≪≫
    (Functor.associator F G (U ⋙ V)).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g f).symm
      (U ⋙ V) ≪≫
    Functor.isoWhiskerLeft (ordinaryFinitePullback A (g ≫ f))
      (derivedTensorRightTensorIso (ModuleCat.{u + 1} A) X (G.obj L) M)

private noncomputable def twistedThenPullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (g : X ⟶ Y) (L : DerivedCategoryModule A Y) :
    ordinaryFiniteTwistedPullback A f L ⋙ ordinaryFinitePullback A g ≅
      ordinaryFiniteTwistedPullback A (g ≫ f) ((ordinaryFinitePullback A g).obj L) :=
  let F := ordinaryFinitePullback A f
  let G := ordinaryFinitePullback A g
  let T := derivedTensorRight (ModuleCat.{u + 1} A) Y L
  let U := derivedTensorRight (ModuleCat.{u + 1} A) X (G.obj L)
  Functor.associator F T G ≪≫
    Functor.isoWhiskerLeft F
      (derivedTensorRightCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) g L) ≪≫
    (Functor.associator F G U).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g f).symm U

private noncomputable def twistedPairThenPullbackIso
    (A : Type (u + 1)) [CommRing A] {W X Y Z : Scheme.{u}}
    (p : Y ⟶ Z) (q : W ⟶ Y) (j : X ⟶ W) (f : X ⟶ Z)
    (hp : j ≫ (q ≫ p) = f)
    (L : DerivedCategoryModule A Y) (M : DerivedCategoryModule A W)
    (K : DerivedCategoryModule A X)
    (e : (ordinaryFinitePullback A j).obj
      ((derivedTensorRight (ModuleCat.{u + 1} A) W M).obj
        ((ordinaryFinitePullback A q).obj L)) ≅ K) :
    (ordinaryFiniteTwistedPullback A p L ⋙ ordinaryFiniteTwistedPullback A q M) ⋙
        (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ≅
      ordinaryFiniteTwistedPullback A f K :=
  let B := (derivedTensorRight (ModuleCat.{u + 1} A) W M).obj
    ((ordinaryFinitePullback A q).obj L)
  Functor.isoWhiskerRight (twistedCompIso A p q L M)
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (ordinaryFiniteTwistedPullback A (q ≫ p) B)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm ≪≫
    twistedThenPullbackIso A (q ≫ p) j B ≪≫
    Functor.isoWhiskerLeft (ordinaryFinitePullback A (j ≫ (q ≫ p)))
      ((derivedTensorRightFunctor (ModuleCat.{u + 1} A) X).mapIso e) ≪≫
    Functor.isoWhiskerRight (eqToIso (congrArg (ordinaryFinitePullback A) hp)) _

private noncomputable def derivedTensorRightUnitIso
    (C : Type*) [Category.{u + 1} C] [CategoryTheory.Abelian C]
    [CategoryTheory.IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [CategoryTheory.Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) :
    derivedTensorRight C X (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology C))) ≅ 𝟭 _ :=
  rightUnitorNatIso _

private noncomputable def derivedTensorRightSingleUnitIso
    (C : Type*) [Category.{u + 1} C] [CategoryTheory.Abelian C]
    [CategoryTheory.IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [CategoryTheory.Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) :
    derivedTensorRight C X ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology C).obj (𝟙_ C))) ≅ 𝟭 _ :=
  (derivedTensorRightFunctor C X).mapIso (singleFunctorObjUnitIso C X) ≪≫
    derivedTensorRightUnitIso C X

private lemma towerRightZero (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) :
    ambientTowerRight A N hA S 0 =
      (upperStar (ModuleCat.{u + 1} A) (ambientAffine S 0 ↘ S)).mapDerivedCategory :=
  ambientTowerRight_zero A N hA S

private lemma towerRightSucc (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) (r : ℕ) :
    ambientTowerRight A N hA S (r + 1) =
      (ambientTowerRight A N hA S r ⋙ ordinaryFiniteP1Right A N hA (ambientAffine S r)) ⋙
        (upperStar (ModuleCat.{u + 1} A) (ambientSuccessorChart S r)).mapDerivedCategory :=
  ambientTowerRight_succ A N hA S r

-- Use explicit recursion equations to avoid repeatedly reducing the coordinate tower.
-- Recursion is reduced only at the successor being considered.

private noncomputable def ambientTwistComplex
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (r : ℕ) : DerivedCategoryModule A T :=
  (DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateTwist T N A hA r)

private theorem ambientTwistComplex_eq
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (r : ℕ) :
    ambientTwistComplex A N hA T r =
      (DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateTwist T N A hA r) := rfl

private noncomputable def p1RightIso (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) :
    ordinaryFiniteP1Right A N hA T ≅
      ordinaryFiniteTwistedPullback A (ProjectiveLine T ↘ T)
        ((ambientTwistComplex A N hA (ProjectiveLine T) 1)⟦(2 : ℤ)⟧) := Iso.refl _

private theorem tatePullbackIso (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))) (r : ℕ) :
    Nonempty ((upperStar (ModuleCat.{u + 1} A) f).obj
      (Scheme.finiteEtaleTateTwist T N A hA r) ≅
        Scheme.finiteEtaleTateTwist T' N A hA r) := by
  obtain ⟨_, c, _, _⟩ := Scheme.etaleFiniteTwistPullback A N hN hA
  exact ⟨c f hT hT' (r : ℤ)⟩

private theorem tateProductIso (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (r : ℕ) :
    Nonempty (Scheme.finiteEtaleTateTwist T N A hA r ⊗
      Scheme.finiteEtaleTateTwist T N A hA 1 ≅
        Scheme.finiteEtaleTateTwist T N A hA (r + 1)) := by
  obtain ⟨_, _, p, _⟩ := Scheme.etaleFiniteTwistPullback A N hN hA
  exact ⟨p T hT (r : ℤ) 1⟩

private theorem ambientTwistPullbackIso
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T T' : Scheme.{u}) (f : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))) (r : ℕ) (n : ℤ) :
    Nonempty ((ordinaryFinitePullback A f).obj
      ((ambientTwistComplex A N hA T r)⟦n⟧) ≅
        (ambientTwistComplex A N hA T' r)⟦n⟧) := by
  rw [ambientTwistComplex_eq, ambientTwistComplex_eq]
  obtain ⟨c⟩ := tatePullbackIso A N hN hA f hT hT' r
  let : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  exact ⟨((ordinaryFinitePullback A f).commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso c)⟩

private theorem ambientTwistProductIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (r : ℕ) :
    Nonempty ((derivedTensorRight (ModuleCat.{u + 1} A) T
      (ambientTwistComplex A N hA T 1)).obj (ambientTwistComplex A N hA T r) ≅
        ambientTwistComplex A N hA T (r + 1)) := by
  rw [ambientTwistComplex_eq, ambientTwistComplex_eq, ambientTwistComplex_eq]
  have hg : ∀ t : T, IsUnit (N : T.presheaf.stalk t) := by
    intro t
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ t trivial).hom
  obtain ⟨c⟩ := tateProductIso A N hN hA T hT r
  exact ⟨derivedSingleTensorIso (ModuleCat.{u + 1} A) T _ _ _
    (Scheme.finite_etale_torsion_twist_line T N hN hg A hA r).2.2.1 c⟩

private noncomputable def ambientTwistZeroTensorIso
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) :
    derivedTensorRight (ModuleCat.{u + 1} A) T (ambientTwistComplex A N hA T 0) ≅ 𝟭 _ :=
  derivedTensorRightSingleUnitIso (ModuleCat.{u + 1} A) T

attribute [irreducible] ambientTwistComplex

private noncomputable def twistedShiftNormalIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : DerivedCategoryModule A X) (n : ℤ) :
    ordinaryFiniteTwistedPullback A f (L⟦n⟧) ≅
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        derivedTensorRight (ModuleCat.{u + 1} A) X L) ⋙ shiftFunctor _ n :=
  Functor.isoWhiskerLeft (ordinaryFinitePullback A f)
      (derivedTensorRightShiftIso (ModuleCat.{u + 1} A) L n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
        (derivedTensorRight (ModuleCat.{u + 1} A) X L)) (shiftFunctor _ n)

private noncomputable def ambientTwistUnfoldIso
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (r : ℕ) :
    ambientTwistComplex A N hA T r ≅
      (DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateTwist T N A hA r) :=
  eqToIso (ambientTwistComplex_eq A N hA T r)

private theorem twistedCompositeStep
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S T P X : Scheme.{u}} (p : T ⟶ S) (q : P ⟶ T) (j : X ⟶ P) (f : X ⟶ S)
    (hp : j ≫ (q ≫ p) = f)
    (hT : IsUnit (N : Γ(T, ⊤))) (hP : IsUnit (N : Γ(P, ⊤)))
    (hX : IsUnit (N : Γ(X, ⊤))) (r : ℕ) :
    Nonempty ((ordinaryFiniteTwistedPullback A p
        ((ambientTwistComplex A N hA T r)⟦2 * (r : ℤ)⟧) ⋙
      ordinaryFiniteTwistedPullback A q
        ((ambientTwistComplex A N hA P 1)⟦(2 : ℤ)⟧)) ⋙
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ≅
      ordinaryFiniteTwistedPullback A f
        ((ambientTwistComplex A N hA X (r + 1))⟦2 * ((r + 1 : ℕ) : ℤ)⟧)) := by
  classical
  let E : (Y : Scheme.{u}) → ℕ → DerivedCategoryModule A Y := ambientTwistComplex A N hA
  let L : DerivedCategoryModule A T := (E T r)⟦2 * (r : ℤ)⟧
  let M : DerivedCategoryModule A P := (E P 1)⟦(2 : ℤ)⟧
  let B : DerivedCategoryModule A P :=
    (derivedTensorRight (ModuleCat.{u + 1} A) P M).obj
      ((ordinaryFinitePullback A q).obj L)
  have eB : (ordinaryFinitePullback A j).obj B ≅
      (E X (r + 1))⟦2 * ((r + 1 : ℕ) : ℤ)⟧ := by
    refine ordinaryFiniteTensorPullback A j _ _ ≪≫
      ordinaryFiniteTensorRightMapIso A X
        ((ordinaryFinitePullback A j).mapIso
          (Classical.choice (ambientTwistPullbackIso A N hN hA T P q hT hP r _)) ≪≫
          Classical.choice (ambientTwistPullbackIso A N hN hA P X j hP hX r _))
        (Classical.choice (ambientTwistPullbackIso A N hN hA P X j hP hX 1 2)) ≪≫
      derivedRightTensorShiftIso (ModuleCat.{u + 1} A) X (E X r) (E X 1)
        (E X (r + 1)) _ _ _ (by push_cast; ring)
        (Classical.choice (ambientTwistProductIso A N hN hA X hX r))
  exact ⟨twistedPairThenPullbackIso A p q j f hp L M
    ((E X (r + 1))⟦2 * ((r + 1 : ℕ) : ℤ)⟧) eB⟩

private theorem isUnitNatPullback (N : ℕ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (h : IsUnit (N : Γ(Y, ⊤))) : IsUnit (N : Γ(X, ⊤)) := by
  simpa only [map_natCast] using h.map f.appTop.hom

private theorem functorTowerIsoInduction
    {B : Type*} [Category B] (D : ℕ → Type*) [∀ r, Category (D r)]
    (R F : (r : ℕ) → B ⥤ D r) (H : (r : ℕ) → D r ⥤ D (r + 1))
    (e0 : Nonempty (R 0 ≅ F 0))
    (eR : ∀ r, Nonempty (R (r + 1) ≅ R r ⋙ H r))
    (eF : ∀ r, Nonempty (F r ⋙ H r ≅ F (r + 1))) (d : ℕ) :
    Nonempty (R d ≅ F d) := by
  induction d with
  | zero => exact e0
  | succ r ih =>
    obtain ⟨i⟩ := ih
    obtain ⟨a⟩ := eR r
    obtain ⟨b⟩ := eF r
    exact ⟨a ≪≫ Functor.isoWhiskerRight i (H r) ≪≫ b⟩

/-- The reversed projective-line/open tower is exact inverse image, twist, and shift.
Source: blueprint cor-amb-affine-space-adjunction, proof steps 3--6.
(blueprint: lem-amb-affine-space-tower-right-comparison).

Proof: In dimension zero the tower is inverse image by the zero-dimensional affine-space
projection. The zero Tate sheaf is the constant coefficient sheaf, hence the monoidal unit.
The derived single of this flat sheaf is the derived tensor unit. The right unitor and
zero-shift isomorphism identify the displayed right functor with the tower.
For the successor step write j for `ambientSuccessorChart S d`, q for the projective-line
projection and p for the preceding affine-space projection. Expand `ordinaryFiniteP1Right`
as Lq* followed by derived tensor with A(1)[2]. Exactness identifies Lq* with termwise q*.
Use the finite-twist pullback comparison to move A(d)[2d] through q* and then move both
Tate factors through j*. The inverse-image composition comparison and
`ambientSuccessorChart_over` identify the three inverse-image factors with p_(d+1)*.
The finite Tate sheaves are flat: this follows from finite_etale_torsion_twist_line, since
N is a unit on each intermediate scheme by its global-section pullback. Thus the derived
tensor product of their singles agrees naturally with the single of their sheaf tensor
product. For d positive, the defining tensor-power recursion identifies A(d) tensor A(1)
with A(d+1); for d zero use the coefficient-sheaf left unitor. Tensor associativity regroups
the factors. Derived tensor commutes with shift in each variable, and shift composition
adds 2d and 2 to 2(d+1). These maps descend from the degreewise associativity and even-shift
maps on flat complexes, so they are natural on the entire unbounded derived category.
Apply the induction isomorphism and these successor comparisons. No adjunction or trace
identity is used in this comparison. -/
theorem nonempty_ambientTowerRightComparison (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty (ambientTowerRight A N hA S d ≅
      ((upperStar (ModuleCat.{u + 1} A) (ambientAffine S d ↘ S)).mapDerivedCategory ⋙
        derivedTensorRight (ModuleCat.{u + 1} A) (ambientAffine S d)
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist (ambientAffine S d) N A hA d))) ⋙
        shiftFunctor _ (2 * (d : ℤ))) := by
  classical
  let E : (T : Scheme.{u}) → ℕ → DerivedCategoryModule A T :=
    ambientTwistComplex A N hA
  have normal : ∀ r : ℕ, Nonempty (ambientTowerRight A N hA S r ≅
      ordinaryFiniteTwistedPullback A (ambientAffine S r ↘ S)
        ((E (ambientAffine S r) r)⟦2 * (r : ℤ)⟧)) := by
    intro k
    apply functorTowerIsoInduction
      (fun r ↦ DerivedCategoryModule A (ambientAffine S r))
      (fun r ↦ ambientTowerRight A N hA S r)
      (fun r ↦ ordinaryFiniteTwistedPullback A (ambientAffine S r ↘ S)
        ((E (ambientAffine S r) r)⟦2 * (r : ℤ)⟧))
      (fun r ↦ ordinaryFiniteP1Right A N hA (ambientAffine S r) ⋙
        (upperStar (ModuleCat.{u + 1} A) (ambientSuccessorChart S r)).mapDerivedCategory)
    · rw [towerRightZero]
      let T := ambientAffine S 0
      let F := ordinaryFinitePullback A (T ↘ S)
      have e : (E T 0)⟦(2 * ((0 : ℕ) : ℤ))⟧ ≅ E T 0 :=
        (shiftFunctorZero _ ℤ).app _
      refine ⟨(?_ : ordinaryFiniteTwistedPullback A (T ↘ S)
        ((E T 0)⟦2 * ((0 : ℕ) : ℤ)⟧) ≅
          (upperStar (ModuleCat.{u + 1} A) (T ↘ S)).mapDerivedCategory).symm⟩
      exact Functor.isoWhiskerLeft F
          ((derivedTensorRightFunctor (ModuleCat.{u + 1} A) T).mapIso e) ≪≫
        Functor.isoWhiskerLeft F (ambientTwistZeroTensorIso A N hA T) ≪≫
        Functor.rightUnitor F ≪≫
        leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (T ↘ S)
    · intro r
      exact ⟨eqToIso (towerRightSucc A N hA S r) ≪≫
        Functor.associator _ _ _⟩
    · intro r
      let T := ambientAffine S r
      let P := ProjectiveLine T
      let X := ambientAffine S (r + 1)
      let q := (P ↘ T)
      let j := ambientSuccessorChart S r
      let p := (T ↘ S)
      have hT : IsUnit (N : Γ(T, ⊤)) := isUnitNatPullback N p hS
      have hP : IsUnit (N : Γ(P, ⊤)) := isUnitNatPullback N q hT
      have hX : IsUnit (N : Γ(X, ⊤)) := isUnitNatPullback N j hP
      obtain ⟨step⟩ := twistedCompositeStep A N hN hA p q j (X ↘ S)
        (ambientSuccessorChart_over S r) hT hP hX r
      exact ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft
            (ordinaryFiniteTwistedPullback A p ((E T r)⟦2 * (r : ℤ)⟧))
            (p1RightIso A N hA T))
          (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ≪≫ step⟩
  obtain ⟨e⟩ := normal d
  exact ⟨e ≪≫ twistedShiftNormalIso A (ambientAffine S d ↘ S)
    (E (ambientAffine S d) d) (2 * (d : ℤ)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (upperStar (ModuleCat.{u + 1} A) (ambientAffine S d ↘ S)).mapDerivedCategory
        ((derivedTensorRightFunctor (ModuleCat.{u + 1} A) (ambientAffine S d)).mapIso
          (ambientTwistUnfoldIso A N hA (ambientAffine S d) d)))
      (shiftFunctor _ (2 * (d : ℤ)))⟩

end AlgebraicGeometry.Etale
