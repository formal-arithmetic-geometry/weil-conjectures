module

public import Sheaf.Paper.ConstantComplexQuotientModel
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison

/-! # Strict constant-complex base change

Source: Stacks Project, Tags 03EL, 03EK, 015F, 014E and 08TC.
(blueprint: def-a1-constant-complex-base-change-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
attribute [-instance] AlgebraicGeometry.Scheme.coefficientProEtaleModelBaseChange_isContinuous
  WeilConjectures.integralOperationsSiteSmall WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify
namespace AlgebraicGeometry.ConstantComplexBaseChange

/-- The recorded Roos differential arrow for the actual reduction tower.
Source: Stacks 08TC (blueprint: lem-a1-constant-complex-strict-base-change). -/
def ReductionData.roosArrow (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} (e : ReductionData W I d) (P : ScalarComplex R) :=
  towerTransitionEndomorphism (K := fun n ↦ ((e.tower W I).obj P).obj (op n))
    (fun n ↦ ((e.tower W I).obj P).map (homOfLE (Nat.le_succ n)).op)

/-- The normalized augmentation has zero shifted-product component and the prescribed
product projection. Its type requires an actual chain map to the recorded strict Roos cone.
Source: Stacks 014E and 08TC
(blueprint: lem-a1-constant-complex-strict-base-change). -/
structure RoosAugmentation (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} (e : ReductionData W I d) where
  beta : ∀ (P : ScalarComplex R) (_hP : IsBoundedFiniteProjective P),
    (completedComplex W I e.coefficient).obj P ⟶
      WeilConjectures.integralOperationsRoosFunctor.obj ((e.tower W I).obj P)

/-- The generator formulas and coherence equations for this comparison data.
Source: Stacks 03EK, 03EL and 08TC
(blueprint: lem-a1-constant-complex-strict-base-change). -/
def RoosAugmentation.IsNormalized (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} {e : ReductionData W I d} (a : RoosAugmentation W I e) : Prop :=
  (∀ (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P),
    e.productMap W I P hP ≫ e.roosArrow W I P = 0) ∧
  (∀ (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P),
    HEq (a.beta P hP ≫ CochainComplex.mappingCocone.fst
      (e.roosArrow W I P)) (e.productMap W I P hP)) ∧
  (∀ (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P) (r : ℤ),
    (a.beta P hP).f r ≫
      (CochainComplex.mappingCocone.snd
        (e.roosArrow W I P)).v
          r (r + -1) rfl = 0) ∧
  (∀ (P Q : ScalarComplex R)
    (hP : IsBoundedFiniteProjective P) (hQ : IsBoundedFiniteProjective Q) (f : P ⟶ Q),
    (completedComplex W I e.coefficient).map f ≫ a.beta Q hQ =
      a.beta P hP ≫ WeilConjectures.integralOperationsRoosFunctor.map ((e.tower W I).map f))

/-- Pulled finite complexes viewed over the original constant ring on the target.
Source: Stacks 03EL (blueprint: lem-a1-constant-complex-strict-base-change). -/
def pulledFiniteOverScalar {X Y : Scheme.{u}} (g : X ⟶ Y) {R : Type u} [CommRing R]
    (I : Ideal R) (n : ℕ) :=
  finiteComplex Y I n ⋙
    (proEtaleConstantRingPullback (Quotient R I n) g).mapHomologicalComplex (.up ℤ) ⋙
      (restriction X (quotientMap X I n)).mapHomologicalComplex (.up ℤ)

/-- The finite comparison is an isomorphism of strict towers, natural in every scalar
chain map, and normalized by the constant tensor sections. The source transitions are
specified by pulling the actual quotient maps, not by an arbitrary choice of maps.
Source: Stacks 03EL (blueprint: lem-a1-constant-complex-strict-base-change). -/
structure FiniteComparison {X Y : Scheme.{u}} (g : X ⟶ Y) {R : Type u} [CommRing R]
    (I : Ideal R) (dY : FiniteTower Y I) (dX : FiniteTower X I) where
  level : ∀ n : ℕ, finiteComplex Y I n ⋙
    (proEtaleConstantRingPullback (Quotient R I n) g).mapHomologicalComplex (.up ℤ) ≅
      finiteComplex X I n
  pulledStep : ∀ n : ℕ, pulledFiniteOverScalar g I (n + 1) ⟶ pulledFiniteOverScalar g I n
  tower : (Functor.ofOpSequence (X := fun n ↦ pulledFiniteOverScalar g I n)
    pulledStep).flip ≅ dX.scalarTower X I

/-- The generator formulas and coherence equations for this comparison data.
Source: Stacks 03EK, 03EL and 08TC
(blueprint: lem-a1-constant-complex-strict-base-change). -/
def FiniteComparison.IsNormalized {X Y : Scheme.{u}} (g : X ⟶ Y) {R : Type u} [CommRing R]
    (I : Ideal R) {dY : FiniteTower Y I} {dX : FiniteTower X I}
    (e : FiniteComparison g I dY dX) : Prop :=
  (∀ (n : ℕ) (P : ScalarComplex R) (r : ℤ) (V : Y.ProEtᵒᵖ)
    (a : Quotient R I n) (p : P.X r)
    (x : (((finiteComplex Y I n).obj P).X r).val.obj V)
    (y : (((finiteComplex Y I n ⋙
      (proEtaleConstantRingPullback (Quotient R I n) g).mapHomologicalComplex (.up ℤ)).obj
        P).X r).val.obj ((proEtaleBaseChange g).op.obj V)),
    HEq x (finiteSection Y I n (P.X r) V a p) →
    HEq y (pulledSection g (Quotient R I n) (((finiteComplex Y I n).obj P).X r) V x) →
    HEq (((((e.level n).hom.app P).f r).val.app ((proEtaleBaseChange g).op.obj V)) y)
      (finiteSection X I n (P.X r) ((proEtaleBaseChange g).op.obj V) a p)) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (r : ℤ) (V : Y.ProEtᵒᵖ)
    (m : (((finiteComplex Y I (n + 1)).obj P).X r).val.obj V)
    (x : (((pulledFiniteOverScalar g I (n + 1)).obj P).X r).val.obj
      ((proEtaleBaseChange g).op.obj V))
    (y : (((finiteComplex Y I n).obj P).X r).val.obj V),
    HEq x (pulledSection g (Quotient R I (n + 1))
      (((finiteComplex Y I (n + 1)).obj P).X r) V m) →
    HEq y ((((dY.step n).app P).f r).val.app V m) →
    HEq (((((e.pulledStep n).app P).f r).val.app ((proEtaleBaseChange g).op.obj V)) x)
      (pulledSection g (Quotient R I n) (((finiteComplex Y I n).obj P).X r) V y)) ∧
  (∀ (P : ScalarComplex R) (n : ℕ), (e.tower.hom.app P).app (op n) =
    ((restriction X (quotientMap X I n)).mapHomologicalComplex (.up ℤ)).map
      ((e.level n).hom.app P))

/-- The strict comparison localized in the ambient module derived categories. The exact
pullback's recorded factorization is used, so this applies to unbounded scalar complexes.
Source: Stacks 015F (blueprint: lem-a1-constant-complex-strict-base-change). -/
def FiniteComparison.derived {X Y : Scheme.{u}} (g : X ⟶ Y) {R : Type u} [CommRing R]
    (I : Ideal R) {dY : FiniteTower Y I} {dX : FiniteTower X I}
    (e : FiniteComparison g I dY dX) (n : ℕ) (P : ScalarComplex R) :
    (proEtaleConstantRingDerivedPullback (Quotient R I n) g).obj
      (DerivedCategory.Q.obj ((finiteComplex Y I n).obj P)) ≅
        DerivedCategory.Q.obj ((finiteComplex X I n).obj P) :=
  (proEtaleConstantRingPullback (Quotient R I n) g).mapDerivedCategoryFactors.app
    ((finiteComplex Y I n).obj P) ≪≫ DerivedCategory.Q.mapIso ((e.level n).app P)

/-- The map-induced completed module pullback uses extension along c, without requiring
c to be invertible. This is the ordinary functor G in the normalized reduction square.
Source: Stacks 03EL (blueprint: lem-a1-constant-complex-strict-base-change). -/
def completedPullback {X Y : Scheme.{u}} (g : X ⟶ Y) {R : Type u} [CommRing R]
    (I : Ideal R)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (completed Y I) ⟶
      completed X I) :=
  proEtaleModuleInverseImage g (completed Y I) ⋙ extension.{u + 1, u, u + 1} c

/-- Termwise application of the actual completed pullback; additivity is proof data,
not an additional assumption on the scheme morphism or coefficient ring.
Source: Stacks 03EL (blueprint: lem-a1-constant-complex-strict-base-change). -/
def completedPullbackComplex {X Y : Scheme.{u}} (g : X ⟶ Y) {R : Type u} [CommRing R]
    (I : Ideal R)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (completed Y I) ⟶
      completed X I) (h : (completedPullback g I c).Additive) :=
  letI := h
  (completedPullback g I c).mapHomologicalComplex (.up ℤ)

/-- Scalar multiplication on a pulled local section, with its target-ring action explicit.
Source: Stacks 03D2 (blueprint: lem-a1-constant-complex-strict-base-change). -/
def scaledPulledSection {X Y : Scheme.{u}} (g : X ⟶ Y) (A : Type u) [CommRing A]
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (V : Y.ProEtᵒᵖ)
    (a : (proEtaleConstantRing X A).obj.obj ((proEtaleBaseChange g).op.obj V))
    (m : M.val.obj V) :
    ((proEtaleConstantRingPullback A g).obj M).val.obj ((proEtaleBaseChange g).op.obj V) :=
  let N : ModuleCat.{u + 1}
      ((proEtaleConstantRing X A).obj.obj ((proEtaleBaseChange g).op.obj V)) :=
    ((proEtaleConstantRingPullback A g).obj M).val.obj ((proEtaleBaseChange g).op.obj V)
  a • (show N from pulledSection g A M V m)

/-- The actual completed-coefficient map and the normalized geometric reduction square.
Its projection equations determine c uniquely, and its tensor formulas determine the
comparison and the pulled reduction maps. There is no inverse for c in this interface.
Source: Stacks 03EL and 03EK
(blueprint: lem-a1-constant-complex-strict-base-change). -/
structure GeometricReduction {X Y : Scheme.{u}} (g : X ⟶ Y) {R : Type u} [CommRing R]
    (I : Ideal R) {dY : FiniteTower Y I} {dX : FiniteTower X I}
    (eY : ReductionData Y I dY) (eX : ReductionData X I dX)
    (f : FiniteComparison g I dY dX) where
  coefficient : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (completed Y I) ⟶
    completed X I
  additive : (completedPullback g I coefficient).Additive
  comparison : ∀ (P : ScalarComplex R) (_hP : IsBoundedFiniteProjective P),
    (completedPullbackComplex g I coefficient additive).obj
      ((completedComplex Y I eY.coefficient).obj P) ≅
        (completedComplex X I eX.coefficient).obj P
  pulledReduction : ∀ (n : ℕ) (P : ScalarComplex R) (_hP : IsBoundedFiniteProjective P),
    (completedPullbackComplex g I coefficient additive).obj
      ((completedComplex Y I eY.coefficient).obj P) ⟶
        ((restriction X (limit.π (coefficientTower X I) (op n))).mapHomologicalComplex
          (.up ℤ)).obj (((proEtaleConstantRingPullback (Quotient R I n) g).mapHomologicalComplex
            (.up ℤ)).obj ((finiteComplex Y I n).obj P))

/-- The generator formulas and coherence equations for this comparison data.
Source: Stacks 03EK, 03EL and 08TC
(blueprint: lem-a1-constant-complex-strict-base-change). -/
def GeometricReduction.IsNormalized {X Y : Scheme.{u}} (g : X ⟶ Y) {R : Type u} [CommRing R]
    (I : Ideal R) {dY : FiniteTower Y I} {dX : FiniteTower X I}
    {eY : ReductionData Y I dY} {eX : ReductionData X I dX}
    {f : FiniteComparison g I dY dX} (e : GeometricReduction g I eY eX f) : Prop :=
  (∀ n : ℕ,
    e.coefficient ≫ limit.π (coefficientTower X I) (op n) =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (limit.π (coefficientTower Y I) (op n)) ≫
          (proEtaleConstantRingComparison g (Quotient R I n)).hom) ∧
  (∀ (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P)
    (r : ℤ) (V : Y.ProEtᵒᵖ) (b : (completed Y I).obj.obj V)
    (b' : (completed X I).obj.obj ((proEtaleBaseChange g).op.obj V)) (p : P.X r)
    (m : (((completedComplex Y I eY.coefficient).obj P).X r).val.obj V)
    (x : ((proEtaleModuleInverseImage g (completed Y I)).obj
      (((completedComplex Y I eY.coefficient).obj P).X r)).val.obj
        ((proEtaleBaseChange g).op.obj V))
    (y : (((completedPullbackComplex g I e.coefficient e.additive).obj
      ((completedComplex Y I eY.coefficient).obj P)).X r).val.obj
        ((proEtaleBaseChange g).op.obj V)),
    HEq m (tensorSection.{u + 1, u, u + 1} eY.coefficient
      ((constantModules Y R).obj (P.X r)) V b (constantSection Y (P.X r) V p)) →
    HEq x (AlgebraicGeometry.ProEtaleTensorComparison.inverseSection g (R := completed Y I)
      (((completedComplex Y I eY.coefficient).obj P).X r) V.unop m) →
    HEq y (tensorSection.{u + 1, u, u + 1} e.coefficient
      ((proEtaleModuleInverseImage g (completed Y I)).obj
        (((completedComplex Y I eY.coefficient).obj P).X r))
          ((proEtaleBaseChange g).op.obj V) b' x) →
    HEq (((((e.comparison P hP).hom.f r).val.app ((proEtaleBaseChange g).op.obj V)) y))
      (tensorSection.{u + 1, u, u + 1} eX.coefficient
        ((constantModules X R).obj (P.X r)) ((proEtaleBaseChange g).op.obj V)
          (b' * e.coefficient.hom.app ((proEtaleBaseChange g).op.obj V)
            ((((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app
              (completed Y I)).hom.app V) b))
          (constantSection X (P.X r) ((proEtaleBaseChange g).op.obj V) p))) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P)
    (r : ℤ) (V : Y.ProEtᵒᵖ) (b' : (completed X I).obj.obj ((proEtaleBaseChange g).op.obj V))
    (m : (((completedComplex Y I eY.coefficient).obj P).X r).val.obj V)
    (x : ((proEtaleModuleInverseImage g (completed Y I)).obj
      (((completedComplex Y I eY.coefficient).obj P).X r)).val.obj
        ((proEtaleBaseChange g).op.obj V))
    (y : (((completedPullbackComplex g I e.coefficient e.additive).obj
      ((completedComplex Y I eY.coefficient).obj P)).X r).val.obj
        ((proEtaleBaseChange g).op.obj V))
    (z : (((finiteComplex Y I n).obj P).X r).val.obj V),
    HEq x (AlgebraicGeometry.ProEtaleTensorComparison.inverseSection g (R := completed Y I)
      (((completedComplex Y I eY.coefficient).obj P).X r) V.unop m) →
    HEq y (tensorSection.{u + 1, u, u + 1} e.coefficient
      ((proEtaleModuleInverseImage g (completed Y I)).obj
        (((completedComplex Y I eY.coefficient).obj P).X r))
          ((proEtaleBaseChange g).op.obj V) b' x) →
    HEq z (((eY.alpha n P hP).f r).val.app V m) →
    HEq (((((e.pulledReduction n P hP).f r).val.app ((proEtaleBaseChange g).op.obj V)) y))
      (scaledPulledSection g (Quotient R I n) (((finiteComplex Y I n).obj P).X r) V
        (show (proEtaleConstantRing X (Quotient R I n)).obj.obj
          ((proEtaleBaseChange g).op.obj V) from
            (limit.π (coefficientTower X I) (op n)).hom.app
              ((proEtaleBaseChange g).op.obj V) b') z)) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P),
    e.pulledReduction n P hP ≫
      ((restriction X (limit.π (coefficientTower X I) (op n))).mapHomologicalComplex
        (.up ℤ)).map ((f.level n).hom.app P) =
      (e.comparison P hP).hom ≫ eX.alpha n P hP) ∧
  (∀ (P Q : ScalarComplex R)
    (hP : IsBoundedFiniteProjective P) (hQ : IsBoundedFiniteProjective Q) (a : P ⟶ Q),
    (completedPullbackComplex g I e.coefficient e.additive).map
      ((completedComplex Y I eY.coefficient).map a) ≫ (e.comparison Q hQ).hom =
      (e.comparison P hP).hom ≫ (completedComplex X I eX.coefficient).map a)

end AlgebraicGeometry.ConstantComplexBaseChange
