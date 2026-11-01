/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.WeilSheaf.LisseRealization.LisseRationalRealizationData
public import WeilConjectures.WeilSheaf.LocalFrobeniusLarge.LocalFrobeniusLargeScalarTower
import WeilConjectures.CategoryTheory.StageSystem.Const

/-! # Local Frobenius with a larger coefficient closure

Source: Deligne, Weil II (1.1.7)--(1.1.10); Bhatt--Scholze, Proposition 6.8.4
and Remark 6.8.15 (blueprint: def-weil-local-frobenius-trace).

The finite-stage constructions are imported unchanged. This interface takes degree-zero
cohomology before extending to a larger coefficient closure. Thus the scheme universe
is independent of the size of that closure. All common-stage maps are fixed by their
finite-stage representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ w w' z z'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.LocalFrobeniusLarge
open AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

attribute [local irreducible] pointRationalFibre pointRationalFibreScalarIso
  DerivedCategory.fieldDerivedHomologyIso

attribute [local instance 3000] Field.toCommRing

attribute [local irreducible] stageScalar scalarCohomology
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The common-stage point functor is uniquely specified on objects and every representative.
Source: Weil II (1.1.1)d); blueprint common-stage fibre
(blueprint: def-weil-local-frobenius-trace).
Proof: on a pair use stageFibre. Send a representative to its finite-stage fibre map,
conjugated by the two stageScalar comparisons. Tensor flattening obeys the identity
and tower laws. The normalized sections comparisons obey those same laws, so further
extension does not change this formula. It therefore descends to the Hom quotient.
The middle scalar comparisons cancel in a composite; every arrow has a representative,
which also proves uniqueness. -/
theorem pointFibre_existsUnique :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) ⥤
        ModuleCat.{u + 1} Ω,
      (∀ N, F.obj N = (stageFibre D l hl Ω N.stage).obj N.obj) ∧
      (∀ (N M : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
        (L : Padic.FiniteCoefficientFields l Ω) (hN : N.stage ≤ L) (hM : M.stage ≤ L)
        (f : N.toStage hN ⟶ M.toStage hM),
        HEq (F.map (StageSystem.PairCategory.mkHom L hN hM f))
          ((stageScalar D l hl Ω hN).inv.app N.obj ≫
            (stageFibre D l hl Ω L).map f ≫ (stageScalar D l hl Ω hM).hom.app M.obj)) := by
  let F := StageSystem.descFunctor (stageFibre D l hl Ω)
    (fun {_ _} h ↦ stageScalar D l hl Ω h) (stageScalar_tower D l hl Ω)
  refine ⟨F, ⟨fun N ↦ rfl, ?_⟩, ?_⟩
  · intro N M L hN hM f
    exact HEq.rfl
  · intro G hG
    apply Functor.hext hG.1
    intro N M f
    induction f using StageSystem.PairCategory.hom_induction with
    | h L hN hM f => exact hG.2 N M L hN hM f

attribute [local semireducible] pointRationalFibre pointRationalFibreScalarIso
  DerivedCategory.fieldDerivedHomologyIso scalarCohomology

/-- The canonical functor with its literal finite-stage object function.
Source: blueprint point-fibre convention (blueprint: def-weil-local-frobenius-trace). -/
def pointFibre : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) ⥤
    ModuleCat.{u + 1} Ω :=
  (pointFibre_existsUnique D l hl Ω).exists.choose.copyObj
    (fun N ↦ (stageFibre D l hl Ω N.stage).obj N.obj)
    (fun N ↦ eqToIso ((pointFibre_existsUnique D l hl Ω).exists.choose_spec.1 N))

/-- The common-stage pullback has exactly its prescribed finite-stage object.
Source: blueprint pullback convention (blueprint: def-weil-local-frobenius-trace). -/
def pullbackStage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω f).obj K ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).obj
        ((rationalDerivedPullback l (Coefficient.{u} l Ω K.stage) f).obj K.obj) :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 K)

/-- The prescribed composition map, with no identification of scheme and coefficient sizes.
Source: blueprint composition convention (blueprint: def-weil-local-frobenius-trace). -/
def composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    (commonStageDerivedPullback l Ω (f ≫ g)).obj K ≅
      (commonStageDerivedPullback l Ω f).obj ((commonStageDerivedPullback l Ω g).obj K) :=
  pullbackStage l Ω (f ≫ g) K ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso
      (localPullbackComposition l (Coefficient.{u} l Ω K.stage) f g K.obj) ≪≫
    (pullbackStage l Ω f
      ((GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).obj
        ((rationalDerivedPullback l (Coefficient.{u} l Ω K.stage) g).obj K.obj))).symm ≪≫
    (commonStageDerivedPullback l Ω f).mapIso (pullbackStage l Ω g K).symm

/-- One restriction-and-coprojection transport, extended from the actual finite stage.
Source: blueprint point transport (blueprint: def-weil-local-frobenius-trace). -/
def transport (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    (pointFibre D l hl Ω).obj N ⟶
      (pointFibre D l hl Ω).obj
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _ (frobeniusPointIso D).hom
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N) :=
  (ModuleCat.extendScalars (embedding l Ω N.stage)).map
    ((DerivedCategory.coefficientFdCohomology (Coefficient.{u} l Ω N.stage) 0).map
      (localPointTransport l (Coefficient.{u} l Ω N.stage) D hl N.obj)) ≫
    (pointFibre D l hl Ω).map
      (@pullbackStage l _ Ω _ _ _ _ _ (frobeniusPointIso D).hom
        (frobeniusPointPrimeInvertible D l hl)
        (frobeniusPointPrimeInvertible D l hl) N).inv

/-- The iterated point transport, with index n denoting exponent n+1.
Source: blueprint I^[n] (blueprint: def-weil-local-frobenius-trace). -/
def transportIterate
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    (n : ℕ) → (pointFibre D l hl Ω).obj N ⟶
      (pointFibre D l hl Ω).obj
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (localPositivePower (frobeniusPointIso D).hom n)
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N)
  | 0 => transport D l hl Ω N
  | n + 1 =>
    letI := frobeniusPointPrimeInvertible D l hl
    transport D l hl Ω N ≫
      transportIterate ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj N) n ≫
      (pointFibre D l hl Ω).map
        (composition l Ω (localPositivePower (frobeniusPointIso D).hom n)
          (frobeniusPointIso D).hom N).inv

variable (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Derived stalk, evaluated by the normalized finite-stage point fibre.
Source: blueprint geometric stalk (blueprint: def-weil-local-frobenius-trace). -/
def stalk (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left ⥤
      ModuleCat.{u + 1} Ω :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ x
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀) ⋙
      pointFibre D l hl Ω

/-- The actual iterated Weil isomorphism, with index n denoting exponent n+1.
Source: blueprint theta^[n] (blueprint: def-weil-local-frobenius-trace). -/
def weilIterate (K : sfCommonStageWeilComplex D l hl Y₀ Ω) :
    (n : ℕ) →
    (@commonStageDerivedPullback l _ Ω _ _ _ _ _
      (localPositivePower (D.geometricFrobenius Y₀).hom n)
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K.carrier ≅
      K.carrier
  | 0 => K.str
  | n + 1 =>
    letI := sfWeilPrimeInvertible D l hl Y₀
    composition l Ω (localPositivePower (D.geometricFrobenius Y₀).hom n)
      (D.geometricFrobenius Y₀).hom K.carrier ≪≫
      (commonStageDerivedPullback l Ω
        (localPositivePower (D.geometricFrobenius Y₀).hom n)).mapIso K.str ≪≫
      weilIterate K n

/-- The middle factor uses the semilinear return equality.
Source: blueprint return comparison (blueprint: def-weil-local-frobenius-trace). -/
def returnComparison (K : generalAlgebraicallyClosedConstructibleCategory l Ω
    (D.geometricFiber Y₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (composition l Ω (localPositivePower (frobeniusPointIso D).hom n) x K).symm ≪≫
    eqToIso (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj K) h.symm) ≪≫
    composition l Ω x (localPositivePower (D.geometricFrobenius Y₀).hom n) K

/-- The normalized local operator: point transport, return comparison, then the Weil map.
Source: Weil II (1.1.7)--(1.1.10) (blueprint: def-weil-local-frobenius-trace). -/
def operator (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x) :
    (stalk D l hl Ω Y₀ x).obj K.carrier ⟶ (stalk D l hl Ω Y₀ x).obj K.carrier :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  transportIterate D l hl Ω
    ((commonStageDerivedPullback l Ω x).obj K.carrier) n ≫
    (pointFibre D l hl Ω).map (returnComparison D l hl Ω Y₀ K.carrier x n h).hom ≫
    (stalk D l hl Ω Y₀ x).map (weilIterate D l hl Ω Y₀ K n).hom

end WeilConjectures.LocalFrobeniusLarge
