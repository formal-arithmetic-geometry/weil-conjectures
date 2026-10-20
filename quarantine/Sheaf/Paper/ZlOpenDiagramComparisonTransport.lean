/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.ZlFrameworkPbcOpenComparisonData

/-! # Transport of the specified exchange comparisons along diagram isomorphisms
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrameworkPbc
open PurCompactSupport

section BaseProjections
variable {D : FiniteFieldDatum.{u}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
  {Ω : Type w} [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {S : FdCoefficientComparisonSystem.{u} l Ω} {G : OpenDiagram D l}

/-- The underlying compatible family, projecting away exactness only after elaboration.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def SquarePacket.supportBase (A : SquarePacket D l hl Ω G S) :
    (pbcScalarSystem l Ω G.X G.dimX.out G.invX.out).Morphism
      (pbcScalarSystem l Ω G.Y G.dimY.out G.invY.out) :=
  A.support.family.base

/-- The underlying compatible family, projecting away exactness only after elaboration.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def SquarePacket.supportBase' (A : SquarePacket D l hl Ω G S) :
    (pbcScalarSystem l Ω G.U G.dimU.out G.invU.out).Morphism
      (pbcScalarSystem l Ω G.V G.dimV.out G.invV.out) :=
  A.support'.family.base

/-- The underlying compatible family, projecting away exactness only after elaboration.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def SquarePacket.pullBase (A : SquarePacket D l hl Ω G S) :
    (pbcScalarSystem l Ω G.Y G.dimY.out G.invY.out).Morphism
      (pbcScalarSystem l Ω G.V G.dimV.out G.invV.out) :=
  A.pull.family.base

/-- The underlying compatible family, projecting away exactness only after elaboration.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def SquarePacket.pullBase' (A : SquarePacket D l hl Ω G S) :
    (pbcScalarSystem l Ω G.X G.dimX.out G.invX.out).Morphism
      (pbcScalarSystem l Ω G.U G.dimU.out G.invU.out) :=
  A.pull'.family.base

end BaseProjections

section CompositeEvaluation
universe a b v
variable {J : Type a} [Preorder J] [IsDirectedOrder J]
  {A B C Z : J → Type b}
  [∀ i, Category.{v} (A i)] [∀ i, Category.{v} (B i)]
  [∀ i, Category.{v} (C i)] [∀ i, Category.{v} (Z i)]
  {SA : StageSystem A} {SB : StageSystem B}
  {SC : StageSystem C} {SZ : StageSystem Z}

/-- A compatible composite comparison fixed by specified component maps.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
structure NormalizedCompositeIso
    (F : SA.Morphism SB) (G : SB.Morphism SZ)
    (H : SA.Morphism SC) (I : SC.Morphism SZ)
    {R : ∀ i, A i → Type v} (r : ∀ i K, R i K) where
  comparison : FamilyIso (F.comp G) (H.comp I)
  normalization : ∀ i K, HEq ((comparison.finite i).hom.app K) (r i K)

end CompositeEvaluation

universe z

/-- A dependent bundle keeping the integral and localized comparison data together.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
structure DiagramComparisonBundle
    (IS IP : Type z)
    (SB SB' SA SA' : IS → Type z)
    (PB PB' PA PA' : IP → Type z)
    (normalized : IS → IP → Prop) where
  integralSf : IS
  integralPbc : IP
  sfB : SB integralSf
  sfB' : SB' integralSf
  sfA : SA integralSf
  sfA' : SA' integralSf
  pbcB : PB integralPbc
  pbcB' : PB' integralPbc
  pbcA : PA integralPbc
  pbcA' : PA' integralPbc
  normalization : normalized integralSf integralPbc

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (S : FdCoefficientComparisonSystem.{u} l Ω)
  {G H : OpenDiagram D l} (I : DiagramIso G H)
  (Q : SquarePacket D l hl Ω G S) (R : SquarePacket D l hl Ω H S)
  (T : SquarePacket D l hl Ω I.supportGeometry S)
  (T' : SquarePacket D l hl Ω I.supportGeometry' S)

/-- The actual sf corner pullback, with its corner categories exposed.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def sfCornerX :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω G.X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω H.X) :=
  T.data.sfP'.system

/-- The actual sf corner pullback, with its corner categories exposed.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def sfCornerY :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω G.Y).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω H.Y) :=
  T.data.sfP.system

/-- The actual sf corner pullback, with its corner categories exposed.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def sfCornerU :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω G.U).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω H.U) :=
  T'.data.sfP'.system

/-- The actual sf corner pullback, with its corner categories exposed.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def sfCornerV :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω G.V).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω H.V) :=
  T'.data.sfP.system

/-- The actual pbc corner pullback, with its corner categories exposed.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def pbcCornerX :
    (pbcScalarSystem l Ω G.X G.dimX.out G.invX.out).Morphism
      (pbcScalarSystem l Ω H.X H.dimX.out H.invX.out) :=
  T.pullBase'

/-- The actual pbc corner pullback, with its corner categories exposed.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def pbcCornerY :
    (pbcScalarSystem l Ω G.Y G.dimY.out G.invY.out).Morphism
      (pbcScalarSystem l Ω H.Y H.dimY.out H.invY.out) :=
  T.pullBase

/-- The actual pbc corner pullback, with its corner categories exposed.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def pbcCornerU :
    (pbcScalarSystem l Ω G.U G.dimU.out G.invU.out).Morphism
      (pbcScalarSystem l Ω H.U H.dimU.out H.invU.out) :=
  T'.pullBase'

/-- The actual pbc corner pullback, with its corner categories exposed.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def pbcCornerV :
    (pbcScalarSystem l Ω G.V G.dimV.out G.invV.out).Morphism
      (pbcScalarSystem l Ω H.V H.dimV.out H.invV.out) :=
  T'.pullBase

/-- The naturality comparisons on integral and raw coefficient families. All eight
field families retain their actual mixed beta equations and integral normalizations.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
abbrev DiagramIntegralSf : Type _ := ∀ E, ZlExchange.Comparisons
        (constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) I.x.hom)
        (constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) I.y.hom)
        (constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) I.u.hom)
        (constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) I.v.hom)
        (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) G.c
          (pbcFiniteField.{u} l Ω E))
        (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) G.c'
          (pbcFiniteField.{u} l Ω E))
        (constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) G.v)
        (constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) G.u)
        (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) H.c
          (pbcFiniteField.{u} l Ω E))
        (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) H.c'
          (pbcFiniteField.{u} l Ω E))
        (constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) H.v)
        (constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) H.u)

/-- The integral PBC comparison with the four actual corner pullbacks as its vertices.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
abbrev DiagramIntegralPbc : Type _ := ∀ E, ZlExchange.Comparisons
        (familyIntegralPull l Ω T.pull' E)
        (familyIntegralPull l Ω T.pull E)
        (familyIntegralPull l Ω T'.pull' E)
        (familyIntegralPull l Ω T'.pull E)
        (integralSupport D l Ω G Q.support E)
        (integralSupport' D l Ω G Q.support' E)
        (familyIntegralPull l Ω Q.pull E)
        (familyIntegralPull l Ω Q.pull' E)
        (integralSupport D l Ω H R.support E)
        (integralSupport' D l Ω H R.support' E)
        (familyIntegralPull l Ω R.pull E)
        (familyIntegralPull l Ω R.pull' E)

/-- The specified integralSf_b normalization, named to keep record projection types small.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def diagramCondition_integralSf_b
    (integralSf : DiagramIntegralSf D l hl Ω I) : Prop :=
  ∀ E, HEq ((integralSf E).b.hom)
      ((T.data.integral E).sfExchange)


/-- The specified integralSf_b' normalization, named to keep record projection types small.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def diagramCondition_integralSf_b'
    (integralSf : DiagramIntegralSf D l hl Ω I) : Prop :=
  ∀ E, HEq ((integralSf E).b'.hom)
      ((T'.data.integral E).sfExchange)


/-- The specified integralSf_a normalization, named to keep record projection types small.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def diagramCondition_integralSf_a
    (integralSf : DiagramIntegralSf D l hl Ω I) : Prop :=
  ∀ E, HEq ((integralSf E).a)
      (sfPullSquare l (pbcFiniteField.{u} l Ω E) S.realization
      I.lower)


/-- The specified integralSf_a' normalization, named to keep record projection types small.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def diagramCondition_integralSf_a'
    (integralSf : DiagramIntegralSf D l hl Ω I) : Prop :=
  ∀ E, HEq ((integralSf E).a')
      (sfPullSquare l (pbcFiniteField.{u} l Ω E) S.realization
      I.upper)


/-- The specified integralPbc_b normalization, named to keep record projection types small.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def diagramCondition_integralPbc_b
    (integralPbc : DiagramIntegralPbc D l hl Ω S I Q R T T') : Prop :=
  ∀ E, HEq ((integralPbc E).b.hom)
      ((T.data.integral E).pbcExchange)


/-- The specified integralPbc_b' normalization, named to keep record projection types small.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def diagramCondition_integralPbc_b'
    (integralPbc : DiagramIntegralPbc D l hl Ω S I Q R T T') : Prop :=
  ∀ E, HEq ((integralPbc E).b'.hom)
      ((T'.data.integral E).pbcExchange)


/-- The specified integralPbc_a normalization, named to keep record projection types small.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def diagramCondition_integralPbc_a
    (integralPbc : DiagramIntegralPbc D l hl Ω S I Q R T T') : Prop :=
  ∀ E, HEq ((integralPbc E).a)
      (pbcPullSquare l Ω I.lower Q.pull T'.pull T.pull R.pull E)


/-- The specified integralPbc_a' normalization, named to keep record projection types small.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def diagramCondition_integralPbc_a'
    (integralPbc : DiagramIntegralPbc D l hl Ω S I Q R T T') : Prop :=
  ∀ E, HEq ((integralPbc E).a')
      (pbcPullSquare l Ω I.upper Q.pull' T'.pull' T.pull'
      R.pull' E)


/-- Whole-diagram comparisons retaining integral normalization and mixed beta equations.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
abbrev DiagramComparisons : Type _ :=
  DiagramComparisonBundle
    (DiagramIntegralSf D l hl Ω I)
    (DiagramIntegralPbc D l hl Ω S I Q R T T')
    (fun integralSf ↦ @NormalizedCompositeIso
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Q.data.sfH.system) (sfCornerY D l hl Ω S I T)
      (sfCornerX D l hl Ω S I T) (R.data.sfH.system)
      _ (fun E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω G.X E) ↦
        (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) H.Y).map
          ((integralSf E).b.hom.app K.obj)))
    (fun integralSf ↦ @NormalizedCompositeIso
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Q.data.sfH'.system) (sfCornerV D l hl Ω S I T')
      (sfCornerU D l hl Ω S I T') (R.data.sfH'.system)
      _ (fun E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω G.U E) ↦
        (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) H.V).map
          ((integralSf E).b'.hom.app K.obj)))
    (fun integralSf ↦ @NormalizedCompositeIso
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Q.data.sfP.system) (sfCornerV D l hl Ω S I T')
      (sfCornerY D l hl Ω S I T) (R.data.sfP.system)
      _ (fun E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω G.Y E) ↦
        (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) H.V).map
          ((integralSf E).a.hom.app K.obj)))
    (fun integralSf ↦ @NormalizedCompositeIso
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Q.data.sfP'.system) (sfCornerU D l hl Ω S I T')
      (sfCornerX D l hl Ω S I T) (R.data.sfP'.system)
      _ (fun E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω G.X E) ↦
        (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) H.U).map
          ((integralSf E).a'.hom.app K.obj)))
    (fun integralPbc ↦ @NormalizedCompositeIso
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Q.supportBase) (pbcCornerY D l hl Ω S I T)
      (pbcCornerX D l hl Ω S I T) (R.supportBase)
      _ (fun E (K : pbcStageCategory l Ω G.X E) ↦
        (pbcStageLocalization l Ω H.Y E).map
          ((integralPbc E).b.hom.app K.obj)))
    (fun integralPbc ↦ @NormalizedCompositeIso
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Q.supportBase') (pbcCornerV D l hl Ω S I T')
      (pbcCornerU D l hl Ω S I T') (R.supportBase')
      _ (fun E (K : pbcStageCategory l Ω G.U E) ↦
        (pbcStageLocalization l Ω H.V E).map
          ((integralPbc E).b'.hom.app K.obj)))
    (fun integralPbc ↦ @NormalizedCompositeIso
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Q.pullBase) (pbcCornerV D l hl Ω S I T')
      (pbcCornerY D l hl Ω S I T) (R.pullBase)
      _ (fun E (K : pbcStageCategory l Ω G.Y E) ↦
        (pbcStageLocalization l Ω H.V E).map
          ((integralPbc E).a.hom.app K.obj)))
    (fun integralPbc ↦ @NormalizedCompositeIso
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Q.pullBase') (pbcCornerU D l hl Ω S I T')
      (pbcCornerX D l hl Ω S I T) (R.pullBase')
      _ (fun E (K : pbcStageCategory l Ω G.X E) ↦
        (pbcStageLocalization l Ω H.U E).map
          ((integralPbc E).a'.hom.app K.obj)))
    (fun integralSf integralPbc ↦
      diagramCondition_integralSf_b (D := D) (l := l) (hl := hl) (Ω := Ω)
        (S := S) (I := I) (T := T) (integralSf := integralSf) ∧
      diagramCondition_integralSf_b' (D := D) (l := l) (hl := hl) (Ω := Ω)
        (S := S) (I := I) (T' := T') (integralSf := integralSf) ∧
      diagramCondition_integralSf_a (D := D) (l := l) (hl := hl) (Ω := Ω)
        (S := S) (I := I) (integralSf := integralSf) ∧
      diagramCondition_integralSf_a' (D := D) (l := l) (hl := hl) (Ω := Ω)
        (S := S) (I := I) (integralSf := integralSf) ∧
      diagramCondition_integralPbc_b (D := D) (l := l) (hl := hl) (Ω := Ω)
        (S := S) (I := I) (Q := Q) (R := R) (T := T) (T' := T')
        (integralPbc := integralPbc) ∧
      diagramCondition_integralPbc_b' (D := D) (l := l) (hl := hl) (Ω := Ω)
        (S := S) (I := I) (Q := Q) (R := R) (T := T) (T' := T')
        (integralPbc := integralPbc) ∧
      diagramCondition_integralPbc_a (D := D) (l := l) (hl := hl) (Ω := Ω)
        (S := S) (I := I) (Q := Q) (R := R) (T := T) (T' := T')
        (integralPbc := integralPbc) ∧
      diagramCondition_integralPbc_a' (D := D) (l := l) (hl := hl) (Ω := Ω)
        (S := S) (I := I) (Q := Q) (R := R) (T := T) (T' := T')
        (integralPbc := integralPbc))

variable {D l hl Ω S I Q R T T'}

/-- The finite-stage diagram transport uses the specified coefficient associators.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def DiagramComparisons.finiteSf
    (N : DiagramComparisons D l hl Ω S I Q R T T') (E : Padic.FiniteCoefficientFields l Ω) :
    ZlExchange.Comparisons
      ((sfCornerX D l hl Ω S I T).Φ E)
      ((sfCornerY D l hl Ω S I T).Φ E)
      ((sfCornerU D l hl Ω S I T').Φ E)
      ((sfCornerV D l hl Ω S I T').Φ E)
      (Q.data.sfH.system.Φ E)
      (Q.data.sfH'.system.Φ E)
      (Q.data.sfP.system.Φ E)
      (Q.data.sfP'.system.Φ E)
      (R.data.sfH.system.Φ E)
      (R.data.sfH'.system.Φ E)
      (R.data.sfP.system.Φ E)
      (R.data.sfP'.system.Φ E) where
  b := N.sfB.comparison.finite E
  b' := N.sfB'.comparison.finite E
  a := N.sfA.comparison.finite E
  a' := N.sfA'.comparison.finite E

/-- The finite-stage diagram transport uses the specified coefficient associators.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def DiagramComparisons.finitePbc
    (N : DiagramComparisons D l hl Ω S I Q R T T') (E : Padic.FiniteCoefficientFields l Ω) :
    ZlExchange.Comparisons
      ((pbcCornerX D l hl Ω S I T).Φ E)
      ((pbcCornerY D l hl Ω S I T).Φ E)
      ((pbcCornerU D l hl Ω S I T').Φ E)
      ((pbcCornerV D l hl Ω S I T').Φ E)
      (Q.supportBase.Φ E)
      (Q.supportBase'.Φ E)
      (Q.pullBase.Φ E)
      (Q.pullBase'.Φ E)
      (R.supportBase.Φ E)
      (R.supportBase'.Φ E)
      (R.pullBase.Φ E)
      (R.pullBase'.Φ E) where
  b := N.pbcB.comparison.finite E
  b' := N.pbcB'.comparison.finite E
  a := N.pbcA.comparison.finite E
  a' := N.pbcA'.comparison.finite E

/-- The pair-stage diagram transport uses the specified coefficient associators.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def DiagramComparisons.pairSf
    (N : DiagramComparisons D l hl Ω S I Q R T T') :
    ZlExchange.Comparisons
      ((sfCornerX D l hl Ω S I T).functor)
      ((sfCornerY D l hl Ω S I T).functor)
      ((sfCornerU D l hl Ω S I T').functor)
      ((sfCornerV D l hl Ω S I T').functor)
      (Q.data.sfH.system.functor)
      (Q.data.sfH'.system.functor)
      (Q.data.sfP.system.functor)
      (Q.data.sfP'.system.functor)
      (R.data.sfH.system.functor)
      (R.data.sfH'.system.functor)
      (R.data.sfP.system.functor)
      (R.data.sfP'.system.functor) where
  b := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ N.sfB.comparison.pair ≪≫
      StageSystem.Morphism.functorCompIso _ _
  b' := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ N.sfB'.comparison.pair ≪≫
      StageSystem.Morphism.functorCompIso _ _
  a := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ N.sfA.comparison.pair ≪≫
      StageSystem.Morphism.functorCompIso _ _
  a' := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ N.sfA'.comparison.pair ≪≫
      StageSystem.Morphism.functorCompIso _ _

/-- The pair-stage diagram transport uses the specified coefficient associators.
Source: thm-cbc-qbar.proof.md, naturality of ordered mates
(blueprint: def-zl-open-diagram-comparison-transport). -/
def DiagramComparisons.pairPbc
    (N : DiagramComparisons D l hl Ω S I Q R T T') :
    ZlExchange.Comparisons
      ((pbcCornerX D l hl Ω S I T).functor)
      ((pbcCornerY D l hl Ω S I T).functor)
      ((pbcCornerU D l hl Ω S I T').functor)
      ((pbcCornerV D l hl Ω S I T').functor)
      (Q.supportBase.functor)
      (Q.supportBase'.functor)
      (Q.pullBase.functor)
      (Q.pullBase'.functor)
      (R.supportBase.functor)
      (R.supportBase'.functor)
      (R.pullBase.functor)
      (R.pullBase'.functor) where
  b := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ N.pbcB.comparison.pair ≪≫
      StageSystem.Morphism.functorCompIso _ _
  b' := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ N.pbcB'.comparison.pair ≪≫
      StageSystem.Morphism.functorCompIso _ _
  a := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ N.pbcA.comparison.pair ≪≫
      StageSystem.Morphism.functorCompIso _ _
  a' := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ N.pbcA'.comparison.pair ≪≫
      StageSystem.Morphism.functorCompIso _ _

end WeilConjectures.ZlFrameworkPbc
