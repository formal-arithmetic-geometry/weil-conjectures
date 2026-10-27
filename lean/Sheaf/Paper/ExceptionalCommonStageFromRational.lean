/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Paper.ExceptionalRationalStageLocalization

/-! # Common-field descent of fixed rational exceptional operations

Only the closed operations and their inclusion comparisons are outputs. Rational
operations and their scalar maps are fixed inputs. The representative-arrow law is
proved by the consumer from the transition law and naturality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Closed operations descending the supplied rational family, with its transition law.
No rational operation or scalar comparison is chosen again by this record.
Source: Zheng, Construction 6.6; coefficient construction step 5, common-field part
(blueprint: lem-sf-common-stage-descent-fixed-rational). -/
structure CommonStageAssembly
    (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
    (P : RationalStageAssembly.{u, v} l Ω D hl A) where
  operation (c : Compactification f) : Operation.{u, v} l Ω X Y .closed
  comparison (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    CounitFieldComparison.{u, v} l Ω (P.operation c (commonField.{u, v} l Ω i)) (operation c)
      (commonInclusion.{u, v} l Ω X i) (commonInclusion.{u, v} l Ω Y i)
  normalized (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    HEq ((comparison c i).q.hom.app K)
      (𝟙 ((commonInclusion.{u, v} l Ω Y i).obj
        ((P.operation c (commonField.{u, v} l Ω i)).F.obj K)))
  shiftX (c d : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    (comparison c i).shiftX = (comparison d i).shiftX
  shiftY (c d : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    (comparison c i).shiftY = (comparison d i).shiftY
  transition (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (comparison c i).q.hom.app K ≫
        (operation c).F.map ((commonTransition.{u, v} l Ω X i j h).inv.app K) =
      (commonTransition.{u, v} l Ω Y i j h).inv.app
          ((P.operation c (commonField.{u, v} l Ω i)).F.obj K) ≫
        (commonInclusion.{u, v} l Ω Y j).map
          ((P.scalar c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q.hom.app K) ≫
        (comparison c j).q.hom.app
          ((rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X).obj K)

/-- Descend a fixed normalized rational family to the literal common-field pair category.
Only closed operations and inclusion comparisons are constructed here. In particular,
this does not assert the rational-localization existence theorem.
Source: Zheng, Construction 6.6; `lem-sf-field-stage-completion`, step 4
(blueprint: lem-sf-common-stage-descent-fixed-rational).

Proof: use `P.action`, `P.scalar_normalized`, and the residue-Tor equality to identify
all rational scalar comparisons with localizations of the supplied integral comparisons.
The proper/open coefficient projection cocycle and the tensor unit normalization prove
their balanced composition and identity laws; the counit equations give the same laws
for right adjoints by transposition. At each common finite coefficient field take exactly
`P.operation` as stage functor. The published scalar transitions, tensor associators and
unitors form the actual stage systems. Their cocycle gives morphisms of these systems
for both adjoints. Apply coherent-pair functor descent: a pair (E,K) goes to (E,F_E K),
and a representative at a common stage is conjugated by the scalar q comparisons.
This preserves identity, composition and addition, and is unchanged by enlargement.
Descend each stage adjunction Hom bijection and its inverse at one common field. The
mate unit and counit equations make these maps compatible with enlargement. Naturality
and the two triangles hold on representatives, and hence on their quotient Hom groups.
They give the closed adjunction. Descend the stage shift isomorphisms; distinguished
triangles are represented at finite stages, so both closed functors are exact. The
units and counits commute with shifts already at each stage. Choose inclusion shifts
from the endpoint coefficient functors, independently of compactification. The left
inclusion comparison is the identity on the literal pair object, and the right one is
its invertible counit transpose. Finally the quotient functor's formula on an inverse
transition gives the displayed transition equation. No absolute separatedness is used;
identity field extensions use the tensor unit and empty schemes give zero functors. -/
theorem exists_common_stage_descent
    (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
    (P : RationalStageAssembly.{u, v} l Ω D hl A) :
    Nonempty (CommonStageAssembly.{u, v} l Ω D hl A P) := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
