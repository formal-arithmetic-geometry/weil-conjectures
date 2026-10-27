/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q24 and Z6
-/
module

public import Sheaf.Paper.ExceptionalRefinementTransportData
public import Sheaf.Paper.ConstructibleExceptionalRefinementMate

/-! # Left refinements and their complete adjunction mate records -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalRefinement
open WeilConjectures.ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

variable {c d : Compactification f}

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The refinement maps on exactly the given operations. The two transpose formulas fix
both directions of the right isomorphism; the ring predicate fixes the open-unit inverse.
The rational and closed formulas include the comparisons on both sides, so they also
apply before identifying the prescribed representatives by their identity normalizations.
Source: blueprint retained steps 20--21
(blueprint: lem-sf-exceptional-refinement-mates). -/
structure Mates (A : Transport.{u, v} l Ω D hl c) (B : Transport.{u, v} l Ω D hl d)
    (r : c.Refinement d) where
  comparison (s : Stage.{max u v} l) :
    RefinementComparison.{u, v} l Ω (A.operation s) (B.operation s)
  normalized (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (A.left s) (B.left s) (comparison (s.stage l))
  transpose (s : Stage.{max u v} l) (L : C.{u, v} l Ω Y s) :
    (comparison s).right.hom.app L =
      (A.operation s).adjunction.homEquiv _ _
        ((comparison s).left.hom.app ((B.operation s).G.obj L) ≫
          (B.operation s).adjunction.counit.app L)
  inverseTranspose (s : Stage.{max u v} l) (L : C.{u, v} l Ω Y s) :
    (comparison s).right.inv.app L =
      (B.operation s).adjunction.homEquiv _ _
        ((comparison s).left.inv.app ((A.operation s).G.obj L) ≫
          (A.operation s).adjunction.counit.app L)
  rationalLeft (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
    (A.localization E).q.inv.app K ≫
        (rationalization.{u, v} l Ω E Y).map ((comparison (.integral E)).left.hom.app K) ≫
        (B.localization E).q.hom.app K =
      (comparison (.rational E)).left.hom.app ((rationalization.{u, v} l Ω E X).obj K)
  rationalRight (E : FieldStage.{max u v} l) (L : C.{u, v} l Ω Y (.integral E)) :
    (B.localization E).b.inv.app L ≫
        (rationalization.{u, v} l Ω E X).map ((comparison (.integral E)).right.hom.app L) ≫
        (A.localization E).b.hom.app L =
      (comparison (.rational E)).right.hom.app ((rationalization.{u, v} l Ω E Y).obj L)
  commonLeft (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω E))) :
    (A.common E).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y E).map
          ((comparison (.rational (commonField.{u, v} l Ω E))).left.hom.app K) ≫
        (B.common E).q.hom.app K =
      (comparison .closed).left.hom.app ((commonInclusion.{u, v} l Ω X E).obj K)
  commonRight (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (L : C.{u, v} l Ω Y (.rational (commonField.{u, v} l Ω E))) :
    (B.common E).b.inv.app L ≫
        (commonInclusion.{u, v} l Ω X E).map
          ((comparison (.rational (commonField.{u, v} l Ω E))).right.hom.app L) ≫
        (A.common E).b.hom.app L =
      (comparison .closed).right.hom.app ((commonInclusion.{u, v} l Ω Y E).obj L)

/-- The geometric left comparisons, without any right-mate or system-realization data.
The ring comparisons use the proper/open unit normalization; the other two equations
retain the prescribed coefficient comparisons. Source: retained refinement steps 1, 3,
4 and 6--8 (blueprint: def-sf-exceptional-refinement-left-data). -/
structure LeftMates (A : Transport.{u, v} l Ω D hl c) (B : Transport.{u, v} l Ω D hl d)
    (r : c.Refinement d) where
  left (s : Stage.{max u v} l) : (A.operation s).F ≅ (B.operation s).F
  leftShift (s : Stage.{max u v} l) : (left s).hom.CommShift ℤ
  normalized (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (A.left s) (B.left s)
      (refinementComparisonOfLeft l Ω (A.operation (s.stage l)) (B.operation (s.stage l))
        (left (s.stage l)) (leftShift (s.stage l)))
  rational (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
    (A.localization E).q.inv.app K ≫
        (rationalization.{u, v} l Ω E Y).map ((left (.integral E)).hom.app K) ≫
        (B.localization E).q.hom.app K =
      (left (.rational E)).hom.app ((rationalization.{u, v} l Ω E X).obj K)
  common (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω E))) :
    (A.common E).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y E).map
          ((left (.rational (commonField.{u, v} l Ω E))).hom.app K) ≫
        (B.common E).q.hom.app K =
      (left .closed).hom.app ((commonInclusion.{u, v} l Ω X E).obj K)


end WeilConjectures.ExceptionalRefinement
