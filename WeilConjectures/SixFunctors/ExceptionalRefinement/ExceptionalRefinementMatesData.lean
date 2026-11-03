/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalRefinement.ExceptionalRefinementTransportData
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalRefinementMate

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
      (let q := refinementComparisonOfLeft
          (A.operation (s.stage l)).adjunction (B.operation (s.stage l)).adjunction
          (left (s.stage l)) (leftShift (s.stage l))
          (A.operation (s.stage l)).unitShift (B.operation (s.stage l)).counitShift;
        { left := q.left, right := q.right, counit := q.counit, unit := q.unit,
          leftShift := q.leftShift, rightShift := q.rightShift })
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
