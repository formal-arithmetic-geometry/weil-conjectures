module

public import Sheaf.Paper.SystemCompactSupportData

/-! # Actual semilinear transitions in the constant-coefficient presentation

Source: Zheng Construction 4.1; Stacks 07A6
(blueprint: def-coef-system-compact-support-transitions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.Etale.SystemCompactSupport
open SystemProjection

/-- The actual composite quotient map, including the identity quotient.
Source: Zheng Construction 4.1
(blueprint: def-coef-system-compact-support-transitions). -/
def quotientMap (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) {m n : ℕ} (h : n ≤ m) :=
  (B.map (homOfLE h).op).hom

/-- Transport of the actual strict transition to fixed coefficient modules.
Equality on every local section pins the ordinary map uniquely; it is not an
independently selected derived transition.
Source: Zheng Construction 4.1
(blueprint: def-coef-system-compact-support-transitions). -/
structure TransitionEvaluation (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1})
    (ev : ∀ n : ℕ, Evaluation W B n) where
  ordinary : ∀ {m n : ℕ} (h : n ≤ m), level W B m ⟶
    level W B n ⋙ Sheaf.restrictScalars W.smallEtaleTopology (quotientMap B h)
  sections : ∀ {m n : ℕ} (h : n ≤ m) (M : Modules W B) (U : W.Etaleᵒᵖ)
    (x : M.val.obj (op (m, U.unop))),
    HEq ((((ordinary h).app M).hom.app U) x)
      ((((WeilConjectures.SemilinearSections.transition.{u + 1, u, u + 1}
        W.smallEtaleTopology
        (coefficients W B) (transitions W B) h).app M).val.app U) x)

/-- Exact localization of the actual ordinary transition.
Source: Stacks 05RU, 07A6
(blueprint: def-coef-system-compact-support-transitions). -/
def TransitionEvaluation.derived {W : Scheme.{u}} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {ev : ∀ n : ℕ, Evaluation W B n} (t : TransitionEvaluation W B ev)
    {m n : ℕ} (h : n ≤ m) :
    (ev m).E ⟶ (ev n).E ⋙
      Sheaf.derivedRestrictScalars W.smallEtaleTopology (quotientMap B h) :=
  letI := (ev m).additive
  letI := (ev m).limits
  letI := (ev m).colimits
  letI := (ev n).additive
  letI := (ev n).limits
  letI := (ev n).colimits
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules W B) (.up ℤ)) _ _
    (level W B m).mapDerivedCategory
    ((level W B n ⋙
      Sheaf.restrictScalars W.smallEtaleTopology (quotientMap B h)).mapDerivedCategory)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (t.ordinary h) (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (level W B n)
      (Sheaf.restrictScalars W.smallEtaleTopology (quotientMap B h))).hom

/-- The quotient reduction is the scalar-extension adjunct of the actual transition.
Source: Stacks 07A6 (blueprint: def-coef-system-compact-support-transitions). -/
def TransitionEvaluation.reduction {W : Scheme.{u}}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {ev : ∀ n : ℕ, Evaluation W B n}
    (t : TransitionEvaluation W B ev) {m n : ℕ} (h : n ≤ m) (M : Derived W B) :
    (scalarExtension (quotientMap B h) W).obj ((ev m).E.obj M) ⟶ (ev n).E.obj M :=
  ((Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology (quotientMap B h))).homEquiv
      _ _).symm ((t.derived h).app M)

end AlgebraicGeometry.Etale.SystemCompactSupport
