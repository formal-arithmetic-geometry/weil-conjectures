/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.CompactProjectionComparison
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionChangeCompactification

/-! # The compact projection square for the geometric category's chosen compactification -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

local notation "fb" => geometricFiberHom (k₀ := k₀) f
local notation "cb" => geometricFiberHomCompactification (k₀ := k₀) f

/-- The forget comparison, transported to the geometric category's chosen compactification. -/
def projectionCompactForgetIso :
    compactProjectionForget k₀ l X ⋙ CondensedRing.boundedConstructibleLowerShriek l fb ≅
      derivedLowerShriek k₀ l f ⋙ compactProjectionForget k₀ l Y :=
  Functor.isoWhiskerLeft (compactProjectionForget k₀ l X)
    (CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl
      (f := fb) l (CondensedRing.compactificationOverField fb) cb) ≪≫
      (projectionCompactificationForgetIso k₀ l f).symm

/-- Its mate under arbitrary Weil exceptional adjunctions is invertible. -/
theorem isIso_mateEquiv_projectionCompactForgetIso
    {R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l f ⊣ R) :
    IsIso (mateEquiv adj (CondensedRing.boundedConstructibleUpperShriekAdjunction l fb)
      (projectionCompactForgetIso k₀ l f).hom).natTrans := by
  have := isIso_mateEquiv_projectionCompactificationForgetIso k₀ l f adj
  exact isIso_mateEquiv_whiskerLeftIso adj
    (CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction l cb)
    (CondensedRing.boundedConstructibleUpperShriekAdjunction l fb)
    (CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl
      (f := fb) l (CondensedRing.compactificationOverField fb) cb)
    (projectionCompactificationForgetIso k₀ l f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The normalized compact projection lies over the geometric exceptional projection. -/
theorem projectionCompact_forget_square (M : WeilComplex k₀ l X) (N : WeilComplex k₀ l Y) :
    (compactProjectionForget k₀ l Y).map ((projectionCompactIso k₀ l f).hom.app (M, N)) ≫
        (projectionCompactForgetIso k₀ l f).inv.app _ ≫
        (CondensedRing.boundedConstructibleLowerShriek l fb).map
          ((compactProjectionForgetTensorIso k₀ l X).hom.app (M, (upperStar f).obj N) ≫
            (compactProjectionForget k₀ l X).obj M ◁
              (projectionCompactPullForgetIso k₀ l f).hom.app N) =
      (compactProjectionForgetTensorIso k₀ l Y).hom.app ((derivedLowerShriek k₀ l f).obj M, N) ≫
        (projectionCompactForgetIso k₀ l f).inv.app M ▷
          (compactProjectionForget k₀ l Y).obj N ≫
        CondensedRing.boundedConstructibleExceptionalProjectionMorphism l fb _ _ := by
  let η : CondensedRing.boundedConstructibleLowerShriek l fb ≅
      CondensedRing.boundedConstructibleLowerShriekOfCompactification l cb :=
    CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl
      (f := fb) l (CondensedRing.compactificationOverField fb) cb
  let t := (compactProjectionForgetTensorIso k₀ l X).hom.app (M, (upperStar f).obj N) ≫
    (compactProjectionForget k₀ l X).obj M ◁ (projectionCompactPullForgetIso k₀ l f).hom.app N
  have hη := CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom_app_whiskerRight_comp
    (f := fb) l (CondensedRing.compactificationOverField fb) cb
      ((compactProjectionForget k₀ l X).obj M) ((compactProjectionForget k₀ l Y).obj N)
  exact projectionForgetSquare_changeGeometricPush η
    ((compactProjectionForget k₀ l Y).map ((projectionCompactIso k₀ l f).hom.app (M, N)))
    ((projectionCompactificationForgetIso k₀ l f).hom.app _)
    ((compactProjectionForgetTensorIso k₀ l Y).hom.app ((derivedLowerShriek k₀ l f).obj M, N))
    ((projectionCompactificationForgetIso k₀ l f).hom.app M)
    ((projectionCompactForgetIso k₀ l f).inv.app _)
    ((projectionCompactForgetIso k₀ l f).inv.app M) t _ _ rfl rfl hη
    (projectionCompactification_forget_square k₀ l f M N)

end AlgebraicGeometry.WeilComplex
