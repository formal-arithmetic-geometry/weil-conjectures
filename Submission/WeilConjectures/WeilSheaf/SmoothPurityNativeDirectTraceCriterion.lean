/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.WeilSheaf.SmoothPurityCondensedCarrier
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityCondensedTraceCriterion

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# A native direct-image trace criterion in condensed coordinates

The free Weil resolution proves universality in the condensed category. Full
faithfulness of the native comparison then proves invertibility of the native
adjoint of the trace.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]

/-- Direct image of native Weil complexes commutes with the condensed equivalence. -/
noncomputable def directTraceCondensedComparison :
    derivedLowerStar (k₀ := k₀) (l := l) f ⋙ (objectProperty k₀ l Y).ι ⋙
        (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor ≅
      (objectProperty k₀ l X).ι ⋙ (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor ⋙
        (CondensedRing.geometricFiberMapWeilLowerStar (Profinite.padicAlgClRingObj l)
          f (comp_over f _)).rightDerivedFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.rightDerivedLowerStarCompToCondensedIso k₀ l f)

end AlgebraicGeometry.WeilComplex
