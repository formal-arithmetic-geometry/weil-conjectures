/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.HomologySequence
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.UpperStarExact

/-!
# Properties of the direct image with compact support of Weil complexes

This file collects the properties of `Rf₀!` on Weil complexes used in the Deligne–Laumon
reductions.

- `Rf₀!` of a Weil sheaf has no cohomology in negative degrees
  (`AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg`): it is computed
  as `Rḡ_*` of the extension by zero along a compactification, a right derived functor.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

section

variable (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- The direct image with compact support of Weil complexes is the functor attached to the
chosen compactification on the derived categories of pro-étale Weil sheaves. -/
noncomputable def WeilComplex.derivedLowerShriekCompιIso :
    WeilComplex.derivedLowerShriek k₀ l f ⋙ (WeilComplex.objectProperty k₀ l Y).ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f
        (HasCompactification.compactification f
          (hf := hasCompactification_of_over (k₀ := k₀) f)) := by
  unfold WeilComplex.derivedLowerShriek
  exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

attribute [local instance] Compactification.over in
/-- The direct image with compact support of a Weil sheaf has no cohomology in negative
degrees: `Rf₀! = Rḡ_* ∘ ī_!` for a compactification, and `ī_!` is exact while `Rḡ_*` is a right
derived functor. -/
theorem WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg (F : WeilSheaf k₀ l X) {a : ℤ}
    (ha : a < 0) :
    IsZero ((WeilComplex.homologySheaf a).obj
      ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F))) := by
  let c := HasCompactification.compactification f
    (hf := hasCompactification_of_over (k₀ := k₀) f)
  let e : ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F)).obj ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj F.obj)) :=
    (WeilComplex.derivedLowerShriekCompιIso f).app _ ≪≫
      (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).mapIso
        (WeilSheaf.toComplexCompιIso.app F) ≪≫
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
        (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor 0).app F.obj)
  have := (ProEtaleWeilSheaf.lowerStar k₀ l c.g).isGE_rightDerivedFunctor_obj_singleFunctor
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj F.obj)
  have : ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F)).obj.IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  exact WeilComplex.isZero_homologySheaf_obj (DerivedCategory.isZero_of_isGE _ 0 a ha)

end

end AlgebraicGeometry
