/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.UpperStarId

/-! # Restriction of projective-line cohomology to infinity -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Pull back to the projective line and take ordinary proper direct image. -/
noncomputable abbrev projectiveLineCohomology :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l X :=
  upperStar (ProjectiveLine X ↘ X) ⋙ derivedLowerStar (ProjectiveLine X ↘ X)

/-- Restriction of relative projective-line cohomology to the section at infinity.
(blueprint: def-pur-b3-weil-projective-restriction).
It is constructed from the counit of pullback/direct-image adjunction and the equality
`infinity ≫ projection = identity`; no cohomology calculation enters this definition. -/
noncomputable def projectiveLineRestriction :
    projectiveLineCohomology (k₀ := k₀) (l := l) X ⟶ 𝟭 _ := by
  let q := ProjectiveLine X ↘ X
  let i := ProjectiveLine.infinity X
  letI : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change (i ≫ q) ≫ (X ↘ Spec (CommRingCat.of k₀)) = _
    rw [ProjectiveLine.infinity_over, Category.id_comp]⟩
  let L := upperStar (k₀ := k₀) (l := l) q
  let R := derivedLowerStar (k₀ := k₀) (l := l) q
  let I := upperStar (k₀ := k₀) (l := l) i
  let e : L ⋙ I ≅ 𝟭 _ :=
    (upperStarCompIso i q).symm ≪≫ upperStarCongrIso ProjectiveLine.infinity_over ≪≫
      upperStarIdIso X
  let ε := (upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) q).counit
  exact (Functor.rightUnitor (L ⋙ R)).inv ≫
    Functor.whiskerLeft (L ⋙ R) e.inv ≫
    (Functor.associator L R (L ⋙ I)).hom ≫
    Functor.whiskerLeft L (Functor.associator R L I).inv ≫
    Functor.whiskerLeft L (Functor.whiskerRight ε I) ≫ e.hom

end AlgebraicGeometry.WeilComplex
