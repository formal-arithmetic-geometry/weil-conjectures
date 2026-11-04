/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeProperDualizing
public import WeilConjectures.WeilSheaf.SmoothPurityNativeDescentPullback

/-!
# Descent of the exceptional unit through a compactification

Proper direct image followed by open restriction describes the exceptional
inverse image. The proper descended trace and the pullback comparison identify
its unit value with native descent of the finite-base dualizing complex.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance] Compactification.over
attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

local instance : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩
local instance : (boundedConstructible (condensedRingObj
    (Profinite.padicAlgClRingObj l) (Spec (CommRingCat.of k₀)))).IsMonoidal :=
  CondensedRing.isMonoidal_boundedConstructible l (CondensedRing.point k₀)
local noncomputable instance : MonoidalCategory (BoundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (CommRingCat.of k₀)))) :=
  ObjectProperty.fullMonoidalSubcategory _
local instance : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))

/-- The exceptional inverse image of the descended unit is native descent of the
finite-base dualizing complex, including the Weil structure. -/
theorem nonempty_shriekRightAdjoint_finiteBaseNativeDescent_dualizing_iso
    {R : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ R) :
    Nonempty (R.obj ((finiteBaseNativeDescent (k₀ := k₀) (l := l)).obj (𝟙_ _)) ≅
      (finiteBaseNativeDescent (k₀ := k₀) (l := l)).obj
        (CondensedRing.dualizingComplex l (Over.mk (X ↘ Spec (CommRingCat.of k₀))))) := by
  let c := structureMorphismCompactification (k₀ := k₀) X
  have : IsProper c.g := c.isProper
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c.g (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiCompact (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c.g (Spec (CommRingCat.of k₀))]
    infer_instance
  have : IsSeparated (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c.g (Spec (CommRingCat.of k₀))]
    infer_instance
  have : IsLocallyNoetherian (Spec (CommRingCat.of k₀)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := inferInstance
  have := isLeftAdjoint_derivedLowerStar_of_isProper' (k₀ := k₀) (l := l) c.g
  let adjg := Adjunction.ofIsLeftAdjoint (derivedLowerStar (k₀ := k₀) (l := l) c.g)
  have e : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ≅
      extensionByZero c.i ⋙ derivedLowerStar c.g :=
    NatIso.ofComponents (fun K ↦ Iso.refl _) (fun φ ↦ by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)
  let eR := adj.rightAdjointUniq
    (((extensionByZeroUpperStarAdjunction c.i).comp adjg).ofNatIsoLeft e.symm)
  obtain ⟨eZ⟩ := nonempty_rightAdjoint_finiteBaseNativeDescent_dualizing_iso c.g adjg
  let Z₀ := Over.mk (c.Z ↘ Spec (CommRingCat.of k₀))
  have : LocallyOfFiniteType Z₀.hom := ‹LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k₀))›
  have : QuasiCompact Z₀.hom := ‹QuasiCompact (c.Z ↘ Spec (CommRingCat.of k₀))›
  have : IsSeparated Z₀.hom := ‹IsSeparated (c.Z ↘ Spec (CommRingCat.of k₀))›
  let j : Over.mk (X ↘ Spec (CommRingCat.of k₀)) ⟶ Z₀ :=
    Over.homMk c.i (comp_over c.i (Spec (CommRingCat.of k₀)))
  have : IsOpenImmersion j.left := ‹IsOpenImmersion c.i›
  have e₀ : (finiteBaseTracePullback (k₀ := k₀) (l := l) c.i).obj
      (CondensedRing.dualizingComplex l Z₀) ≅
      CondensedRing.dualizingComplex l (Over.mk (X ↘ Spec (CommRingCat.of k₀))) :=
    (CondensedRing.dualizingComplexIsoUpperStar l j).symm
  exact ⟨eR.app _ ≪≫ (upperStar c.i).mapIso eZ ≪≫
    finiteBaseNativeDescentUpperStarIso c.i (CondensedRing.dualizingComplex l Z₀) ≪≫
    (finiteBaseNativeDescent (k₀ := k₀) (l := l)).mapIso e₀⟩

end AlgebraicGeometry.WeilComplex
