/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.CompactProjectionIso
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionPasting

/-! # Canonical open and proper projection isomorphisms on Weil complexes -/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]

/-- The canonical proper projection isomorphism restricted to Weil complexes. -/
def nativeBoundedProperProjectionIso [IsProper f] :
    (derivedLowerStar f).prod (𝟭 _) ⋙ nativeConstructibleTensor k₀ l Y ≅
      (𝟭 _).prod (upperStar f) ⋙ nativeConstructibleTensor k₀ l X ⋙ derivedLowerStar f :=
  ((objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso
    (rightDerivedLowerStarNativeDerivedTensorIso f)

/-- The canonical open projection isomorphism restricted to Weil complexes. -/
def nativeBoundedOpenProjectionIso [IsOpenImmersion f] [QuasiCompact f] :
    (extensionByZero f).prod (𝟭 _) ⋙ nativeConstructibleTensor k₀ l Y ≅
      (𝟭 _).prod (upperStar f) ⋙ nativeConstructibleTensor k₀ l X ⋙ extensionByZero f :=
  ((objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft ((objectProperty k₀ l X).ι.prod (objectProperty k₀ l Y).ι)
      (ProEtaleWeilSheaf.nativeOpenProjectionIso k₀ l f))

@[simp]
lemma nativeBoundedProperProjectionIso_hom_app [IsProper f]
    (M : WeilComplex k₀ l X) (N : WeilComplex k₀ l Y) :
    ((nativeBoundedProperProjectionIso (k₀ := k₀) (l := l) f).hom.app (M, N)).hom =
      (rightDerivedLowerStarNativeDerivedTensorIso f).hom.app (M, N) := rfl

@[simp]
lemma nativeBoundedOpenProjectionIso_hom_app [IsOpenImmersion f] [QuasiCompact f]
    (M : WeilComplex k₀ l X) (N : WeilComplex k₀ l Y) :
    ((nativeBoundedOpenProjectionIso (k₀ := k₀) (l := l) f).hom.app (M, N)).hom =
      (ProEtaleWeilSheaf.nativeOpenProjectionIso k₀ l f).hom.app (M.obj, N.obj) := rfl

end AlgebraicGeometry.WeilComplex
