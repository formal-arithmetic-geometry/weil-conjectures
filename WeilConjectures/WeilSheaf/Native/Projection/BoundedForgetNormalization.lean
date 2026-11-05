/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.CompactForgetComparison
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionForgetIsoTransport

/-! # Components of the bounded tensor and pullback realization comparisons -/

@[expose] public noncomputable section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The composition comparison from the derived realization to its two derived factors. -/
def projectionRealizationCompIso (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :=
  Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
    (adicSheafEquivCondensedMod l _).functor

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- The bounded tensor comparison is the transported ambient tensor comparison. -/
lemma compactProjectionForgetTensorIso_hom_app (M N : WeilComplex k₀ l X) :
    ((compactProjectionForgetTensorIso k₀ l X).hom.app (M, N)).hom =
      (projectionTensorForgetIso (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l X)
        (projectionRealizationCompIso k₀ l X)).hom.app (M.obj, N.obj) := rfl

/-- The bounded pullback comparison is the transported ambient pullback comparison. -/
lemma compactProjectionForgetUpperStarIso_hom_app
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (M : WeilComplex k₀ l Y) :
    ((compactProjectionForgetUpperStarIso k₀ l f).hom.app M).hom =
      (projectionPushForgetIso (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso
        k₀ l f).symm (projectionRealizationCompIso k₀ l Y)
          (projectionRealizationCompIso k₀ l X)).hom.app M.obj := rfl

end AlgebraicGeometry.WeilComplex
