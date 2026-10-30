/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.StalkFrobeniusOfId
public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.WeilSheaf.CondensedModelWeil
public import WeilConjectures.WeilSheaf.PointTraceComparison

/-!
# Traces of Weil sheaves on `Spec k₀` in the two models

TODO
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Traces on `Spec k₀` in the two models.** -/
theorem endTensorUnitRingEquiv_weilSheafStalkTrace_ofId
    (G : AlgebraicGeometry.WeilSheaf k₀ l (Spec (CommRingCat.of k₀)))
    (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (CommRingCat.of k₀))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (CommRingCat.of k₀))))
    (β : (ProEtaleWeilSheaf.toCondensed k₀ l (Spec (CommRingCat.of k₀))).obj G.obj ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).obj N)
    (m : ℕ) (hm : 1 ≤ m) :
    endTensorUnitRingEquiv l (AlgebraicClosure k₀)
        (weilSheafStalkTrace l m (specAlgebraicClosure k₀) (specAlgebraicClosure_comp_pow m)
          (ProEtale.CondensedRing.WeilSheaf.ofId l (X := point k₀) N)) =
      LinearMap.trace (PadicAlgCl l) _ (G.globalSections.frobeniusEnd ^ m) :=
  sorry

end AlgebraicGeometry.WeilComplex
