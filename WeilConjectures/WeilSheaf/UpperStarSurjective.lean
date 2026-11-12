/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.SurjectiveUnit
public import WeilConjectures.WeilSheaf.UpperStarFiniteEtale

/-!
# The unit of `g^* ⊣ g_*` on Weil sheaves along a surjective étale morphism

For a quasi-compact quasi-separated surjective étale morphism `g` of `k₀`-schemes, the unit
`F ⟶ g_* g^* F` of Weil sheaves is a monomorphism
(`AlgebraicGeometry.WeilSheaf.mono_upperStarLowerStarAdjunction_unit_app_of_surjective`): its
underlying morphism of `ℓ`-adic sheaves is the unit along the base change of `g` to the
geometric fibres, which is again quasi-compact, surjective and étale.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- For a qcqs surjective étale morphism `g` of `k₀`-schemes, the unit `F ⟶ g_* g^* F`
of Weil sheaves is a monomorphism: on underlying `ℓ`-adic sheaves it is the unit along the base
change of `g` to the geometric fibres
(`AlgebraicGeometry.ProEtale.mono_adicUpperStarLowerStarAdjunction_unit_app`). -/
theorem mono_upperStarLowerStarAdjunction_unit_app_of_surjective (g : X ⟶ Y)
    [g.IsOver (Spec (CommRingCat.of k₀))] [Etale g] [Surjective g] [QuasiCompact g]
    [QuasiSeparated g]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y) :
    Mono ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) g).unit.app F) := by
  have : Etale (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Etale) g _ ‹_›
  have : Surjective (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Surjective) g _ ‹_›
  have : QuasiCompact
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @QuasiCompact) g _ ‹_›
  have h : Mono ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) g).unit.app F).hom.hom.f := by
    rw [upperStarLowerStarAdjunction_unit_app_hom_hom_f]
    exact ProEtale.mono_adicUpperStarLowerStarAdjunction_unit_app l _ _
  have : Mono ((Endofunctor.IsoAlgebra.forget _).map
      ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) g).unit.app F).hom) := h
  have : Mono ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) g).unit.app F).hom :=
    (Endofunctor.IsoAlgebra.forget _).mono_of_mono_map this
  exact (ObjectProperty.ι _).mono_of_mono_map this

end AlgebraicGeometry.WeilSheaf
