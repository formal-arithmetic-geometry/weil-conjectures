/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence

/-!
# The strict open comparison of the localization sequence

Source: trace-additivity proof Steps 2 and 6, Stacks Tag 09AH
(blueprint: lem-trf-localization-sheaf-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
variable {R : Type (u + 1)} [Ring R] {U Z X : Scheme.{u}}
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  (hji : IsCompl (Set.range j.base) (Set.range i.base))
  (t : X ⟶ X) (tU : U ⟶ U) (tZ : Z ⟶ Z)
  (hj : tU ≫ j = j ≫ t) (hi : tZ ≫ i = i ≫ t)

/-- The open part of the comparison of the two short exact localization sequences.
Source: trace-additivity Steps 2 and 6, Stacks Tag 09AH
(blueprint: lem-trf-localization-sheaf-exchange). -/
def localizationSheafOpenExchangeObj
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (upperStar (ModuleCat.{u + 1} R) t).obj
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj
        ((upperStar (ModuleCat.{u + 1} R) j).obj M)) ≅
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj
      ((upperStar (ModuleCat.{u + 1} R) j).obj
        ((upperStar (ModuleCat.{u + 1} R) t).obj M)) :=
  ShortComplex.π₁.mapIso
    (openClosedShortComplexBaseChangeIso i j t i j tZ tU
      hji.symm hji.symm hi.symm hj.symm M)

/-- The open comparison commutes with the actual counit and has identity total map.
Source: trace-additivity Steps 2 and 6, Stacks Tag 09AH.
Proof: this is the first square of the short-complex isomorphism; its middle
map is the identity by construction.
(blueprint: lem-trf-localization-sheaf-exchange). -/
theorem localizationSheafOpenExchangeObj_counit
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (localizationSheafOpenExchangeObj j i hji t tU tZ hj hi M).hom ≫
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app
          ((upperStar (ModuleCat.{u + 1} R) t).obj M) =
      (upperStar (ModuleCat.{u + 1} R) t).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app M) := by
  simpa [localizationSheafOpenExchangeObj, openClosedShortComplex] using
    (openClosedShortComplexBaseChangeIso i j t i j tZ tU
      hji.symm hji.symm hi.symm hj.symm M).hom.comm₁₂

/-- The strict open comparison is natural, as its counit square determines it uniquely.
Source: trace-additivity Steps 2 and 6, Stacks Tag 09AH.
Proof: compose the naturality equation with the target open counit, which is
monic by the localization short exact sequence. Both sides then agree by the
counit square and naturality of the counit.
(blueprint: lem-trf-localization-sheaf-exchange). -/
def localizationSheafOpenExchange :
    (upperStar (ModuleCat.{u + 1} R) j ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} R) j) ⋙
        upperStar (ModuleCat.{u + 1} R) t ≅
      upperStar (ModuleCat.{u + 1} R) t ⋙
        (upperStar (ModuleCat.{u + 1} R) j ⋙
          openImmersionLowerShriek (ModuleCat.{u + 1} R) j) :=
  NatIso.ofComponents (localizationSheafOpenExchangeObj j i hji t tU tZ hj hi) (by
    intro M N f
    let a := (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit
    let H := upperStar (ModuleCat.{u + 1} R) t
    have : Mono (a.app (H.obj N)) :=
      (shortExact_openClosedShortComplex i j hji.symm (H.obj N)).mono_f
    apply (cancel_mono (a.app (H.obj N))).1
    dsimp only [Functor.comp_map]
    rw [Category.assoc, localizationSheafOpenExchangeObj_counit]
    have hn : (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).map
        ((upperStar (ModuleCat.{u + 1} R) j).map (H.map f)) ≫ a.app (H.obj N) =
        a.app (H.obj M) ≫ H.map f := a.naturality (H.map f)
    rw [Category.assoc, hn, ← Category.assoc]
    change H.map _ ≫ H.map _ =
      ((localizationSheafOpenExchangeObj j i hji t tU tZ hj hi M).hom ≫
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app
          (H.obj M)) ≫ H.map f
    rw [localizationSheafOpenExchangeObj_counit, ← H.map_comp, ← H.map_comp]
    exact congrArg H.map (a.naturality f))

end AlgebraicGeometry.ProEtale
