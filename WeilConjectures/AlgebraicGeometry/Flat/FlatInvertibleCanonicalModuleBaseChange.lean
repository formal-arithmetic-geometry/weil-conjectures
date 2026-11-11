/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange
import WeilConjectures.AlgebraicGeometry.FlatModuleCanonicalDerivedPullback

/-! # Derived base change for a line bundle on a flat family

For a flat quasi-compact separated morphism `f : X ⟶ S`, a cartesian square along
`g : S' ⟶ S` and an invertible module `ℒ` on `X`, the base-change map
`Lg^* Rf_* ℒ ⟶ Rf'_* ℒ_{S'}`, with the ordinary pullback `ℒ_{S'}` as target, is an isomorphism.
(blueprint: lemma-coherent-base-change-invertible-sheaves--2)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Blueprint `lemma-coherent-base-change-invertible-sheaves--2`: derived base change for a line
bundle with the pulled-back line bundle as target.

For a flat quasi-compact separated morphism `f : X ⟶ S` (such as `f_T : C_T ⟶ T` for a smooth
proper curve `C`), a cartesian square with `a = g : S' ⟶ S`, and an invertible module `ℒ` on
`X`, the base-change map `La^* Rf_* ℒ ⟶ Rf'_* ℒ_{S'}` is an isomorphism in the derived category of
`𝒪_{S'}`-modules. Here `ℒ_{S'}` is the ordinary pullback `g'^* ℒ`, and the base-change map is the
canonical derived base-change map `La^* Rf_* ℒ ⟶ Rf'_* Lg'^* ℒ` followed by `Rf'_*` of the
comparison `c : Lg'^* ℒ ⟶ g'^* ℒ`, which is itself an isomorphism since `ℒ` is flat.

Proof: `AlgebraicGeometry.exists_isIso_canonicalModuleBaseChange_of_isFlatOver` applies, since
`ℒ` is flat over `S`; the comparison `c` is invertible by flatness of `ℒ` over `𝒪_X`. The
additivity hypothesis on `g'^*` always holds (it is a left adjoint), see the proof of
`AlgebraicGeometry.Scheme.Modules.isIso_derivedBaseChange_of_flat_invertible`. -/
theorem exists_isIso_canonicalModuleBaseChange_of_isInvertible
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] [Flat f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (sq : IsPullback g' f' f g) [(Scheme.Modules.tensorPullback g').Additive]
    (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] :
    ∃ c : (AlgebraicGeometry.derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj M),
      IsDerivedModulePullbackComparison g' M c ∧ IsIso c ∧
        IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≫
          (schemeDerivedDirectImage f').map c) := by
  obtain ⟨c, hc, hbc⟩ := exists_isIso_canonicalModuleBaseChange_of_isFlatOver
    f g g' f' sq M (isFlatOver_of_isInvertible f M)
  exact ⟨c, hc, isIso_modulePullbackComparison_of_isFlatOver_identity
    g' M (isFlatOver_of_isInvertible (𝟙 X) M) c hc, hbc⟩

end AlgebraicGeometry.Scheme.Modules
