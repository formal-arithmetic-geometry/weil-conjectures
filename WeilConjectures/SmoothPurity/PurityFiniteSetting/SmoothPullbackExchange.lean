/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteCoefficientSmoothPurity
public import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth pullback exchange for exceptional inverse image

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/sk-prop-sp-purity-bc/
def-pur-smooth-pullback-exchange.md, definition
(blueprint: def-pur-smooth-pullback-exchange).
The displayed exchange is built in the finite-coefficient intrinsic pro-etale category.
The middle arrow is the explicit native pullback compositor, Cartesian coefficient-twist
comparison and cochain shift comparison transported through the unit-preserving coefficient
realization. Its data contains no arbitrary isomorphism selector.

Main definitions: `sfFinitePullbackComparison` changes pullback coordinates;
`smoothPullbackExchangeFixedSource` constructs the fixed-coordinate middle arrow;
`sfFinitePullback_baseChangeSource` returns it to the original objects; and
`smoothPullbackExchange` is the displayed three-factor composite.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.defProp false
set_option warn.classDefReducibility false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
namespace PurityFiniteSetting

/-- Step 2. The recorded finite-Tor pullback theorem applied to the coefficient
ring and level in `P`. Source:
literature/blueprint/latest/blueprint/part-six-operations/sec-proetale-coefficients/
sec-pe-constructibility/sk-cor-pe-finite-tor-comparison/lem-sf-pullback-tor-amplitude.md
(blueprint: def-pur-smooth-pullback-exchange). -/
noncomputable def sfFinitePullback_finiteTorConstructible
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X
      ((sfFiniteDerivedPullback P.coefficients.l P.extension P.level P.level_pos g).obj K) := by
  let X₀ : Over (Spec (.of P.field.k)) := Over.mk (X ↘ Spec (.of P.field.k))
  let Y₀ : Over (Spec (.of P.field.k)) := Over.mk (Y ↘ Spec (.of P.field.k))
  let g₀ : X₀ ⟶ Y₀ := Over.homMk g (by
    exact (Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp inferInstance)
  let : LocallyOfFiniteType X₀.hom := ‹LocallyOfFiniteType (X ↘ Spec (.of P.field.k))›
  let : QuasiCompact X₀.hom := ‹QuasiCompact (X ↘ Spec (.of P.field.k))›
  let : LocallyOfFiniteType Y₀.hom := ‹LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))›
  let : QuasiCompact Y₀.hom := ‹QuasiCompact (Y ↘ Spec (.of P.field.k))›
  have hsep : IsSeparated (g ≫ (Y ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : g.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : IsSeparated (X ↘ Spec (.of P.field.k)))
  have hlfp : LocallyOfFiniteType (g ≫ (Y ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : g.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)))
  have hqc : QuasiCompact (g ≫ (Y ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : g.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : QuasiCompact (X ↘ Spec (.of P.field.k)))
  let : IsSeparated (g ≫ (Y ↘ Spec (.of P.field.k))) := hsep
  let : LocallyOfFiniteType (g ≫ (Y ↘ Spec (.of P.field.k))) := hlfp
  let : QuasiCompact (g ≫ (Y ↘ Spec (.of P.field.k))) := hqc
  let : IsSeparated g₀.left := IsSeparated.of_comp g (Y ↘ Spec (.of P.field.k))
  let : LocallyOfFiniteType g₀.left := locallyOfFiniteType_of_comp g (Y ↘ Spec (.of P.field.k))
  let : QuasiCompact g₀.left := QuasiCompact.of_comp g (Y ↘ Spec (.of P.field.k))
  simpa [X₀, Y₀, g₀] using
    (sf_pullback_finiteTorConstructible P.field P.coefficients.l P.coefficients.different
      P.extension P.level P.level_pos X₀ Y₀ g₀ K hK)

/-- Step 4, change of coordinates for the recorded derived pullback. First use
`openSquareDerivedPullbackModel`, the derived unit-preserving module comparison.
Then derive the three exact functors separately using the localization compositor.
Source: blueprint `def-pur-smooth-pullback-exchange`, middle arrow; the coefficient
realization is the recorded `def-weil-pbc-proetale-operations` construction
(blueprint: def-pur-smooth-pullback-exchange). -/
def sfFinitePullbackComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (g : X ⟶ Y) :
    sfFiniteDerivedPullback P.coefficients.l P.extension P.level P.level_pos g ≅
      (sfIntrinsicDerivedEquivalence Y P.Ring).inverse ⋙ P.smoothPurityPullback g ⋙
        (sfIntrinsicDerivedEquivalence X P.Ring).functor := by
  let R := (sfIntrinsicModuleEquivalence Y P.Ring).inverse
  let F := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g
  let S := (sfIntrinsicModuleEquivalence X P.Ring).functor
  letI : S.Additive :=
    inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization X P.Ring).Additive
  exact openSquareDerivedPullbackModel P.Ring g ≪≫
    Functor.mapDerivedCategoryCompIso R (F ⋙ S) ≪≫
    Functor.isoWhiskerLeft R.mapDerivedCategory (Functor.mapDerivedCategoryCompIso F S)

/-- Step 4 in fixed scalar coordinates. Move the outer shift through pullback,
use its tensor comparison, and pull the shifted Tate coefficient back by the
Cartesian twist comparison and the negative-shift commutator. Apply the twist/shift
functor to the square compositor
`c(f',v) ∘ eqToIso(sq.w) ∘ c(u,f)⁻¹`.
Source: blueprint `def-pur-smooth-pullback-exchange`, displayed middle arrow
(blueprint: def-pur-smooth-pullback-exchange). -/
def smoothPullbackExchangeFixedSource (P : PurityFiniteSetting.{u})
    {X' X Y' Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (d : ℕ)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.smoothPurityPullback u).obj
        ((P.compositionTwistShift X d).obj ((P.smoothPurityPullback f).obj M)) ≅
      (P.compositionTwistShift X' d).obj
        ((P.smoothPurityPullback f').obj ((P.smoothPurityPullback v).obj M)) := by
  let F := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) u).mapDerivedCategory
  let N := (P.smoothPurityPullback f).obj M
  let T := P.diagonalTwist X d
  let r : ℤ := 2 * (d : ℤ)
  let shift := shiftFunctor
    (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} P.Coefficient))) r
  let coefficient : F.obj (T⟦-r⟧) ≅ (P.diagonalTwist X' d)⟦-r⟧ :=
    (F.commShiftIso (-r)).app T ≪≫
      (shiftFunctor _ (-r)).mapIso (P.compositionTwistPullback u d)
  let tensor := compositionPullbackTensorFixed P.Ring u N (T⟦-r⟧)
  let twist := compositionTensorMapIso (smoothPurityTensor P.Coefficient X')
    (Iso.refl (F.obj N)) coefficient
  let square : P.smoothPurityPullback f ⋙ P.smoothPurityPullback u ≅
      P.smoothPurityPullback v ⋙ P.smoothPurityPullback f' :=
    (compositionFixedPullbackComp P.Ring u f).symm ≪≫
      eqToIso (congrArg (fun g : X' ⟶ Y ↦ P.smoothPurityPullback g) sq.w) ≪≫
      compositionFixedPullbackComp P.Ring f' v
  exact (F.commShiftIso r).app (((smoothPurityTensor P.Coefficient X).obj N).obj
      (T⟦-r⟧)) ≪≫ shift.mapIso tensor ≪≫ shift.mapIso twist ≪≫
    (P.compositionTwistShift X' d).mapIso (square.app M)

/-- Step 4 on the node's original objects. Transport the explicit fixed-coordinate
compositor/twist/shift composite with `sfFinitePullbackComparison`; cancel each
inserted realization equivalence by its unit. No endpoint isomorphism is selected.
Source: blueprint `def-pur-smooth-pullback-exchange`, displayed middle arrow
(blueprint: def-pur-smooth-pullback-exchange). -/
def sfFinitePullback_baseChangeSource
    (P : PurityFiniteSetting.{u}) {X' X Y' Y : Scheme.{u}}
    [X'.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (d : ℕ)
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (sfFiniteDerivedPullback P.coefficients.l P.extension P.level P.level_pos u).obj
        ((P.compositionShiftedPullback f d).obj K) ≅
      (P.compositionShiftedPullback f' d).obj
        ((sfFiniteDerivedPullback P.coefficients.l P.extension P.level P.level_pos v).obj K) := by
  let EX := sfIntrinsicDerivedEquivalence X P.Ring
  let EX' := sfIntrinsicDerivedEquivalence X' P.Ring
  let EY := sfIntrinsicDerivedEquivalence Y P.Ring
  let EY' := sfIntrinsicDerivedEquivalence Y' P.Ring
  let M := EY.inverse.obj K
  let N := (P.compositionTwistShift X d).obj ((P.smoothPurityPullback f).obj M)
  let first := (P.sfFinitePullbackComparison u).app (EX.functor.obj N) ≪≫
    EX'.functor.mapIso ((P.smoothPurityPullback u).mapIso (EX.unitIso.app N).symm)
  let middle := EX'.functor.mapIso (P.smoothPullbackExchangeFixedSource u f' f v sq d M)
  let right := EY'.inverse.mapIso ((P.sfFinitePullbackComparison v).app K) ≪≫
    (EY'.unitIso.app ((P.smoothPurityPullback v).obj M)).symm
  let last := EX'.functor.mapIso ((P.compositionTwistShift X' d).mapIso
    ((P.smoothPurityPullback f').mapIso right.symm))
  exact first ≪≫ middle ≪≫ last

/-- Derive separatedness of a k-morphism from separatedness of its source structure map.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/sk-prop-sp-purity-bc/
def-pur-smooth-pullback-exchange.md, step 2
(blueprint: def-pur-smooth-pullback-exchange). -/
noncomputable def separatedOfStructure (P : PurityFiniteSetting.{u}) {T W : Scheme.{u}}
    [T.Over (Spec (.of P.field.k))] [W.Over (Spec (.of P.field.k))]
    (h : T ⟶ W) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    [IsSeparated (W ↘ Spec (.of P.field.k))] : IsSeparated h := by
  let : IsSeparated (h ≫ (W ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : h.IsOver (Spec (.of P.field.k)))).symm ▸ inferInstance
  exact IsSeparated.of_comp h (W ↘ Spec (.of P.field.k))

/-- Step 2: derive local finite type of a k-morphism from its source structure map.
Source: blueprint definition, scheme-morphism cancellation
(blueprint: def-pur-smooth-pullback-exchange). -/
noncomputable def locallyOfFiniteTypeOfStructure (P : PurityFiniteSetting.{u}) {T W : Scheme.{u}}
    [T.Over (Spec (.of P.field.k))] [W.Over (Spec (.of P.field.k))]
    (h : T ⟶ W) [h.IsOver (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [IsSeparated (W ↘ Spec (.of P.field.k))] : LocallyOfFiniteType h := by
  let : LocallyOfFiniteType (h ≫ (W ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : h.IsOver (Spec (.of P.field.k)))).symm ▸ inferInstance
  exact locallyOfFiniteType_of_comp h (W ↘ Spec (.of P.field.k))

/-- Step 2: derive quasi-compactness of a k-morphism from its source structure map.
Source: blueprint definition, scheme-morphism cancellation
(blueprint: def-pur-smooth-pullback-exchange). -/
noncomputable def quasiCompactOfStructure (P : PurityFiniteSetting.{u}) {T W : Scheme.{u}}
    [T.Over (Spec (.of P.field.k))] [W.Over (Spec (.of P.field.k))]
    (h : T ⟶ W) [h.IsOver (Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    [IsSeparated (W ↘ Spec (.of P.field.k))] : QuasiCompact h := by
  let : QuasiCompact (h ≫ (W ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : h.IsOver (Spec (.of P.field.k)))).symm ▸ inferInstance
  exact QuasiCompact.of_comp h (W ↘ Spec (.of P.field.k))

/-- The exceptional inverse image with the step-2 morphism properties supplied by
the structure-map derivations above.
Source: blueprint definition, typing the exceptional inverse images
(blueprint: def-pur-smooth-pullback-exchange). -/
noncomputable def compositionExceptionalDerived (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))] :
    Scheme.proEtaleDerivedCategory Y P.Ring ⥤
      Scheme.proEtaleDerivedCategory X P.Ring := by
  letI : IsSeparated h := P.separatedOfStructure h
  letI : LocallyOfFiniteType h := P.locallyOfFiniteTypeOfStructure h
  letI : QuasiCompact h := P.quasiCompactOfStructure h
  exact P.compositionExceptional h

/-- Steps 1--5. The smooth pullback exchange is the typed composite of inverse pulled-back
purity, the native Cartesian source comparison, and the final smooth purity map.
For each hypothesis: the four `Over` instances give the k-schemes; the four `IsOver`
instances give k-morphisms; separated, locally finite type and quasi-compact instances
are the finite-type hypotheses; `sq` is the Cartesian square; `[SmoothOfRelativeDimension
 d f]` is the smooth pure-dimension clause; and `hK` is the bounded constructible
finite-Tor clause. Step 1 uses the finite coefficient ring and the specified small
pro-etale operations. Step 2 derives the three morphism properties by cancellation,
base changes smoothness, and applies `lem-sf-pullback-tor-amplitude` to supply the domain
of the final purity map. Step 3 applies `thm-pur-finite-coefficient-smooth-purity` to
invert the recorded `def-pur-smooth-purity-map`. Step 4 is the explicit compositor,
Cartesian twist and shift construction of `sfFinitePullback_baseChangeSource`, using
`prop-sfb-module-left-derived-upper-star-comp` and
`det-prop-sfb-cartesian-coefficients-twists`. Step 5 composes the three factors;
their inverses in reverse order give the inverse.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/sk-prop-sp-purity-bc/
def-pur-smooth-pullback-exchange.md
(blueprint: def-pur-smooth-pullback-exchange). -/
def smoothPullbackExchange
    (P : PurityFiniteSetting.{u}) {X' X Y' Y : Scheme.{u}}
    [X'.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    [u.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [f.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
    (sq : IsPullback u f' f v) (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (sfFiniteDerivedPullback P.coefficients.l P.extension P.level P.level_pos u).obj
        ((P.compositionExceptionalDerived f).obj K) ≅
      (P.compositionExceptionalDerived f').obj
        ((sfFiniteDerivedPullback P.coefficients.l P.extension P.level P.level_pos v).obj K) := by
  have hsep_f : IsSeparated (f ≫ (Y ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : f.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : IsSeparated (X ↘ Spec (.of P.field.k)))
  let : IsSeparated (f ≫ (Y ↘ Spec (.of P.field.k))) := hsep_f
  let : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of P.field.k))
  have hlfp_f : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : f.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)))
  let : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k))) := hlfp_f
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of P.field.k))
  have hqc_f : QuasiCompact (f ≫ (Y ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : f.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : QuasiCompact (X ↘ Spec (.of P.field.k)))
  let : QuasiCompact (f ≫ (Y ↘ Spec (.of P.field.k))) := hqc_f
  let : QuasiCompact f := QuasiCompact.of_comp f (Y ↘ Spec (.of P.field.k))
  have hsep_v : IsSeparated (v ≫ (Y ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : v.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : IsSeparated (Y' ↘ Spec (.of P.field.k)))
  let : IsSeparated (v ≫ (Y ↘ Spec (.of P.field.k))) := hsep_v
  let : IsSeparated v := IsSeparated.of_comp v (Y ↘ Spec (.of P.field.k))
  have hlfp_v : LocallyOfFiniteType (v ≫ (Y ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : v.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k)))
  let : LocallyOfFiniteType (v ≫ (Y ↘ Spec (.of P.field.k))) := hlfp_v
  let : LocallyOfFiniteType v := locallyOfFiniteType_of_comp v (Y ↘ Spec (.of P.field.k))
  have hqc_v : QuasiCompact (v ≫ (Y ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : v.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : QuasiCompact (Y' ↘ Spec (.of P.field.k)))
  let : QuasiCompact (v ≫ (Y ↘ Spec (.of P.field.k))) := hqc_v
  let : QuasiCompact v := QuasiCompact.of_comp v (Y ↘ Spec (.of P.field.k))
  have hsep_f' : IsSeparated (f' ≫ (Y' ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : f'.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : IsSeparated (X' ↘ Spec (.of P.field.k)))
  let : IsSeparated (f' ≫ (Y' ↘ Spec (.of P.field.k))) := hsep_f'
  let : IsSeparated f' := IsSeparated.of_comp f' (Y' ↘ Spec (.of P.field.k))
  have hlfp_f' : LocallyOfFiniteType (f' ≫ (Y' ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : f'.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : LocallyOfFiniteType (X' ↘ Spec (.of P.field.k)))
  let : LocallyOfFiniteType (f' ≫ (Y' ↘ Spec (.of P.field.k))) := hlfp_f'
  let : LocallyOfFiniteType f' := locallyOfFiniteType_of_comp f' (Y' ↘ Spec (.of P.field.k))
  have hqc_f' : QuasiCompact (f' ≫ (Y' ↘ Spec (.of P.field.k))) := by
    exact ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp
      (inferInstance : f'.IsOver (Spec (.of P.field.k)))).symm ▸
      (inferInstance : QuasiCompact (X' ↘ Spec (.of P.field.k)))
  let : QuasiCompact (f' ≫ (Y' ↘ Spec (.of P.field.k))) := hqc_f'
  let : QuasiCompact f' := QuasiCompact.of_comp f' (Y' ↘ Spec (.of P.field.k))
  let _ := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  let : SmoothOfRelativeDimension d f' :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) sq inferInstance
  let hK' := sfFinitePullback_finiteTorConstructible P v K hK
  letI := P.isIso_smoothPurityMap f d K hK
  letI := P.isIso_smoothPurityMap f' d
    ((sfFiniteDerivedPullback P.coefficients.l P.extension P.level P.level_pos v).obj K) hK'
  exact
    ((sfFiniteDerivedPullback P.coefficients.l P.extension P.level P.level_pos u).mapIso
      (asIso (P.smoothPurityMap f d K hK))).symm ≪≫
    sfFinitePullback_baseChangeSource P u f' f v sq d K ≪≫
      asIso (P.smoothPurityMap f' d
        ((sfFiniteDerivedPullback P.coefficients.l P.extension P.level P.level_pos v).obj K) hK')

end PurityFiniteSetting
end WeilConjectures
