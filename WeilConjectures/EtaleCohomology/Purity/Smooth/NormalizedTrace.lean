/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-!
# The normalized smooth trace

Let `k` be a separably closed perfect field and `a : X ⟶ Spec k` smooth separated of relative
dimension `d`. A purity isomorphism `γ : La^* Λ(d)[2d] ≅ Ra^! Λ` is determined only up to a
unit of `H⁰(X, Λ)`, and the smooth trace `Tr^sm_a = counit ∘ Ra_!(γ)`
(`AlgebraicGeometry.Etale.smoothPurityTrace`) changes by that unit. The canonical purity map of
blueprint `def-pur-smooth-purity-map` is singled out by the normalization of
`thm-pur-trace-normalization-transitivity`: the trace sends the fundamental class of the fibre
to `1`. Here the fibre is `X` itself, and the normalization is imposed at every `k`-point
`x : Spec k ⟶ X`:

`Λ ≅ Ra_! Rx_! Λ ──Ra_!(cl_x)──▶ Ra_! Λ_X(d)[2d] ──Tr^sm_a──▶ Λ`

is the identity, where `cl_x : Rx_! Λ ⟶ Λ_X(d)[2d]` is the adjoint of the fundamental class of
the regular closed immersion `x` (`AlgebraicGeometry.Etale.fundamentalClassMap`), and
`Λ ≅ Ra_! Rx_! Λ` is the canonical composition law of the bounded below `R_!` with
`R(x ≫ a)_! = R(𝟙)_! ≅ 𝟭` (`AlgebraicGeometry.Etale.lowerShriekSectionIso`). Every connected
component of `X` has a `k`-point, so this pins `γ` down; as in
`AlgebraicGeometry.Etale.fundamentalClass`, the canonical purity map
`AlgebraicGeometry.Etale.normalizedSmoothPurityIso` is the unique normalized one.

## Main definitions

- `AlgebraicGeometry.Etale.lowerShriekSectionIso`: `Ra_! Rx_! K ≅ K` for a section `x` of `a`
  and a bounded below `K`.
- `AlgebraicGeometry.Etale.pointFundamentalClassTrace`: the image `T(cl_x) ∈ End(Λ)` of the
  fundamental class of a `k`-point under a trace map `T : Ra_! La^* Λ(d)[2d] ⟶ Λ`.
- `AlgebraicGeometry.Etale.normalizedSmoothPurityIso`: the canonical purity map `γ_a`.
- `AlgebraicGeometry.Etale.smoothTrace`: the canonical smooth trace `Tr^sm_a`.

## Main statements

- `AlgebraicGeometry.Etale.existsUnique_pointFundamentalClassTrace_eq_id`: there is a unique
  purity map whose trace sends the fundamental class of every `k`-point to `1`.
- `AlgebraicGeometry.Etale.counit_eq_smoothTrace`: the counit `Ra_! ω_X ⟶ Λ` is the canonical
  smooth trace, which sends the fundamental class of every `k`-point to `1` (blueprint
  `cor-pur-finite-stage-smooth-dualizing-complex`).

## Implementation notes

The composition law of the unbounded `R_!` is only known to exist
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`), so `Ra_! Rx_! Λ ≅ Λ`
is computed on the bounded below derived categories, where the composition law
`AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso` is canonical, through the
compatibility `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompatibility`.

The normalization is stated for a separably closed perfect base field, where the fibre is the
scheme itself; the fundamental class of `AlgebraicGeometry.Etale.fundamentalClass` needs a
perfect base field. Over a general base the canonical trace is obtained from this one by base
change to geometric points, which needs a canonical base change of the traces and is not done
here.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Section

variable {X Y : Scheme.{u}}

/-- The constant complex `Λ_Y` as an object of the bounded below derived category. -/
noncomputable def constantComplexPlus (Y : Scheme.{u}) :
    _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨constantComplex Λ Y, ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
    (constantComplexIsoSingleFunctor Λ Y).symm 0⟩⟩

/-- For a section `x : Y ⟶ X` of `a : X ⟶ Y` and a bounded below `K ∈ D⁺(Y_ét, Λ)`, the
identification

`Ra_! Rx_! K ≅ Ra_!⁺ Rx_!⁺ K ≅ R(x ≫ a)_!⁺ K = R(𝟙)_!⁺ K ≅ K`

through the canonical composition law of the bounded below compactly supported direct image
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso`). -/
noncomputable def lowerShriekSectionIso (a : X ⟶ Y) (x : Y ⟶ X) (hx : x ≫ a = 𝟙 Y)
    [HasCompactification a] [HasCompactification x]
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(a)_![ModuleCat.{u + 1} Λ]).obj ((R(x)_![ModuleCat.{u + 1} Λ]).obj
        (_root_.DerivedCategory.Plus.ι.obj K)) ≅
      _root_.DerivedCategory.Plus.ι.obj K :=
  haveI : HasCompactification (x ≫ a) := by rw [hx]; infer_instance
  haveI : QuasiCompact (x ≫ a) := by rw [hx]; infer_instance
  (R(a)_![ModuleCat.{u + 1} Λ]).mapIso
      ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} Λ) x).app K).symm ≪≫
    ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} Λ) a).app _).symm ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso ((rightDerivedLowerShriekPlusCompIso Λ x a).app K ≪≫
      (rightDerivedLowerShriekPlusCongr Λ hx).app K ≪≫ (rightDerivedLowerShriekPlusId Λ Y).app K)

end Section

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k]
  [PerfectField k] {X : Scheme.{u}} (d : ℕ) (a : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension d a]
  [HasCompactification a] [HasInvertibleExponent Λ X]

/-- The identification `La^* Λ(d)[2d] ≅ Λ_X(d)[2d]` of the source of the smooth trace with the
shifted Tate twist. -/
noncomputable def twistShiftTateObjectIso :
    (twistShift Λ X d).obj ((L((a)^*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ (Spec (.of k)))) ≅
      (tateObject Λ X d)⟦2 * (d : ℤ)⟧ :=
  (twistShift Λ X d).mapIso (leftDerivedUpperStarConstantComplexIso Λ a) ≪≫
    twistShiftConstantComplexIso Λ X d

/-- The image `T(cl_x) ∈ End(Λ)` of the fundamental class of a `k`-point `x` of `X` under a
trace map `T : Ra_! La^* Λ(d)[2d] ⟶ Λ`: the composite

`Λ ≅ Ra_! Rx_! Λ ──Ra_!(cl_x)──▶ Ra_! Λ_X(d)[2d] ≅ Ra_! La^* Λ(d)[2d] ──T──▶ Λ`

where `cl_x : Rx_! Λ ⟶ Rx_! Rx^! Λ_X(d)[2d] ⟶ Λ_X(d)[2d]` is the adjoint of the fundamental
class of the regular closed immersion `x` of codimension `d`
(`AlgebraicGeometry.Etale.fundamentalClassMap`) and `Λ ≅ Ra_! Rx_! Λ` is
`AlgebraicGeometry.Etale.lowerShriekSectionIso`. The trace sends the fundamental class of `x`
to `1` when this is the identity. -/
noncomputable def pointFundamentalClassTrace
    (T : (R(a)_![ModuleCat.{u + 1} Λ]).obj ((twistShift Λ X d).obj
        ((L((a)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ (Spec (.of k))))) ⟶
      constantComplex Λ (Spec (.of k)))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ a = 𝟙 _) [IsRegularImmersion d x]
    (hZ : ∀ z : Spec (.of k), IsRegularLocalRing ((Spec (.of k)).presheaf.stalk z)) :
    constantComplex Λ (Spec (.of k)) ⟶ constantComplex Λ (Spec (.of k)) :=
  haveI := SmoothOfRelativeDimension.smooth d a
  (lowerShriekSectionIso Λ a x hx (constantComplexPlus Λ _)).inv ≫
    (R(a)_![ModuleCat.{u + 1} Λ]).map ((R(x)_![ModuleCat.{u + 1} Λ]).map
        (fundamentalClassMap Λ d x a hZ) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) x).counit.app
        ((tateObject Λ X d)⟦2 * (d : ℤ)⟧)) ≫
    (R(a)_![ModuleCat.{u + 1} Λ]).map (twistShiftTateObjectIso Λ d a).inv ≫ T

variable [IsSepClosed k] [IsSeparated a]

/-- Blueprint `def-pur-smooth-purity-map`: Smooth purity map

**The normalization pins the purity map down.** For `a : X ⟶ Spec k` smooth separated of
relative dimension `d` over a separably closed perfect field, there is a unique purity
isomorphism `γ : La^* Λ(d)[2d] ≅ Ra^! Λ` whose smooth trace sends the fundamental class of
every `k`-point of `X` to `1` (blueprint `thm-pur-trace-normalization-transitivity`).

Two purity isomorphisms differ by a unit `u` of `H⁰(X, Λ)`, a locally constant function on `X`,
and the traces of the fundamental class of `x` differ by `u(x)`. Every connected component of
`X` has a `k`-point, which gives uniqueness; for existence, the trace of the fundamental class
of a `k`-point generates `End(Λ)` and depends only on the connected component of the point, so
the trace can be rescaled component by component. -/
theorem existsUnique_pointFundamentalClassTrace_eq_id :
    ∃! γ : (twistShift Λ X d).obj ((L((a)^*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ (Spec (.of k)))) ≅
      (R(a)^![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ (Spec (.of k))),
      ∀ (x : Spec (.of k) ⟶ X) (hx : x ≫ a = 𝟙 _) [IsRegularImmersion d x]
        (hZ : ∀ z : Spec (.of k), IsRegularLocalRing ((Spec (.of k)).presheaf.stalk z)),
        pointFundamentalClassTrace Λ d a (smoothPurityTrace Λ d a γ) x hx hZ = 𝟙 _ := by
  -- TODO: needs `H⁰(X, Λ)` as the locally constant functions, the computation
  -- `H^{2d}_c(X, Λ(d)) ≅ Λ` on a connected component generated by the class of a point, and
  -- the existence of a `k`-point on every connected component.
  sorry

/-- Blueprint `def-pur-smooth-purity-map`: Smooth purity map

The canonical smooth purity map `γ_a : La^* Λ(d)[2d] ≅ Ra^! Λ` of `a : X ⟶ Spec k`: the unique
purity isomorphism whose trace sends the fundamental class of every `k`-point to `1`.

It is *defined* as `Classical.choose` of
`AlgebraicGeometry.Etale.existsUnique_pointFundamentalClassTrace_eq_id`; uniqueness is what
makes the choice canonical. -/
noncomputable def normalizedSmoothPurityIso :
    (twistShift Λ X d).obj ((L((a)^*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ (Spec (.of k)))) ≅
      (R(a)^![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ (Spec (.of k))) :=
  (existsUnique_pointFundamentalClassTrace_eq_id Λ d a).exists.choose

/-- Blueprint `def-pur-smooth-trace`: Smooth trace

The canonical smooth trace `Tr^sm_a : Ra_! La^* Λ(d)[2d] ⟶ Λ` of `a : X ⟶ Spec k`: the smooth
trace (`AlgebraicGeometry.Etale.smoothPurityTrace`) of the canonical purity map
`AlgebraicGeometry.Etale.normalizedSmoothPurityIso`. -/
noncomputable def smoothTrace :
    (R(a)_![ModuleCat.{u + 1} Λ]).obj ((twistShift Λ X d).obj
        ((L((a)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ (Spec (.of k))))) ⟶
      constantComplex Λ (Spec (.of k)) :=
  smoothPurityTrace Λ d a (normalizedSmoothPurityIso Λ d a)

/-- Blueprint `thm-pur-trace-normalization-transitivity`: Trace normalization and transitivity

**Normalization.** The canonical smooth trace sends the fundamental class of every `k`-point
of `X` to `1`. -/
theorem pointFundamentalClassTrace_smoothTrace (x : Spec (.of k) ⟶ X) (hx : x ≫ a = 𝟙 _)
    [IsRegularImmersion d x]
    (hZ : ∀ z : Spec (.of k), IsRegularLocalRing ((Spec (.of k)).presheaf.stalk z)) :
    pointFundamentalClassTrace Λ d a (smoothTrace Λ d a) x hx hZ = 𝟙 _ :=
  (existsUnique_pointFundamentalClassTrace_eq_id Λ d a).exists.choose_spec x hx hZ

/-- Blueprint `cor-pur-finite-stage-smooth-dualizing-complex`: Finite-stage smooth dualizing
complex

Let `a : X ⟶ Spec k` be smooth separated of pure dimension `d` over a separably closed perfect
field. Under the canonical identification `γ_a : Λ_X(d)[2d] = La^* Λ(d)[2d] ≅ ω_X`
(`AlgebraicGeometry.Etale.normalizedSmoothPurityIso`), the counit `Ra_! ω_X ⟶ Λ` of
`Ra_! ⊣ Ra^!` is the canonical smooth trace `Tr^sm_a : RΓ_c(X, Λ(d)[2d]) ⟶ Λ`, which sends the
fundamental class of every `k`-point to `1`. -/
theorem counit_eq_smoothTrace :
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) a).counit.app
        (constantComplex Λ (Spec (.of k))) =
      (R(a)_![ModuleCat.{u + 1} Λ]).map (normalizedSmoothPurityIso Λ d a).inv ≫
        smoothTrace Λ d a ∧
    ∀ (x : Spec (.of k) ⟶ X) (hx : x ≫ a = 𝟙 _) [IsRegularImmersion d x]
      (hZ : ∀ z : Spec (.of k), IsRegularLocalRing ((Spec (.of k)).presheaf.stalk z)),
      pointFundamentalClassTrace Λ d a (smoothTrace Λ d a) x hx hZ = 𝟙 _ :=
  ⟨rightDerivedUpperShriekAdjunction_counit_app_eq_smoothPurityTrace _,
    fun x hx _ hZ ↦ pointFundamentalClassTrace_smoothTrace Λ d a x hx hZ⟩

end Etale

end AlgebraicGeometry
