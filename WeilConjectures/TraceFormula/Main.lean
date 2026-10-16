/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Correspondence
public import WeilConjectures.TraceFormula.FixedPoint

/-!

# The Grothendieck–Lefschetz trace formula

Let `k₀ = 𝔽_q` be a finite field, `k` an algebraic closure, `X₀` a separated `k₀`-scheme of finite
type, `X = X₀ ×_{k₀} k` with its model Frobenius `Φ` (`ProEtale.CondensedRing.IsModelFrobenius`)
and `(K, φ)` a Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `Φ`. For every `m ≥ 1`,
```
tr(F_{c,m} | RΓ_c(X, K)) = ∑_{x ∈ X₀(𝔽_{q^m})} tr(F_{x,m} | K_x̄)
```
(`ProEtale.CondensedRing.trace_globalOperator_eq_sum_trace_stalkFrobenius`, blueprint
`thm-trf-grothendieck-lefschetz-finite-ring` and `thm-trf-grothendieck-lefschetz-qbar`), where

* `F_{c,m}` is the Frobenius of the Weil object `RΓ_c(X, (K, φ_m))` for the identity of the base
  point, the compactly supported cohomology of Weil objects
  (`ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator`);
* `x` runs over the rational points of `X` fixed by `Φ_m`, which are the points of `X₀` rational
  over `𝔽_{q^m}` (`ProEtale.CondensedRing.IsModelFrobenius.fixedPointEquiv`);
* `F_{x,m}` is the Frobenius of the stalk of `(K, φ_m)` at `x`, the image of `(K, φ_m)` under the
  stalk functor of Weil objects (`ProEtale.CondensedRing.WeilBoundedConstructible.stalkFrobenius`);
* both traces are categorical traces in `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`, with values in
  `End (ℚ̄_ℓ,s) ≅ ℚ̄_ℓ` (`ProEtale.CondensedRing.unitEndRingEquiv`), of perfect complexes
  (`WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology`,
  `WeilBoundedConstructible.nonempty_hasRightDual_stalk`).

For the constant Weil object `ℚ̄_ℓ` every local trace is `1`, and the formula counts the points
of `X₀` over `𝔽_{q^m}` (`ProEtale.CondensedRing.trace_globalOperator_unit_eq_card`, blueprint
`cor-trf-point-counting`).

## The proof

The proof follows the blueprint (`sk-thm-trace-formula`); here only its steps are stated, for the
statement `ProEtale.CondensedRing.WeilBoundedConstructible.TraceFormula` of the trace formula of
a Weil object in degree `m` and its version `ProEtale.CondensedRing.ModelTraceFormula` for all
Weil objects over a model `X₀`:

1. **Additivity** (blueprint `prop-trf-trace-additivity-open-closed`): for an open subscheme
   `U ⊆ X` with closed complement `Z`, both stable under Frobenius,
   `tr(F_c | RΓ_c(X, K)) = tr(F_c | RΓ_c(U, K|_U)) + tr(F_c | RΓ_c(Z, K|_Z))`
   (`ProEtale.CondensedRing.WeilBoundedConstructible.trace_compactFrobenius_eq_add`), so the
   trace formula on `U` and on `Z` gives it on `X`
   (`ProEtale.CondensedRing.modelTraceFormula_of_isCompl`).
2. **Dimension zero** (`ProEtale.CondensedRing.modelTraceFormula_of_isFinite`).
3. **Smooth curves** (`ProEtale.CondensedRing.modelTraceFormula_of_smoothOfRelativeDimension_one`):
   by the Lefschetz–Verdier formula on a compactification
   (`Correspondence.trace_globalOperator_eq_integral_traceClass`), the decomposition of the
   integral into local terms over the finite fixed locus
   (`BorelMooreSection.integral_eq_sum_localTerm`) and the computation of the local terms of the
   Frobenius correspondence (`WeilBoundedConstructible.localTerm_traceClass_graph_eq_trace`),
   which uses smooth purity `ω_C ≅ ℚ̄_ℓ,C(1)[2]`.
4. **Fibrations in curves** (blueprint `lem-trf-weil-shriek-operator-fibres`): along a morphism
   `f`, the trace formula for `Rf_! K` and for the restrictions of `K` to the fibres gives the
   trace formula for `K`, by the Leray isomorphism
   `nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso` and proper base change for Weil
   objects `nonempty_weilStalk_weilLowerShriekOfFrobenius_iso`.

Noetherian induction on `X₀` along affine open covers, closed subschemes of affine spaces and
projections to affine spaces of smaller dimension combines these steps.

## Main statements

- `ProEtale.CondensedRing.trace_globalOperator_eq_sum_trace_stalkFrobenius`: the
  Grothendieck–Lefschetz trace formula.
- `ProEtale.CondensedRing.trace_globalOperator_eq_sum_trace_stalkFrobenius_padicAlgCl`: the same,
  in `ℚ̄_ℓ`.
- `ProEtale.CondensedRing.trace_globalOperator_unit_eq_card`: the point-counting formula.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### The statement -/

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X}

variable (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) [IsFinite (frobeniusIterate Φ m).left]
  [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] in
/-- The *trace formula* for a Weil object `(K, φ)` in degree `m`: the trace of the global
operator `F_{c,m}` on `RΓ_c(X, K)` is the sum over the rational points `x` fixed by `Φ_m` of the
traces of the local Frobenii `F_{x,m}` on the geometric stalks `K_x̄`. The traces do not depend on
the choice of the duals of the perfect complexes `RΓ_c(X, K)` and `K_x̄`. -/
def TraceFormula : Prop :=
  ∀ [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        K.carrier)],
    trace (K.globalOperator m) = ∑ x : FixedPoint Φ m, trace (K.stalkFrobenius m x.1 x.2)

/-! ### Additivity -/

variable {U Z : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X} [IsOpenImmersion j.left]
  [IsClosedImmersion i.left]

/-- **Additivity of the compactly supported Frobenius along an open–closed decomposition**
(blueprint `prop-trf-trace-additivity-open-closed`): for an open subscheme `j : U ⟶ X` with
closed complement `i : Z ⟶ X`, both stable under the Frobenius, the trace of the Frobenius of
`RΓ_c(X, K)` is the sum of the traces of the Frobenii of `RΓ_c(U, K|_U)` and `RΓ_c(Z, K|_Z)`,
the restrictions being the derived pullbacks of Weil objects. It comes from the localization
triangle `j_! j^* K ⟶ K ⟶ i_* i^* K ⟶`, a triangle of Weil objects, and the additivity of
traces in distinguished triangles (blueprint `lem-trf-trace-triangle-compatibility`); no
invertibility of `φ` is used in the blueprint. -/
theorem trace_compactFrobenius_eq_add
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ)
    [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left]
    [IsUniversalHomeomorphism ΦU.left] [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]
    (K : WeilBoundedConstructible ℓ Φ)
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint U)).obj
        ((weilUpperStar ℓ ΦU Φ j hj).obj K).carrier)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).obj
        ((weilUpperStar ℓ ΦZ Φ i hi).obj K).carrier)] :
    trace K.compactFrobenius =
      trace ((weilUpperStar ℓ ΦU Φ j hj).obj K).compactFrobenius +
        trace ((weilUpperStar ℓ ΦZ Φ i hi).obj K).compactFrobenius :=
  sorry

/-- The stalks of the restriction of a Weil object to a Frobenius stable subscheme are the
stalks of the Weil object: for `j : U ⟶ X` with `Φ_U ≫ j = j ≫ Φ` and a rational point `x` of
`U` fixed by `Φ_{U,m}`, the local Frobenius of `K|_U` at `x` has the trace of the local
Frobenius of `K` at `x ≫ j` (blueprint `prop-trf-trace-additivity-open-closed`, the stalk
side). -/
theorem trace_stalkFrobenius_weilUpperStar (hj : ΦU ≫ j = j ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint U)
    (hx : x ≫ frobeniusIterate ΦU m = x)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      ((weilUpperStar ℓ ΦU Φ j hj).obj K).carrier)]
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ j)).obj
      K.carrier)] :
    trace (((weilUpperStar ℓ ΦU Φ j hj).obj K).stalkFrobenius m x hx) =
      trace (K.stalkFrobenius m (x ≫ j) (comp_comp_frobeniusIterate_of_comp hj hx)) :=
  sorry

end WeilBoundedConstructible

/-! ### The trace formula over a model -/

section Model

variable (ℓ) {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]

/-- The trace formula over a model `X₀` of finite type over `k₀`: for every base change `X` of
`X₀` to `k` with its model Frobenius `Φ`, every Weil object `(K, φ)` for `Φ` and every `m ≥ 1`,
the trace formula holds (`WeilBoundedConstructible.TraceFormula`). -/
def ModelTraceFormula {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k₀)) [LocallyOfFiniteType f₀] :
    Prop :=
  ∀ (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (Φ : X ⟶ X) (p : X.left ⟶ X₀) (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructible ℓ Φ) (m : ℕ), 1 ≤ m →
      haveI := hΦ.isFinite m
      haveI := hΦ.isUniversalHomeomorphism m
      K.TraceFormula m

variable {ℓ}

/-- **The trace formula in dimension zero** (blueprint `sk-thm-trace-formula`, Step 1): for a
finite model `X₀`, the fixed points of `Φ_m` are isolated and both sides are computed on the
finitely many points of `X`. -/
theorem modelTraceFormula_of_isFinite [IsAlgClosed k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k₀)) [IsFinite f₀] : ModelTraceFormula ℓ (k := k) f₀ :=
  sorry

/-- **The trace formula for smooth curves** (blueprint `sk-thm-trace-formula`, through
`sk-p-frob` and `sk-p-local`): for a model `X₀` separated and smooth of relative dimension one
over `k₀`, the trace formula follows from the Lefschetz–Verdier formula on a compactification,
the decomposition of the integral of the trace class into local terms along the finite fixed
locus, and the computation of the local terms of the Frobenius correspondence. -/
theorem modelTraceFormula_of_smoothOfRelativeDimension_one [IsAlgClosed k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k₀)) [IsSeparated f₀] [QuasiCompact f₀]
    [SmoothOfRelativeDimension 1 f₀] :
    haveI := SmoothOfRelativeDimension.smooth 1 f₀
    ModelTraceFormula ℓ (k := k) f₀ :=
  sorry

/-- **The trace formula is additive** (blueprint `sk-i-global-additivity`): for a closed
subscheme `i₀ : Z₀ ⟶ X₀` with open complement `j₀ : U₀ ⟶ X₀`, the trace formula over `U₀` and
over `Z₀` gives the trace formula over `X₀`. -/
theorem modelTraceFormula_of_isCompl {X₀ U₀ Z₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k₀))
    [LocallyOfFiniteType f₀] (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀]
    [IsClosedImmersion i₀] (hcompl : IsCompl (Set.range j₀.base) (Set.range i₀.base))
    (hU : ModelTraceFormula ℓ (k := k) (j₀ ≫ f₀)) (hZ : ModelTraceFormula ℓ (k := k) (i₀ ≫ f₀)) :
    ModelTraceFormula ℓ (k := k) f₀ :=
  sorry

/-- **The trace formula over every model** (blueprint `sk-thm-trace-formula`), by Noetherian
induction from `modelTraceFormula_of_isCompl`, `modelTraceFormula_of_isFinite`,
`modelTraceFormula_of_smoothOfRelativeDimension_one` and the fibration step of
`nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso` and
`nonempty_weilStalk_weilLowerShriekOfFrobenius_iso`. -/
theorem modelTraceFormula [IsAlgClosed k] {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k₀))
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀] :
    ModelTraceFormula ℓ (k := k) f₀ :=
  sorry

end Model

/-! ### The trace formula -/

variable {Φ : X ⟶ X} {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}

/-- **The Grothendieck–Lefschetz trace formula** (blueprint
`thm-trf-grothendieck-lefschetz-finite-ring`, `thm-trf-grothendieck-lefschetz-qbar`): let
`X = X₀ ×_{k₀} k` be the base change of a separated `k₀`-scheme of finite type to an
algebraically closed field `k`, with model Frobenius `Φ`, and let `(K, φ)` be a Weil object of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `Φ`. For every `m ≥ 1`,
```
tr(F_{c,m} | RΓ_c(X, K)) = ∑_{x ∈ X₀(𝔽_{q^m})} tr(F_{x,m} | K_x̄),
```
the sum running over the rational points `x` of `X` fixed by `Φ_m`, where `F_{c,m}` is the
Frobenius of the compactly supported cohomology `RΓ_c(X, (K, φ_m))` and `F_{x,m}` the Frobenius
of the stalk of `(K, φ_m)` at `x`, both Weil objects for the identity of the base point. -/
theorem trace_globalOperator_eq_sum_trace_stalkFrobenius [IsAlgClosed k] [IsSeparated f₀]
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (hm : 1 ≤ m)
    [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        K.carrier)] :
    haveI := hΦ.isFinite m
    haveI := hΦ.isUniversalHomeomorphism m
    trace (K.globalOperator m) = ∑ x : FixedPoint Φ m, trace (K.stalkFrobenius m x.1 x.2) := by
  have h := modelTraceFormula (ℓ := ℓ) (k := k) f₀ X Φ p hΦ K m hm
  exact h

/-- **The Grothendieck–Lefschetz trace formula in `ℚ̄_ℓ`**: the trace formula
`trace_globalOperator_eq_sum_trace_stalkFrobenius` read through
`End (ℚ̄_ℓ,s) ≅ ℚ̄_ℓ` (`unitEndRingEquiv`). -/
theorem trace_globalOperator_eq_sum_trace_stalkFrobenius_padicAlgCl [IsAlgClosed k]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (hm : 1 ≤ m)
    [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        K.carrier)] :
    haveI := hΦ.isFinite m
    haveI := hΦ.isUniversalHomeomorphism m
    unitEndRingEquiv ℓ k (trace (K.globalOperator m)) =
      ∑ x : FixedPoint Φ m, unitEndRingEquiv ℓ k (trace (K.stalkFrobenius m x.1 x.2)) := by
  rw [trace_globalOperator_eq_sum_trace_stalkFrobenius hΦ K m hm, map_sum]

/-! ### Counting points -/

namespace WeilBoundedConstructible

variable (ℓ Φ) in
/-- The *constant Weil object* `ℚ̄_ℓ,X` for `Φ`: the unit `ℚ̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with the
structure isomorphism `LΦ^* ℚ̄_ℓ,X ≅ ℚ̄_ℓ,X` of the monoidal functor `LΦ^*`. -/
noncomputable def unit : WeilBoundedConstructible ℓ Φ :=
  IsoAlgebra.mk (𝟙_ _)
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)).symm

/-- The unit comparisons of derived pullbacks along equal morphisms agree up to the cast. -/
lemma eqToHom_comp_εIso_inv {Y Z : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] {f f' : Y ⟶ Z} (e : f = f')
    (h : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj (𝟙_ _) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').obj (𝟙_ _)) :
    eqToHom h ≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          f')).inv =
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        f)).inv := by
  subst e
  rw [eqToHom_refl, Category.id_comp]

/-- The composition isomorphism of derived pullbacks, through a cast `f' = f ≫ g`, is compatible
with the unit comparisons. -/
lemma eqToHom_comp_upperStarComp_hom_app_unit {Y Z W : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    {f' : Y ⟶ W} (f : Y ⟶ Z) (g : Z ⟶ W) (e : f' = f ≫ g)
    (h : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').obj (𝟙_ _) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g)).obj (𝟙_ _)) :
    eqToHom h ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app
          (𝟙_ _) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            g)).inv ≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          f)).inv =
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        f')).inv := by
  rw [boundedConstructibleUpperStarComp_hom_app_unit, eqToHom_comp_εIso_inv e]

/-- The iterated structure isomorphisms of the constant Weil object are the inverses of the unit
comparisons of the pullbacks `LΦ_m^*`. -/
lemma unit_iterateStr_hom (m : ℕ) :
    ((unit ℓ Φ).iterateStr m).hom =
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (frobeniusIterate Φ m))).inv := by
  induction m with
  | zero => exact boundedConstructibleUpperStarId_hom_app_unit _ ℓ X
  | succ m ih =>
    simp only [iterateStr, Iso.trans_hom, eqToIso.hom, Iso.app_hom, Functor.mapIso_hom, ih]
    exact eqToHom_comp_upperStarComp_hom_app_unit _ _ (frobeniusIterate_succ Φ m) _

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The computation behind `stalkFrobenius_unit`, for an abstract family of pullback functors
(kept opaque so that the computation is cheap), on an object `K` equal to the unit `I_X`: the
local Frobenius composite of the inverse unit comparisons `ε` is the identity. -/
lemma stalkFrobenius_unit_aux {𝒞 : Type*} [Category 𝒞] {W Y : 𝒞} {DW DY : Type*} [Category DW]
    [Category DY] (UWW : (W ⟶ W) → DW ⥤ DW) (UWY : (W ⟶ Y) → DY ⥤ DW)
    (UYY : (Y ⟶ Y) → DY ⥤ DY)
    (cWW : ∀ (a : W ⟶ W) (b : W ⟶ Y), UWY (a ≫ b) ≅ UWY b ⋙ UWW a)
    (cWY : ∀ (a : W ⟶ Y) (b : Y ⟶ Y), UWY (a ≫ b) ≅ UYY b ⋙ UWY a)
    (ιW : UWW (𝟙 W) ≅ 𝟭 DW) (IW : DW) (IY : DY) (εWW : ∀ a, (UWW a).obj IW ⟶ IW)
    (εWY : ∀ a, (UWY a).obj IY ⟶ IW) (εYY : ∀ a, (UYY a).obj IY ⟶ IY) [∀ a, IsIso (εWY a)]
    (hid : ιW.hom.app IW = εWW (𝟙 W))
    (hcWW : ∀ a b, (cWW a b).hom.app IY ≫ (UWW a).map (εWY b) ≫ εWW a = εWY (a ≫ b))
    (hcWY : ∀ a b, (cWY a b).hom.app IY ≫ (UWY a).map (εYY b) ≫ εWY a = εWY (a ≫ b))
    {x : W ⟶ Y} {M : Y ⟶ Y} (hx : x ≫ M = x) {K : DY} (hK : K = IY)
    (e₁ : (UWY (𝟙 W ≫ x)).obj K = (UWY (x ≫ M)).obj K)
    (a₁ : (UWY x).obj ((UYY M).obj K) = (UWY x).obj ((UYY M).obj IY))
    (a₂ : (UWY x).obj IY = (UWY x).obj K) :
    ιW.inv.app ((UWY x).obj K) ≫ (cWW (𝟙 W) x).inv.app K ≫ eqToHom e₁ ≫
      (cWY x M).hom.app K ≫ eqToHom a₁ ≫ (UWY x).map (εYY M) ≫ eqToHom a₂ = 𝟙 _ := by
  have hcast : ∀ {f f' : W ⟶ Y} (e : f = f') (h : (UWY f).obj IY = (UWY f').obj IY),
      eqToHom h ≫ εWY f' = εWY f := by
    rintro f _ rfl h
    rw [eqToHom_refl, Category.id_comp]
  subst hK
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← cancel_mono (εWY x)]
  erw [Category.id_comp (εWY x)]
  simp only [Category.assoc]
  rw [hcWY, hcast ((Category.id_comp x).trans hx.symm), ← hcWW (𝟙 W) x,
    Iso.inv_hom_id_app_assoc, ← NatTrans.naturality_assoc, Functor.id_map, ← hid,
    Iso.inv_hom_id_app, Category.comp_id]

/-- The local Frobenii of the constant Weil object are the identity: `tr(F_{x,m} | ℚ̄_ℓ) = 1`. -/
theorem stalkFrobenius_unit (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) :
    (unit ℓ Φ).stalkFrobenius m x hx = 𝟙 _ := by
  rw [stalkFrobenius, frobenius_hom]
  dsimp only [iterateStalk, weilStalk]
  rw [weilUpperStar_obj_str, iterate_str]
  simp only [weilUpperStarComparison,
    boundedConstructiblePullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv, Functor.map_comp,
    eqToHom_map, NatTrans.comp_app, eqToHom_app, Category.assoc, unit_iterateStr_hom]
  exact stalkFrobenius_unit_aux
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)) (𝟙_ _) (𝟙_ _)
    (fun a ↦ (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)).inv)
    (fun a ↦ (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)).inv)
    (fun a ↦ (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)).inv)
    (boundedConstructibleUpperStarId_hom_app_unit _ ℓ _)
    (fun a b ↦ boundedConstructibleUpperStarComp_hom_app_unit _ ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp_hom_app_unit _ ℓ a b) hx (iterate_carrier _ m)
    _ _ _

end WeilBoundedConstructible

/-- **Counting points** (blueprint `cor-trf-point-counting`): the trace of the global operator
`F_{c,m}` on `RΓ_c(X, ℚ̄_ℓ)` is the number of points of `X₀` rational over `𝔽_{q^m}`, the
number of rational points of `X` fixed by `Φ_m`. -/
theorem trace_globalOperator_unit_eq_card [IsAlgClosed k] [IsSeparated f₀]
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] (hΦ : IsModelFrobenius Φ f₀ p) (m : ℕ)
    (hm : 1 ≤ m) [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        (WeilBoundedConstructible.unit ℓ Φ).carrier)] :
    haveI := hΦ.isFinite m
    haveI := hΦ.isUniversalHomeomorphism m
    trace ((WeilBoundedConstructible.unit ℓ Φ).globalOperator m) =
      (Fintype.card (FixedPoint Φ m) :
        End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
