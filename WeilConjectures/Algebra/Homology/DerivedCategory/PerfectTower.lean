/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Algebra.Homology.MinimalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectTrace

/-!
# Normalized towers of perfect complexes over an adic ring

Let `R` be a commutative ring with a tower of quotients `π n : R →+* A n` and transitions
`ρ n : A (n + 1) →+* A n` (the intended case is `R = 𝒪_E` and `A n = 𝒪_E ⧸ ϖⁿ⁺¹`). A
*normalized tower of perfect complexes* (`ModuleCat.NormalizedPerfectTower`) is a family of
perfect complexes `Q n ∈ D(A n)` with maps `Q (n + 1) ⟶ Res Q n` exhibiting `Q n` as the
derived base change `Q (n + 1) ⊗ᴸ_{A (n + 1)} A n`. Its restrictions of scalars form a tower
`n ↦ Res Q n` in `D(R)`.

When the `A n` are local and `R` is complete and separated for the tower, the derived limit
`P = R lim_n Q n` of this tower is represented by a bounded complex of finite free
`R`-modules and reduces to the levels, `P ⊗ᴸ_R A n ≅ Q n` (Stacks, Tag 09AW). A compatible
family of endomorphisms `f n` of the `Q n` lifts to an endomorphism `V` of `P`, and the
categorical trace of any lift reduces to the traces of the `f n`. This is items (2) and (4) of
blueprint `prop-trf-adic-coefficient-morphism-systems`, and the realization over a point of
blueprint `sk-prop-trace-adic` (ii).

## Main definitions

- `ModuleCat.NormalizedPerfectTower`: a normalized tower of perfect complexes.
- `ModuleCat.NormalizedPerfectTower.restrict`: the tower `n ↦ Res Q n` in `D(R)`.
- `ModuleCat.NormalizedPerfectTower.IsCompatible`: compatible families of endomorphisms.
- `ModuleCat.NormalizedPerfectTower.IsLift`: lifts of a compatible family to the derived limit.

## Main results

- `ModuleCat.NormalizedPerfectTower.exists_iso_Q_obj_of_isHomotopyLimit`: the derived limit is
  represented by a bounded complex of finite free `R`-modules.
- `ModuleCat.NormalizedPerfectTower.isDerivedBaseChange_π_app`: the legs `P ⟶ Res Q n` of the
  derived limit exhibit `Q n` as `P ⊗ᴸ_R A n`.
- `ModuleCat.NormalizedPerfectTower.exists_isLift`: compatible families lift.
- `ModuleCat.NormalizedPerfectTower.exists_trace_eq_of_isLift`,
  `ModuleCat.NormalizedPerfectTower.trace_eq_of_isLift`: the trace of a lift reduces to the
  traces of the family, and does not depend on the lift.

## Implementation notes

Derived base change is expressed by universal arrows (`ModuleCat.IsDerivedBaseChange`): the
leg `pr_n : P ⟶ Res Q n` is the blueprint's `π_n : P ⊗ᴸ A n ⟶ Q n` read through the adjunction
between derived base change and restriction of scalars. For the same reason the blueprint's
condition `π_n ∘ (V ⊗ᴸ A n) = f n ∘ π_n` on a lift `V` is the condition
`V ≫ pr_n = pr_n ≫ Res (f n)` of `ModuleCat.NormalizedPerfectTower.IsLift`: `V ⊗ᴸ A n` is the
unique endomorphism `g` of `P ⊗ᴸ A n` with `pr_n ≫ Res g = V ≫ pr_n`.

The proof follows the blueprint. Each `Q n` has a minimal model, a bounded complex of finite
free `A n`-modules whose differentials vanish modulo the maximal ideal
(`CochainComplex.exists_homotopyEquiv_isMinimal`); quasi-isomorphisms between minimal models are
isomorphisms (`CochainComplex.isIso_of_quasiIso_of_isMinimal`). In bases, the models are given by
matrices, and lifting invertible matrices along `A (n + 1) ⟶ A n` strictifies the tower into a
tower of matrix complexes whose transitions are the reductions of the entries. Their entrywise
limit is the bounded free complex over `R` representing `P`
(`DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi`). Lifts are built by choosing chain-level
representatives level by level and correcting them by lifted homotopies, and traces are
alternating sums of matrix traces
(`DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

namespace ModuleCat

variable {R : Type u} [CommRing R] {A : ℕ → Type u} [∀ n, CommRing (A n)]
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [∀ n, HasDerivedCategory.{u} (ModuleCat.{u} (A n))]
  {π : ∀ n, R →+* A n} {ρ : ∀ n, A (n + 1) →+* A n}

variable (π ρ) in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems`: a *normalized tower of perfect
complexes* over the tower of rings `A n` (with `π n : R →+* A n` and transitions
`ρ n : A (n + 1) →+* A n`, `ρ n ∘ π (n + 1) = π n`) is a family of perfect complexes
`Q n ∈ D(A n)` together with maps `Q (n + 1) ⟶ Res Q n` exhibiting `Q n` as the derived base
change `Q (n + 1) ⊗ᴸ_{A (n + 1)} A n`. -/
structure NormalizedPerfectTower (hρ : ∀ n, π n = (ρ n).comp (π (n + 1))) where
  /-- The level `Q n ∈ D(A n)`. -/
  obj (n : ℕ) : DerivedCategory (ModuleCat.{u} (A n))
  /-- Each level is perfect. -/
  isPerfect (n : ℕ) : (obj n).IsPerfect
  /-- The transition `Q (n + 1) ⟶ Res Q n`. -/
  map (n : ℕ) : obj (n + 1) ⟶ (derivedRestrictScalars (ρ n)).obj (obj n)
  /-- The transition exhibits `Q n` as `Q (n + 1) ⊗ᴸ_{A (n + 1)} A n`. -/
  isDerivedBaseChange (n : ℕ) : IsDerivedBaseChange (map n)

namespace NormalizedPerfectTower

variable {hρ : ∀ n, π n = (ρ n).comp (π (n + 1))} (T : NormalizedPerfectTower π ρ hρ)

/-- The tower `n ↦ Res Q n` in `D(R)` of the restrictions of scalars of the levels, with the
restricted transitions. -/
noncomputable def restrict : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Functor.ofOpSequence (X := fun n ↦ (derivedRestrictScalars (π n)).obj (T.obj n)) fun n ↦
    (derivedRestrictScalars (π (n + 1))).map (T.map n) ≫
      (derivedRestrictScalarsCompIso (hρ n)).hom.app (T.obj n)

@[simp]
lemma restrict_obj (n : ℕ) :
    T.restrict.obj (op n) = (derivedRestrictScalars (π n)).obj (T.obj n) :=
  rfl

lemma restrict_map_succ (n : ℕ) :
    T.restrict.map (homOfLE n.le_succ).op =
      (derivedRestrictScalars (π (n + 1))).map (T.map n) ≫
        (derivedRestrictScalarsCompIso (hρ n)).hom.app (T.obj n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- A family of endomorphisms `f n` of the levels is *compatible* if `f n` is the base change
of `f (n + 1)`: `f (n + 1)` followed by the transition is the transition followed by `f n`. -/
def IsCompatible (f : ∀ n, T.obj n ⟶ T.obj n) : Prop :=
  ∀ n, T.map n ≫ (derivedRestrictScalars (ρ n)).map (f n) = f (n + 1) ≫ T.map n

/-- An endomorphism `V` of the point of a cone `c` over `T.restrict` is a *lift* of a family
`f n` of endomorphisms of the levels if `V ≫ pr_n = pr_n ≫ Res (f n)` for the legs
`pr_n : c.pt ⟶ Res Q n`. When the legs exhibit `Q n` as `c.pt ⊗ᴸ_R A n`
(`ModuleCat.NormalizedPerfectTower.isDerivedBaseChange_π_app`), this says that `f n` is
`V ⊗ᴸ_R A n` read through `pr_n`. -/
def IsLift (c : Cone T.restrict) (f : ∀ n, T.obj n ⟶ T.obj n) (V : c.pt ⟶ c.pt) : Prop :=
  ∀ n, V ≫ c.π.app (op n) = c.π.app (op n) ≫ (derivedRestrictScalars (π n)).map (f n)

variable [∀ n, IsLocalRing (A n)] (hπ : ∀ n, Function.Surjective (π n)) {ϖ : R}
  (hker : ∀ n, RingHom.ker (π n) = Ideal.span {ϖ ^ (n + 1)})
  (hcomplete : ∀ x : ∀ n, A n, (∀ n, ρ n (x (n + 1)) = x n) → ∃ r : R, ∀ n, π n r = x n)
  (hsep : ∀ r : R, (∀ n, π n r = 0) → r = 0)
  {c : Cone T.restrict} (hc : IsHomotopyLimit c)

include hπ hker hcomplete hsep hc in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (2), Stacks Tag 09AW: the derived
limit `P = R lim_n Res Q n` of a normalized tower of perfect complexes is represented by a
bounded complex of finite free `R`-modules. -/
theorem exists_iso_Q_obj_of_isHomotopyLimit :
    ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ), M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
      (∀ i, Module.Free R (M.X i) ∧ Module.Finite R (M.X i)) ∧
      Nonempty (c.pt ≅ DerivedCategory.Q.obj M) :=
  sorry

include hπ hker hcomplete hsep hc in
/-- The derived limit of a normalized tower of perfect complexes is perfect. -/
theorem isPerfect_pt : c.pt.IsPerfect := by
  obtain ⟨M, a, b, ha, hb, hM, ⟨e⟩⟩ := T.exists_iso_Q_obj_of_isHomotopyLimit hπ hker hcomplete
    hsep hc
  exact ⟨M, a, b, ha, hb, fun i ↦ ⟨haveI := (hM i).1; Module.Projective.of_free, (hM i).2⟩, ⟨e⟩⟩

include hπ hker hcomplete hsep hc in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (2): every leg `pr_n : P ⟶ Res Q n`
of the derived limit exhibits `Q n` as `P ⊗ᴸ_R A n`, i.e. the adjoint map
`π_n : P ⊗ᴸ_R A n ⟶ Q n` is an isomorphism. -/
theorem isDerivedBaseChange_π_app (n : ℕ) :
    IsDerivedBaseChange (f := π n) (c.π.app (op n)) :=
  sorry

include hπ hker hcomplete hsep hc in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (2): every compatible family of
endomorphisms of the levels lifts to an endomorphism of the derived limit. -/
theorem exists_isLift {f : ∀ n, T.obj n ⟶ T.obj n} (hf : T.IsCompatible f) :
    ∃ V : c.pt ⟶ c.pt, T.IsLift c f V :=
  sorry

section Trace

variable [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
  [∀ n, Abelian.HasFunctorialFlatResolution (ModuleCat.{u} (A n))]
  [BraidedCategory (DerivedCategory (ModuleCat.{u} R))]
  [∀ n, BraidedCategory (DerivedCategory (ModuleCat.{u} (A n)))]
  (hβ : (β_ ((𝟙_ (DerivedCategory (ModuleCat.{u} R)))⟦(1 : ℤ)⟧)
    ((𝟙_ (DerivedCategory (ModuleCat.{u} R)))⟦(1 : ℤ)⟧)).hom = -𝟙 _)
  (hβA : ∀ n, (β_ ((𝟙_ (DerivedCategory (ModuleCat.{u} (A n))))⟦(1 : ℤ)⟧)
    ((𝟙_ (DerivedCategory (ModuleCat.{u} (A n))))⟦(1 : ℤ)⟧)).hom = -𝟙 _)
  [HasRightDual c.pt] [∀ n, HasRightDual (T.obj n)]

include hπ hker hcomplete hsep hc hβ hβA in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (4): the categorical trace of a lift
`V` of a compatible family `f` reduces to the traces of the `f n`: there is `r : R` with
`tr_R(V ∣ P) = r` and `tr_{A n}(f n ∣ Q n) = r mod ϖⁿ⁺¹` for all `n`. -/
theorem exists_trace_eq_of_isLift {f : ∀ n, T.obj n ⟶ T.obj n} (hf : T.IsCompatible f)
    {V : c.pt ⟶ c.pt} (hV : T.IsLift c f V) :
    ∃ r : R,
      MonoidalCategory.trace V = algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u} R)))) r ∧
      ∀ n, MonoidalCategory.trace (f n) =
        algebraMap (A n) (End (𝟙_ (DerivedCategory (ModuleCat.{u} (A n))))) (π n r) :=
  sorry

include hπ hker hcomplete hsep hc hβ hβA in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (4): the categorical trace of a lift
of a compatible family does not depend on the lift. -/
theorem trace_eq_of_isLift {f : ∀ n, T.obj n ⟶ T.obj n} (hf : T.IsCompatible f)
    {V V' : c.pt ⟶ c.pt} (hV : T.IsLift c f V) (hV' : T.IsLift c f V') :
    MonoidalCategory.trace V = MonoidalCategory.trace V' :=
  sorry

end Trace

end NormalizedPerfectTower

end ModuleCat
