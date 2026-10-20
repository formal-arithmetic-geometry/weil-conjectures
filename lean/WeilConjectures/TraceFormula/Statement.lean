/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.TraceFormula.Basic

/-!

# The statement of the Grothendieck–Lefschetz trace formula

Let `k₀ = 𝔽_q` be a finite field, `k` an algebraically closed field containing `k₀`, `X₀` a
separated `k₀`-scheme of finite type and `X = X₀ ×_{k₀} k`, with its model Frobenius `Φ = F₀ × 𝟙`
(`ProEtale.CondensedRing.IsModelFrobenius`). Let `(K, φ)` be a Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`
for `Φ`, that is `φ : LΦ^* K ≅ K` (`ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd`). For
every `m ≥ 1`,
```
tr(F_{c,m} | RΓ_c(X, K)) = ∑_{x ∈ X(k), Φ_m(x) = x} tr(F_{x,m} | K_x̄)
```
(`ProEtale.CondensedRing.trace_globalOperator_eq_sum_trace_stalkFrobenius`, blueprint
`thm-trf-grothendieck-lefschetz-finite-ring` and `thm-trf-grothendieck-lefschetz-qbar`), where:

* `(K, φ_m)` is the iterated Weil object for `Φ_m = Φ^m`
  (`ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd.iterate`);
* `F_{c,m}` is the Frobenius of `RΓ_c(X, (K, φ_m)) = Ra_{X!}(K, φ_m)`, a Weil object for the
  identity of the base point `s = Spec k`
  (`ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd.globalOperator`);
* `x` runs over the rational points `x : s ⟶ X` fixed by `Φ_m`
  (`ProEtale.CondensedRing.FixedPoint`), which are the points of `X₀` rational over `𝔽_{q^m}`;
* `F_{x,m}` is the Frobenius of the stalk `Lx^*(K, φ_m)`, again a Weil object for the identity
  of `s` (`ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd.stalkFrobenius`);
* both traces are categorical traces (`CategoryTheory.MonoidalCategory.trace`) in the symmetric
  monoidal category `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`, with values in `End (ℚ̄_ℓ,s)`, which is `ℚ̄_ℓ` since `k` is
  separably closed. They are taken for chosen duals of `RΓ_c(X, K)` and of the stalks `K_x̄`;
  the trace does not depend on this choice.

## Main definitions

- `ProEtale.CondensedRing.weilStalk`: the stalk `Lx^*` of Weil objects at a fixed point `x`.
- `ProEtale.CondensedRing.weilCompactCohomology`: the compactly supported cohomology
  `RΓ_c(X, -) = Ra_{X!}` of Weil objects, for `Φ` a finite universal homeomorphism.
- `ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd.stalkFrobenius`,
  `ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd.globalOperator`: the local Frobenius
  `F_{x,m}` and the global operator `F_{c,m}` (blueprint `sk-d-weil`,
  `def-trf-frobenius-coefficient-morphism`).
- `ProEtale.CondensedRing.IsModelFrobenius`: `Φ` is the base change of the `q`-power Frobenius
  of a model `X₀` over `k₀` (blueprint `sk-d-weil`).

## Main statements

- `ProEtale.CondensedRing.trace_globalOperator_eq_sum_trace_stalkFrobenius`: the
  Grothendieck–Lefschetz trace formula.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### The stalk at a fixed point -/

section Stalk

variable (Φ : X ⟶ X)

/-- The *stalk functor* at a rational point `x` fixed by `Φ`: the derived pullback `Lx^*`, from
Weil objects for `Φ` on `X` to Weil objects for the identity of the base point `s`. The structure
isomorphism of `Lx^* K` is
```
L(𝟙 s)^* Lx^* K ≅ Lx^* LΦ^* K --Lx^* φ--> Lx^* K,
```
the first isomorphism being the comparison of the pullbacks along the square `𝟙 s ≫ x = x ≫ Φ`.
-/
noncomputable def weilStalk (x : RationalPoint X) (hx : x ≫ Φ = x) :
    WeilBoundedConstructibleOfEnd ℓ Φ ⥤ WeilBoundedConstructibleOfEnd ℓ (𝟙 (point k)) :=
  IsoAlgebra.mapOfNatIso
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      (CommSq.mk (show 𝟙 (point k) ≫ x = x ≫ Φ by rw [Category.id_comp, hx]))).symm

@[simp]
lemma weilStalk_obj_carrier (x : RationalPoint X) (hx : x ≫ Φ = x)
    (K : WeilBoundedConstructibleOfEnd ℓ Φ) :
    ((weilStalk ℓ Φ x hx).obj K).carrier =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier :=
  rfl

end Stalk

/-! ### Compactly supported cohomology -/

section CompactCohomology

variable (Φ : X ⟶ X) [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]

/-- The Frobenius comparison `Ra_{X!} ⋙ L(𝟙 s)^* ≅ LΦ^* ⋙ Ra_{X!}` for a finite universal
homeomorphism `Φ` of `X` over `Spec k`, with `a_X : X ⟶ s` the structure morphism: the composite
```
Ra_{X!} ⋙ L(𝟙 s)^* ≅ Ra_{X!} ≅ LΦ^* ⋙ RΦ_* ⋙ Ra_{X!} ≅ LΦ^* ⋙ RΦ_! ⋙ Ra_{X!}
  ≅ LΦ^* ⋙ R(Φ ≫ a_X)_! = LΦ^* ⋙ Ra_{X!}
```
of the identity isomorphism of `L(𝟙 s)^*`, the unit of `LΦ^* ⊣ RΦ_*` (an isomorphism by
topological invariance), the identification `RΦ_! ≅ RΦ_*` for the proper `Φ` and the composition
isomorphism of the lower shriek (blueprint `sk-d-weil-push`). -/
noncomputable def compactCohomologyFrobeniusComparison :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k)) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  have := isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ Φ
  Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarId _ ℓ (point k)) ≪≫
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ Φ).unit) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Φ).symm _ ≪≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ Φ (toPoint X)).symm ≪≫
        eqToIso (by rw [comp_toPoint]))

/-- The *compactly supported cohomology* `RΓ_c(X, -) = Ra_{X!}` of Weil objects for a finite
universal homeomorphism `Φ`: a Weil object `(K, φ)` for `Φ` is sent to `Ra_{X!} K` with the
structure isomorphism
`L(𝟙 s)^* Ra_{X!} K ≅ Ra_{X!} LΦ^* K --Ra_{X!} φ--> Ra_{X!} K`
of `compactCohomologyFrobeniusComparison`, a Weil object for the identity of the base point
(blueprint `def-trf-weil-shriek-pushforward`). -/
noncomputable def weilCompactCohomology :
    WeilBoundedConstructibleOfEnd ℓ Φ ⥤ WeilBoundedConstructibleOfEnd ℓ (𝟙 (point k)) :=
  IsoAlgebra.mapOfNatIso (compactCohomologyFrobeniusComparison ℓ Φ)

@[simp]
lemma weilCompactCohomology_obj_carrier (K : WeilBoundedConstructibleOfEnd ℓ Φ) :
    ((weilCompactCohomology ℓ Φ).obj K).carrier =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier :=
  rfl

end CompactCohomology

/-! ### The Frobenius operators -/

namespace WeilBoundedConstructibleOfEnd

variable {ℓ} {Φ : X ⟶ X}

/-- The *local Frobenius* `F_{x,m}` of a Weil object `(K, φ)` at a rational point `x` fixed by
`Φ_m`: the Frobenius of the stalk at `x` of the iterate `(K, φ_m)`, an automorphism of the
geometric stalk `K_x̄ = Lx^* K`. Explicitly it is the composite
```
Lx^* K ≅ L(𝟙 s)^* Lx^* K ≅ Lx^* LΦ_m^* K --Lx^* φ_m--> Lx^* K
```
(blueprint `sk-d-weil`). -/
noncomputable def stalkFrobenius (K : WeilBoundedConstructibleOfEnd ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier :=
  ((weilStalk ℓ (frobeniusIterate Φ m) x hx).obj (K.iterate m)).frobenius.hom

/- The carriers `(K.iterate m).carrier` and `K.carrier` are defeq, but the kernel check of this
defeq times out, so the definition casts along `iterate_carrier`. -/
/-- The *global operator* `F_{c,m}` of a Weil object `(K, φ)` on its compactly supported
cohomology `RΓ_c(X, K) = Ra_{X!} K`, for `Φ_m` a finite universal homeomorphism: the Frobenius
of the Weil object `RΓ_c(X, (K, φ_m))` for the identity of the base point. Explicitly it is
```
RΓ_c(X, K) ≅ L(𝟙 s)^* Ra_{X!} K ≅ Ra_{X!} LΦ_m^* K --Ra_{X!} φ_m--> Ra_{X!} K
```
(blueprint `def-trf-frobenius-coefficient-morphism` and
`lem-trf-frobenius-operator-compact-description`). -/
noncomputable def globalOperator (K : WeilBoundedConstructibleOfEnd ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier :=
  eqToHom (by rw [weilCompactCohomology_obj_carrier, iterate_carrier]) ≫
    ((weilCompactCohomology ℓ (frobeniusIterate Φ m)).obj (K.iterate m)).frobenius.hom ≫
    eqToHom (by rw [weilCompactCohomology_obj_carrier, iterate_carrier])

end WeilBoundedConstructibleOfEnd

/-! ### The model Frobenius -/

section Model

variable {ℓ} (Φ : X ⟶ X)

/-- The rational points `x : s ⟶ X` fixed by the iterate `Φ_m`. -/
abbrev FixedPoint (m : ℕ) : Type u :=
  {x : RationalPoint X // x ≫ frobeniusIterate Φ m = x}

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  (f₀ : X₀ ⟶ Spec (.of k₀)) (p : X.left ⟶ X₀)

/-- The endomorphism `Φ` of `X` over `Spec k` is the *model Frobenius* of a model `X₀` of `X`
over the finite field `k₀ ⊆ k`: the square
```
     X ───p───▶ X₀
     │          │
  a_X│          │f₀
     ▼          ▼
  Spec k ───▶ Spec k₀
```
is cartesian, so that `X = X₀ ×_{k₀} k`, and `Φ = F₀ × 𝟙` is the base change of the
`#k₀`-power Frobenius `F₀` of `X₀`, that is `Φ ≫ p = p ≫ F₀`. Since the square is cartesian, the
two equations `Φ ≫ p = p ≫ F₀` and `Φ ≫ a_X = a_X` determine `Φ` (blueprint `sk-d-weil`). -/
structure IsModelFrobenius : Prop where
  /-- `X` is the base change `X₀ ×_{k₀} k`. -/
  isPullback : IsPullback p X.hom f₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))
  /-- `Φ` is the base change of the `#k₀`-power Frobenius of `X₀`. -/
  exists_isFrobenius : ∃ F₀ : X₀ ⟶ X₀, F₀.IsFrobenius (Nat.card k₀) ∧ Φ.left ≫ p = p ≫ F₀

variable {Φ f₀ p}

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- The iterates `Φ_m` of the model Frobenius are universal homeomorphisms (blueprint
`i-relative-frob`, Step 2). -/
lemma IsModelFrobenius.isUniversalHomeomorphism (hΦ : IsModelFrobenius Φ f₀ p) (m : ℕ) :
    IsUniversalHomeomorphism (frobeniusIterate Φ m).left := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  have : IsUniversalHomeomorphism Φ.left :=
    hF₀.isUniversalHomeomorphism_of_isPullback hΦ.isPullback (Over.w Φ) hp
  induction m with
  | zero => exact inferInstanceAs (IsUniversalHomeomorphism (𝟙 X.left))
  | succ m ih =>
    rw [frobeniusIterate_succ, Over.comp_left]
    infer_instance

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- The iterates `Φ_m` of the model Frobenius of a model locally of finite type are finite
(blueprint `i-relative-frob`, Step 1). -/
lemma IsModelFrobenius.isFinite [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    (m : ℕ) : IsFinite (frobeniusIterate Φ m).left := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  have : IsFinite Φ.left := hF₀.isFinite_of_isPullback hΦ.isPullback (Over.w Φ) hp
  induction m with
  | zero => exact inferInstanceAs (IsFinite (𝟙 X.left))
  | succ m ih =>
    rw [frobeniusIterate_succ, Over.comp_left]
    infer_instance

end Model

/-! ### The trace formula -/

variable {ℓ} {Φ : X ⟶ X} {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}

attribute [local instance] boundedConstructibleBraiding in
/-- **The Grothendieck–Lefschetz trace formula** (blueprint
`thm-trf-grothendieck-lefschetz-finite-ring`, `thm-trf-grothendieck-lefschetz-qbar`): let
`X = X₀ ×_{k₀} k` be the base change of a separated `k₀`-scheme of finite type to an
algebraically closed field `k`, with model Frobenius `Φ`, and let `(K, φ)` be a Weil object of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `Φ`. For every `m ≥ 1`,
```
tr(F_{c,m} | RΓ_c(X, K)) = ∑_{x ∈ X(k), Φ_m(x) = x} tr(F_{x,m} | K_x̄),
```
where `F_{c,m}` is the Frobenius of the compactly supported cohomology `RΓ_c(X, (K, φ_m))` and
`F_{x,m}` the Frobenius of the stalk of `(K, φ_m)` at `x`, both Weil objects for the identity of
the base point. The traces are taken in `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` for chosen right duals of `RΓ_c(X, K)` and
of the stalks. -/
theorem trace_globalOperator_eq_sum_trace_stalkFrobenius [IsAlgClosed k] [IsSeparated f₀]
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructibleOfEnd ℓ Φ) (m : ℕ) (hm : 1 ≤ m)
    [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        K.carrier)] :
    haveI := hΦ.isFinite m
    haveI := hΦ.isUniversalHomeomorphism m
    trace (K.globalOperator m) = ∑ x : FixedPoint Φ m, trace (K.stalkFrobenius m x.1 x.2) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
