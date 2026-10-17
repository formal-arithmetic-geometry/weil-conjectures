/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.ReductionTower
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.Amplification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BoundedConstructibleTower
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsConstructible

/-!
# Witness compatibility and tower preservation for a cartesian square

Let `A` be a commutative ring and `ϖ ∈ A` a nonzerodivisor generating the ideal `I`, and put
`P_n = A ⧸ Iⁿ`. For a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

this file defines the two conditions of blueprint `def-weil-pbc-witness-compatibility` and
`def-weil-pbc-tower-preservation` on the four functors `Rf_*`, `Rf'_*`, `Lg^*`, `Lg'^*` between
the derived categories `D(-_proét, A)`:

* `WIT(□)` (`AlgebraicGeometry.ProEtale.WitnessCompatibility`): the four functors commute with
  the reductions `K ↦ K ⊗ᴸ P_n`, and carry objects of étale origin `ν^* L` to objects of étale
  origin;
* `TOW(□; c)` (`AlgebraicGeometry.ProEtale.TowerPreservation`): the four functors, applied
  levelwise, carry uniformly bounded constructible towers with levels in `[a, b]` to uniformly
  bounded constructible towers with levels in `[a, b + c]` (resp. `[a, b]` for the pullbacks).

The main result is `AlgebraicGeometry.ProEtale.preservation_of_witnessCompatibility`, the
argument of blueprint `prop-weil-pbc-preservation-constructible`: under `WIT(□)` and
`TOW(□; c)`, `Rf_*`, the completed pullbacks and `Rf'_*` preserve the bounded constructible
complete category `Dᵇc(-_proét, A)` with the expected reduction amplitudes.

## Implementation notes

As in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BoundedConstructibleComplete`,
the derived category `D(T_proét, A)` is that of sheaves of `A`-modules, and the finite-level
operations are recorded on the restrictions of scalars `Res M_n ∈ D(T_proét, A)` of the levels
`M_n ∈ D(T_proét, P_n)` of a tower: the levelwise image of a tower `M` under `Φ` is the tower
`n ↦ Φ (Res M_n)`. The normalization isomorphisms are thus taken along `A ⟶ P_n`, where `P_n`
is perfect over `A` (a cone of `ϖⁿ`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type (u + 1)} [CommRing A] (I : Ideal A)

set_option hygiene false in
/-- The derived category `D(T_proét, A)` of pro-étale sheaves of `A`-modules. -/
local notation "𝐃(" T ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- A functor `Φ : D(S_proét, A) ⥤ D(T_proét, A)` *commutes with the reductions*: for every
`K` and `n`, `Φ (K ⊗ᴸ A/Iⁿ) ≅ Φ(K) ⊗ᴸ A/Iⁿ`. -/
def CommutesWithReductions {S T : Scheme.{u}} (Φ : 𝐃(S) ⥤ 𝐃(T)) : Prop :=
  ∀ (K : 𝐃(S)) (n : ℕ), Nonempty (Φ.obj
    ((_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology S) I K).obj (op n)) ≅
      (_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology T) I
        (Φ.obj K)).obj (op n))

variable {I} in
/-- A triangulated `A`-linear functor commutes with the reductions for `I = (ϖ)`
(`DerivedCategory.nonempty_iso_map_derivedCompletionDiagram_obj`). -/
lemma commutesWithReductions_of_linear {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A)
    (hI : I = Ideal.span {ϖ}) {S T : Scheme.{u}} (Φ : 𝐃(S) ⥤ 𝐃(T)) [Φ.CommShift ℤ]
    [Φ.IsTriangulated] [Φ.Linear A] : CommutesWithReductions I Φ :=
  fun K n ↦ _root_.DerivedCategory.nonempty_iso_map_derivedCompletionDiagram_obj hϖ hI Φ K n

/-- A functor `Φ : D(S_proét, A) ⥤ D(T_proét, A)` *preserves constructible towers with shift
`c`*: for every normalized tower `M` on `S_proét` whose levels are bounded constructible with
cohomology in `[a, b]`, there is a normalized tower `N` on `T_proét` whose levels are bounded
constructible with cohomology in `[a, b + c]` and such that `Φ (Res M_n) ≅ Res N_n` for every
`n`. -/
def PreservesConstructibleTowers {S T : Scheme.{u}} (Φ : 𝐃(S) ⥤ 𝐃(T)) (c : ℕ) : Prop :=
  ∀ (M : Sheaf.NormalizedTower (Scheme.ProEt.topology S) I) (a b : ℤ),
    IsConstructibleInTower a b M → ∃ N : Sheaf.NormalizedTower (Scheme.ProEt.topology T) I,
      IsConstructibleInTower a (b + c) N ∧
        ∀ n : ℕ, Nonempty (Φ.obj (M.restrict.obj (op n)) ≅ N.restrict.obj (op n))

variable (A)

/-- Blueprint `def-weil-pbc-witness-compatibility`: the witness compatibility condition
`WIT(□)` for a cartesian square `□` (`sq : IsPullback g' f' f g`).

The four functors `Rf_*`, `Rf'_*`, `Lg^*`, `Lg'^*` commute with the normalizations
`K ↦ K ⊗ᴸ A/Iⁿ` (`AlgebraicGeometry.ProEtale.CommutesWithReductions`), and they carry étale-origin
witnesses to étale-origin witnesses: for a bounded below étale complex `L`, the image of
`ν^* L` is `ν^*` of the corresponding étale operation applied to `L`. -/
structure WitnessCompatibility {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (_sq : IsPullback g' f' f g) : Prop where
  lowerStar : CommutesWithReductions I (R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f))
  lowerStar' : CommutesWithReductions I (R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f'))
  upperStar : CommutesWithReductions I (L(ProEtale.upperStar (ModuleCat.{u + 1} A) g))
  upperStar' : CommutesWithReductions I (L(ProEtale.upperStar (ModuleCat.{u + 1} A) g'))
  lowerStar_etale (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    Nonempty ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj
        (D(ν^*(X)[ModuleCat.{u + 1} A]).obj K) ≅
      D(ν^*(Y)[ModuleCat.{u + 1} A]).obj ((R(Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj K))
  lowerStar'_etale
    (K : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    Nonempty ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f')).obj
        (D(ν^*(X')[ModuleCat.{u + 1} A]).obj K) ≅
      D(ν^*(Y')[ModuleCat.{u + 1} A]).obj ((R(Etale.lowerStar (ModuleCat.{u + 1} A) f')).obj K))
  upperStar_etale (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    Nonempty ((L(ProEtale.upperStar (ModuleCat.{u + 1} A) g)).obj
        (D(ν^*(Y)[ModuleCat.{u + 1} A]).obj K) ≅
      D(ν^*(Y')[ModuleCat.{u + 1} A]).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))
  upperStar'_etale
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    Nonempty ((L(ProEtale.upperStar (ModuleCat.{u + 1} A) g')).obj
        (D(ν^*(X)[ModuleCat.{u + 1} A]).obj K) ≅
      D(ν^*(X')[ModuleCat.{u + 1} A]).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategory.obj K))

/-- Blueprint `def-weil-pbc-tower-preservation`: the tower preservation condition `TOW(□; c)`
for a cartesian square `□` (`sq : IsPullback g' f' f g`).

The levelwise tower functors carry uniformly bounded constructible towers to uniformly bounded
constructible towers, compatibly with the amplitude containments of `AMP(□; c)`
(`def-weil-pbc-finite-level-amplification`): towers with levels in `[a, b]` go to towers with
levels in `[a, b + c]` under `Rf_*` and `Rf'_*`, and in `[a, b]` under `Lg^*` and `Lg'^*`
(`AlgebraicGeometry.ProEtale.PreservesConstructibleTowers`). -/
structure TowerPreservation {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (_sq : IsPullback g' f' f g) (c : ℕ) : Prop where
  lowerStar : PreservesConstructibleTowers I (R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)) c
  lowerStar' : PreservesConstructibleTowers I (R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f')) c
  upperStar : PreservesConstructibleTowers I (L(ProEtale.upperStar (ModuleCat.{u + 1} A) g)) 0
  upperStar' : PreservesConstructibleTowers I (L(ProEtale.upperStar (ModuleCat.{u + 1} A) g')) 0

variable {A I}

section Witness

variable {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A) (hI : I = Ideal.span {ϖ})

include hϖ hI in
/-- The witness compatibility `WIT(□)` holds for every cartesian square with `f` and `f'`
quasi-compact and quasi-separated, and `I = (ϖ)` for a nonzerodivisor `ϖ`: the four functors are
triangulated and `A`-linear, hence commute with the reductions
(`AlgebraicGeometry.ProEtale.commutesWithReductions_of_linear`), the direct images carry étale
origin witnesses along the comparison of direct images (`prop-weil-pbc-comparison-direct-image`,
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'`), and the pullbacks along the
comparison of pullbacks (`lem-weil-pbc-comparison-pullback`,
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComparisonIso`). -/
theorem witnessCompatibility_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f'] :
    WitnessCompatibility A I sq where
  lowerStar := commutesWithReductions_of_linear hϖ hI _
  lowerStar' := commutesWithReductions_of_linear hϖ hI _
  upperStar := commutesWithReductions_of_linear hϖ hI _
  upperStar' := commutesWithReductions_of_linear hϖ hI _
  lowerStar_etale K hK := ⟨((rightDerivedLowerStarComparisonIso' f _).app ⟨K, hK⟩).symm ≪≫
    D(ν^*(Y)[ModuleCat.{u + 1} A]).mapIso
      ((Etale.lowerStar _ f).rightDerivedFunctorPlusCompatibility.app ⟨K, hK⟩)⟩
  lowerStar'_etale K hK := ⟨((rightDerivedLowerStarComparisonIso' f' _).app ⟨K, hK⟩).symm ≪≫
    D(ν^*(Y')[ModuleCat.{u + 1} A]).mapIso
      ((Etale.lowerStar _ f').rightDerivedFunctorPlusCompatibility.app ⟨K, hK⟩)⟩
  upperStar_etale K hK := ⟨((leftDerivedUpperStarComparisonIso g A).app ⟨K, hK⟩).symm ≪≫
    D(ν^*(Y')[ModuleCat.{u + 1} A]).mapIso
      ((Etale.upperStar _ g).mapDerivedCategoryPlusCompatibility.app ⟨K, hK⟩)⟩
  upperStar'_etale K hK := ⟨((leftDerivedUpperStarComparisonIso g' A).app ⟨K, hK⟩).symm ≪≫
    D(ν^*(X')[ModuleCat.{u + 1} A]).mapIso
      ((Etale.upperStar _ g').mapDerivedCategoryPlusCompatibility.app ⟨K, hK⟩)⟩

end Witness

section Preservation

variable {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A) (hI : I = Ideal.span {ϖ}) [∀ n, Finite (A ⧸ I ^ n)]

include hϖ hI in
/-- The reductions `K ⊗ᴸ A/Iⁿ` of an object `K` whose reductions lie in `D_c^[a, b](T, A)` are
the restrictions of scalars `Res M_n` of the levels of a normalized tower `M` whose levels lie
in `D_c^[a, b](T, A ⧸ Iⁿ)`: the tower of derived base changes
(`DerivedCategory.exists_normalizedTower_restrict_iso`), whose levels are constructible since
restriction of scalars reflects constructibility
(`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleIn_of_derivedRestrictScalars_obj`). -/
lemma exists_isConstructibleInTower_restrict_iso {T : Scheme.{u}} {K : 𝐃(T)} {a b : ℤ}
    (hK : ∀ n : ℕ, DerivedCategory.constructibleIn (ModuleCat.{u + 1} A) T a b
      ((_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj
        (op n))) :
    ∃ M : Sheaf.NormalizedTower (Scheme.ProEt.topology T) I, IsConstructibleInTower a b M ∧
      ∀ n : ℕ, Nonempty (M.restrict.obj (op n) ≅
        (_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj
          (op n)) := by
  obtain ⟨M, hM⟩ := _root_.DerivedCategory.exists_normalizedTower_restrict_iso hϖ hI K
  refine ⟨M, fun n ↦ ?_, hM⟩
  obtain ⟨e⟩ := hM n
  exact DerivedCategory.constructibleIn_of_derivedRestrictScalars_obj (I ^ n)
    ((DerivedCategory.constructibleIn _ T a b).prop_of_iso e.symm (hK n))

include hϖ hI in
/-- A triangulated `A`-linear functor `Φ` preserves constructible towers with shift `c` as soon
as it carries the restrictions of scalars `Res M_n` of the levels of every tower with levels in
`D_c^[a, b]` into `D_c^[a, b + c](T, A)`. The output tower is the tower of reductions of
`Φ K`, where `K` is the derived limit of the tower
(`CategoryTheory.Sheaf.NormalizedTower.exists_derivedComplete_iso`): `Φ` commutes with the
reductions, so `Φ (Res M_n) ≅ Φ (K ⊗ᴸ A/Iⁿ) ≅ Φ K ⊗ᴸ A/Iⁿ`. -/
theorem preservesConstructibleTowers_of_linear {S T : Scheme.{u}} (Φ : 𝐃(S) ⥤ 𝐃(T))
    [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Linear A] (c : ℕ)
    (hΦ : ∀ (M : Sheaf.NormalizedTower (Scheme.ProEt.topology S) I) (a b : ℤ),
      IsConstructibleInTower a b M → ∀ n : ℕ,
        DerivedCategory.constructibleIn (ModuleCat.{u + 1} A) T a (b + c)
          (Φ.obj (M.restrict.obj (op n)))) :
    PreservesConstructibleTowers I Φ c := by
  intro M a b hM
  obtain ⟨K, -, hK⟩ := Sheaf.NormalizedTower.exists_derivedComplete_iso hϖ hI M
  have hK' : ∀ n : ℕ, DerivedCategory.constructibleIn (ModuleCat.{u + 1} A) T a (b + c)
      ((_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology T) I
        (Φ.obj K)).obj (op n)) := fun n ↦ by
    obtain ⟨e₁⟩ := hK n
    obtain ⟨e₂⟩ := commutesWithReductions_of_linear hϖ hI Φ K n
    exact (DerivedCategory.constructibleIn _ T a (b + c)).prop_of_iso
      (Φ.mapIso e₁.symm ≪≫ e₂) (hΦ M a b hM n)
  obtain ⟨N, hN, hN'⟩ := exists_isConstructibleInTower_restrict_iso hϖ hI hK'
  refine ⟨N, hN, fun n ↦ ?_⟩
  obtain ⟨e₁⟩ := hK n
  obtain ⟨e₂⟩ := commutesWithReductions_of_linear hϖ hI Φ K n
  obtain ⟨e₃⟩ := hN' n
  exact ⟨Φ.mapIso e₁.symm ≪≫ e₂ ≪≫ e₃.symm⟩

include hϖ hI in
/-- A functor `Φ` which commutes with the reductions and preserves constructible towers with
shift `c` carries objects whose reductions lie in `D_c^[a, b]` to objects whose reductions lie
in `D_c^[a, b + c]`: the reductions `K ⊗ᴸ A/Iⁿ` are the levels `Res M_n` of a constructible
tower (`AlgebraicGeometry.ProEtale.exists_isConstructibleInTower_restrict_iso`), so
`Φ K ⊗ᴸ A/Iⁿ ≅ Φ (Res M_n) ≅ Res N_n` for a constructible tower `N`. -/
lemma PreservesConstructibleTowers.constructibleIn_derivedCompletionDiagram_obj
    {S T : Scheme.{u}} {Φ : 𝐃(S) ⥤ 𝐃(T)} {c : ℕ} (hΦ : PreservesConstructibleTowers I Φ c)
    (hΦ' : CommutesWithReductions I Φ) {K : 𝐃(S)} {a b : ℤ}
    (hK : ∀ n : ℕ, DerivedCategory.constructibleIn (ModuleCat.{u + 1} A) S a b
      ((_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology S) I K).obj
        (op n))) (n : ℕ) :
    DerivedCategory.constructibleIn (ModuleCat.{u + 1} A) T a (b + c)
      ((_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology T) I
        (Φ.obj K)).obj (op n)) := by
  obtain ⟨M, hM, hM'⟩ := exists_isConstructibleInTower_restrict_iso hϖ hI hK
  obtain ⟨N, hN, hN'⟩ := hΦ M a b hM
  obtain ⟨e₁⟩ := hM' n
  obtain ⟨e₂⟩ := hΦ' K n
  obtain ⟨e₃⟩ := hN' n
  exact (DerivedCategory.constructibleIn _ T a (b + c)).prop_of_iso
    (e₃.symm ≪≫ Φ.mapIso e₁ ≪≫ e₂)
    (DerivedCategory.constructibleIn_derivedRestrictScalars_obj (I ^ n) (hN n))

include hϖ hI in
/-- The derived completion of an object whose reductions lie in `D_c^[a, b]` (a homotopy limit
of its reductions) is bounded constructible complete with reduction amplitude `[a, b]`: it is
derived complete and has the same reductions
(`DerivedCategory.derivedComplete_and_iso_of_isHomotopyLimit`). -/
lemma boundedConstructibleCompleteIn_of_isHomotopyLimit {T : Scheme.{u}} {K : 𝐃(T)} {a b : ℤ}
    (hK : ∀ n : ℕ, DerivedCategory.constructibleIn (ModuleCat.{u + 1} A) T a b
      ((_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology T) I K).obj
        (op n)))
    {c : Cone (_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology T) I K)}
    (hc : IsHomotopyLimit c) : DerivedCategory.boundedConstructibleCompleteIn I T a b c.pt := by
  obtain ⟨h₁, h₂⟩ := _root_.DerivedCategory.derivedComplete_and_iso_of_isHomotopyLimit hϖ hI K hc
  refine ⟨h₁, fun n ↦ ?_⟩
  obtain ⟨e⟩ := h₂ n
  exact (DerivedCategory.constructibleIn _ T a b).prop_of_iso e.symm (hK n)

include hϖ hI in
/-- Blueprint `prop-weil-pbc-preservation-constructible`, the formal argument: under the
witness compatibility `WIT(□)` and the tower preservation `TOW(□; c)`, for every
`K ∈ Dᵇc(X_proét, A)` whose reductions have the common interval `[a, b]`,
* `Rf_* K ∈ Dᵇc(Y_proét, A)` with reduction amplitude `[a, b + c]`;
* the completed pullback `Lg^*_comp Rf_* K` (a homotopy limit of the reductions of
  `Lg^* Rf_* K`) lies in `Dᵇc(Y'_proét, A)` with reduction amplitude `[a, b + c]`;
* the completed pullback `Lg'^*_comp K` lies in `Dᵇc(X'_proét, A)` with reduction amplitude
  `[a, b]`, and `Rf'_* Lg'^*_comp K ∈ Dᵇc(Y'_proét, A)` with reduction amplitude `[a, b + c]`.

The levelwise functors carry the constructible tower of reductions of `K` to constructible
towers (`TOW`), compatibly with the reductions (`WIT`); derived completeness of the direct
images holds since `Rf_*` is a right adjoint of the `A`-linear functor `Lf^*`
(`DerivedCategory.derivedComplete_obj_of_adjunction`, the completeness clause of
`prop-weil-pbc-direct-image-limits`). -/
theorem boundedConstructibleCompleteIn_of_witnessCompatibility {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {sq : IsPullback g' f' f g} {c : ℕ}
    (hW : WitnessCompatibility A I sq) (hT : TowerPreservation A I sq c) {K : 𝐃(X)} {a b : ℤ}
    (hK : DerivedCategory.boundedConstructibleCompleteIn I X a b K) :
    DerivedCategory.boundedConstructibleCompleteIn I Y a (b + c)
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj K) ∧
      (∀ {cY : Cone (_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology Y') I
          ((L(ProEtale.upperStar (ModuleCat.{u + 1} A) g)).obj
            ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj K)))},
        IsHomotopyLimit cY → DerivedCategory.boundedConstructibleCompleteIn I Y' a (b + c) cY.pt) ∧
      ∀ {cX : Cone (_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X') I
          ((L(ProEtale.upperStar (ModuleCat.{u + 1} A) g')).obj K))},
        IsHomotopyLimit cX → DerivedCategory.boundedConstructibleCompleteIn I X' a b cX.pt ∧
          DerivedCategory.boundedConstructibleCompleteIn I Y' a (b + c)
            ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f')).obj cX.pt) := by
  have hf := hT.lowerStar.constructibleIn_derivedCompletionDiagram_obj hϖ hI hW.lowerStar hK.2
  have hg := hT.upperStar.constructibleIn_derivedCompletionDiagram_obj hϖ hI hW.upperStar hf
  have hg' := hT.upperStar'.constructibleIn_derivedCompletionDiagram_obj hϖ hI hW.upperStar' hK.2
  simp only [Nat.cast_zero, add_zero] at hg hg'
  refine ⟨⟨_root_.DerivedCategory.derivedComplete_obj_of_adjunction hϖ hI
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) hK.1, hf⟩,
    fun hcY ↦ boundedConstructibleCompleteIn_of_isHomotopyLimit hϖ hI hg hcY, fun hcX ↦ ?_⟩
  have hX := boundedConstructibleCompleteIn_of_isHomotopyLimit hϖ hI hg' hcX
  exact ⟨hX, _root_.DerivedCategory.derivedComplete_obj_of_adjunction hϖ hI
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f') hX.1,
    hT.lowerStar'.constructibleIn_derivedCompletionDiagram_obj hϖ hI hW.lowerStar' hX.2⟩

end Preservation

end AlgebraicGeometry.ProEtale
