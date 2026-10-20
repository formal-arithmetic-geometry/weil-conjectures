/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Slop.Stalk
public import WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek

/-!

# The lower shriek of Weil objects and the global Frobenius

Let `f : X ⟶ Y` be a morphism of schemes over `Spec k` and `Φ_X : X ⟶ X`, `Φ_Y : Y ⟶ Y`
endomorphisms with `Φ_X ≫ f = f ≫ Φ_Y`. Unlike the case of automorphisms
(`ProEtale.CondensedRing.weilLowerShriek`), the Frobenius square need not be cartesian: put
```
X' = X ×_{f, Y, Φ_Y} Y,   p : X' ⟶ X,   f' : X' ⟶ Y,   r = (Φ_X, f) : X ⟶ X',
```
so that `r ≫ p = Φ_X` and `r ≫ f' = f`; `r` is the *relative Frobenius* of `f` (blueprint
`sk-d-relative-frob`). For the model Frobenii of a morphism of models over a finite field `r` is
a finite universal homeomorphism. The Frobenius comparison of `Rf_!` (blueprint
`sk-d-weil-push`) is then the composite
```
θ_f : Φ_Y^* Rf_! ≅ Rf'_! p^*                    (compact-support base change)
          ≅ Rf'_! Rr_* r^* p^*                   (topological invariance: the unit of r^* ⊣ Rr_*)
          ≅ Rf'_! Rr_! r^* p^*                   (Rr_! ≅ Rr_*, r being proper)
          ≅ R(r ≫ f')_! L(r ≫ p)^* = Rf_! Φ_X^*  (composition)
```
(`ProEtale.CondensedRing.weilLowerShriekFrobeniusComparison`), and the *lower shriek of Weil
objects* `ProEtale.CondensedRing.weilLowerShriekOfFrobenius` sends `(K, φ)` to `Rf_! K` with
the Weil structure `Φ_Y^* Rf_! K ≅ Rf_! Φ_X^* K --Rf_! φ--> Rf_! K`.

## Compactly supported cohomology

For the structure morphism `a_X : X ⟶ s` and the identity of the base point, the square is
trivially cartesian (`X' = X`, `p = 𝟙`, `r = Φ_X`), and the lower shriek of Weil objects is the
*compactly supported cohomology* of Weil objects
```
RΓ_c(X, -) = ProEtale.CondensedRing.weilCompactCohomology :
  WeilBoundedConstructible ℓ Φ ⥤ WeilBoundedConstructible ℓ (𝟙 s),
```
for every finite universal homeomorphism `Φ`. The *global operator* `F_{c,m}` of a Weil object
`(K, φ)` is the Frobenius of the Weil object `RΓ_c(X, (K, φ_m))` for the identity of `s`, an
automorphism of `RΓ_c(X, K) = Ra_{X!} K`
(`ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator`, blueprint
`def-trf-frobenius-coefficient-morphism` and `lem-trf-frobenius-operator-compact-description`).

## Sorried input

- `ProEtale.CondensedRing.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction`:
  topological invariance, the unit `𝟭 ⟶ Lr^* ⋙ Rr_*` is an isomorphism for a finite universal
  homeomorphism `r`.

## Main definitions

- `ProEtale.CondensedRing.weilLowerShriekFrobeniusComparison`: the Frobenius comparison `θ_f`.
- `ProEtale.CondensedRing.weilLowerShriekOfFrobenius`: the lower shriek of Weil objects along a
  morphism compatible with Frobenius endomorphisms.
- `ProEtale.CondensedRing.weilCompactCohomology`: the compactly supported cohomology of Weil
  objects.
- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobenius`: the Frobenius of
  `RΓ_c(X, K)`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator`: the global Frobenius
  operator `F_{c,m}` on `RΓ_c(X, K)`.

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology`:
  `RΓ_c(X, K)` is perfect (blueprint `prop-trf-compact-support-perfectness`).
- `ProEtale.CondensedRing.nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso`: the
  compactly supported cohomology of `Rf_! K` is that of `K`, as Weil objects (blueprint
  `lem-trf-weil-shriek-operator-fibres`).
- `ProEtale.CondensedRing.nonempty_weilStalk_weilLowerShriekOfFrobenius_iso`: the stalk of
  `Rf_! K` at a fixed point `y` is the compactly supported cohomology of the fibre `X_y`, as Weil
  objects (proper base change, blueprint `lem-trf-weil-shriek-operator-fibres`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

namespace Slop
end Slop
open Slop


open Scheme

/-! ### Topological invariance -/

section TopologicalInvariance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom]
  (r : X ⟶ X') [IsFinite r.left] [IsUniversalHomeomorphism r.left]

/-- **Topological invariance** of the bounded constructible derived category: for a finite
universal homeomorphism `r`, the unit `𝟭 ⟶ Lr^* ⋙ Rr_*` of the adjunction `Lr^* ⊣ Rr_*` is an
isomorphism, so that `Lr^*` is an equivalence with inverse `Rr_*` (blueprint `i-topology`). -/
theorem Slop.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction
    [IsFinitenessCoefficient ℓ Λ] :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ r).unit :=
  sorry

end TopologicalInvariance

/-! ### The lower shriek of Weil objects -/

section LowerShriek

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) (f : X ⟶ Y) {p : X' ⟶ X} {f' : X' ⟶ Y}
  (sq : IsPullback p f' f ΦY) (r : X ⟶ X') (hrp : r ≫ p = ΦX) (hrf : r ≫ f' = f)
  [IsFinite r.left] [IsUniversalHomeomorphism r.left]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] [IsFinite r.left]
  [IsUniversalHomeomorphism r.left] in
include sq hrp hrf in
/-- The Frobenius endomorphisms are compatible with `f`: `Φ_X ≫ f = f ≫ Φ_Y`. -/
lemma Slop.frobenius_comp_eq_comp_frobenius : ΦX ≫ f = f ≫ ΦY :=
  calc ΦX ≫ f = r ≫ p ≫ f := by rw [← hrp, Category.assoc]
    _ = r ≫ f' ≫ ΦY := by rw [sq.w]
    _ = f ≫ ΦY := by rw [← Category.assoc, hrf]

/-- The Frobenius comparison `θ_f : Rf_! ⋙ LΦ_Y^* ≅ LΦ_X^* ⋙ Rf_!` of the lower shriek, for the
cartesian square `sq : p ≫ f = f' ≫ Φ_Y` and the relative Frobenius `r` with `r ≫ p = Φ_X` and
`r ≫ f' = f`, a finite universal homeomorphism: compact-support base change for `sq`, the unit
of `Lr^* ⊣ Rr_*`, the identification `Rr_! ≅ Rr_*` and the composition isomorphisms of the
lower shriek and of the pullback (blueprint `sk-d-weil-push`). -/
noncomputable def Slop.weilLowerShriekFrobeniusComparison :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦY ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have := isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ r
  asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq) ≪≫
    Functor.isoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (asIso (boundedConstructibleUpperStarLowerStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ r).unit) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).symm _)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (boundedConstructibleLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ r f').symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p).symm _ ≪≫
    eqToIso (by rw [hrp, hrf])

/-- The *lower shriek of Weil objects* along a morphism `f` compatible with Frobenius
endomorphisms: a Weil object `(K, φ)` for `Φ_X` is sent to `Rf_! K` with the Weil structure
`Φ_Y^* Rf_! K ≅ Rf_! Φ_X^* K --Rf_! φ--> Rf_! K` given by
`weilLowerShriekFrobeniusComparison` (blueprint `def-trf-weil-shriek-pushforward`). -/
noncomputable def Slop.weilLowerShriekOfFrobenius :
    WeilBoundedConstructible ℓ ΦX ⥤ WeilBoundedConstructible ℓ ΦY :=
  IsoAlgebra.mapOfNatIso (weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f sq r hrp hrf)

@[simp]
lemma Slop.weilLowerShriekOfFrobenius_obj_carrier (K : WeilBoundedConstructible ℓ ΦX) :
    ((weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf).obj K).carrier =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K.carrier :=
  rfl

/-- The lower shriek of Weil objects lifts the lower shriek on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` along the forgetful
functors. -/
lemma Slop.weilLowerShriekOfFrobenius_comp_forget :
    weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf ⋙ WeilBoundedConstructible.forget ℓ ΦY =
      WeilBoundedConstructible.forget ℓ ΦX ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  rfl

end LowerShriek

/-! ### Compactly supported cohomology -/

section CompactCohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

omit [Fact (ringChar k).Prime] in
/-- The trivial cartesian square `𝟙 X ≫ a_X = a_X ≫ 𝟙 s` of the structure morphism. -/
lemma Slop.isPullback_toPoint (X : Over (Spec (.of k))) :
    IsPullback (𝟙 X) (toPoint X) (toPoint X) (𝟙 (point k)) :=
  IsPullback.of_horiz_isIso ⟨by simp⟩

variable (Φ : X ⟶ X) [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]

/-- The *compactly supported cohomology* `RΓ_c(X, -) = Ra_{X!}` of Weil objects for a finite
universal homeomorphism `Φ`: the lower shriek of Weil objects along the structure morphism
`a_X : X ⟶ s`, with the identity of the base point and the trivial cartesian square, the relative
Frobenius being `Φ` itself. -/
noncomputable def Slop.weilCompactCohomology :
    WeilBoundedConstructible ℓ Φ ⥤ WeilBoundedConstructible ℓ (𝟙 (point k)) :=
  weilLowerShriekOfFrobenius ℓ Φ (𝟙 (point k)) (toPoint X) (isPullback_toPoint X) Φ
    (Category.comp_id Φ) (comp_toPoint Φ)

@[simp]
lemma Slop.weilCompactCohomology_obj_carrier (K : WeilBoundedConstructible ℓ Φ) :
    ((weilCompactCohomology ℓ Φ).obj K).carrier =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier :=
  rfl

end CompactCohomology

/-! ### The global operator -/

namespace WeilBoundedConstructible

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {Φ : X ⟶ X}

/-- The *compactly supported Frobenius* of a Weil object `(K, φ)` for a finite universal
homeomorphism `Φ`: the Frobenius of the Weil object `RΓ_c(X, (K, φ))` for the identity of the base
point, an automorphism of `RΓ_c(X, K) = Ra_{X!} K`. Explicitly it is
```
RΓ_c(X, K) ≅ L(𝟙 s)^* Ra_{X!} K --θ_{a_X}--> Ra_{X!} LΦ^* K --Ra_{X!} φ--> Ra_{X!} K.
```
-/
noncomputable def compactFrobenius (K : WeilBoundedConstructible ℓ Φ) [IsFinite Φ.left]
    [IsUniversalHomeomorphism Φ.left] :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier :=
  ((weilCompactCohomology ℓ Φ).obj K).frobenius.hom

/- The carriers `(K.iterate m).carrier` and `K.carrier` are defeq, but the kernel check of this
defeq times out (see `ProEtale.CondensedRing.WeilBoundedConstructible.iterate_str`), so the
definition casts along `iterate_carrier`. -/
/-- The *global operator* `F_{c,m}` of a Weil object `(K, φ)` on its compactly supported
cohomology `RΓ_c(X, K) = Ra_{X!} K`: the compactly supported Frobenius of the iterate
`(K, φ_m)`, that is the Frobenius of the Weil object `RΓ_c(X, (K, φ_m))` for the identity of the
base point. Explicitly it is
```
RΓ_c(X, K) ≅ L(𝟙 s)^* Ra_{X!} K --θ_{a_X}--> Ra_{X!} LΦ_m^* K --Ra_{X!} φ_m--> Ra_{X!} K
```
(blueprint `def-trf-frobenius-coefficient-morphism` and
`lem-trf-frobenius-operator-compact-description`). It agrees with the global operator
`T_{c_m}(φ_m)` of the graph correspondence `c_m = (𝟙, Φ_m)`
(`ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator_eq_correspondenceGlobalOperator`,
blueprint `prop-trf-graph-frobenius-operator`). -/
noncomputable def globalOperator (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier :=
  eqToHom (by rw [iterate_carrier]) ≫ (K.iterate m).compactFrobenius ≫
    eqToHom (by rw [iterate_carrier])

/-- The global operator is invertible. -/
instance isIso_globalOperator (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] :
    IsIso (K.globalOperator m) := by
  have : IsIso (K.iterate m).compactFrobenius :=
    Iso.isIso_hom ((weilCompactCohomology ℓ (frobeniusIterate Φ m)).obj (K.iterate m)).frobenius
  dsimp only [globalOperator]
  infer_instance

/-- The global operator of degree `m` is the `m`-th power of the global operator of degree
one, `F_{c,m} = F_{c,1}^m` (blueprint `lem-trf-weil-shriek-iterates`). -/
lemma globalOperator_eq_pow (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left]
    [IsFinite (frobeniusIterate Φ 1).left] [IsUniversalHomeomorphism (frobeniusIterate Φ 1).left] :
    K.globalOperator m =
      (show End ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (toPoint X)).obj K.carrier) from K.globalOperator 1) ^ m :=
  sorry

/-- **Perfectness of compactly supported cohomology** (blueprint
`prop-trf-compact-support-perfectness`): for `k` separably closed, `RΓ_c(X, K)` is a perfect
complex, that is a dualizable object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`. -/
theorem nonempty_hasRightDual_compactCohomology [IsSepClosed k]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty (HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K)) :=
  sorry

/-- **Perfectness of the geometric stalks**: for `k` separably closed, the stalk `K_x̄ = Lx^* K`
of a bounded constructible complex at a rational point is a perfect complex, that is a
dualizable object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`. -/
theorem nonempty_hasRightDual_stalk [IsSepClosed k]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (x : RationalPoint X) :
    Nonempty (HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :=
  sorry

end WeilBoundedConstructible

/-! ### Compatibilities with the lower shriek -/

section Compatibilities

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {ΦX : X ⟶ X} {ΦY : Y ⟶ Y} {f : X ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y}
  (sq : IsPullback p f' f ΦY) {r : X ⟶ X'} (hrp : r ≫ p = ΦX) (hrf : r ≫ f' = f)
  [IsFinite r.left] [IsUniversalHomeomorphism r.left]
  [IsFinite ΦX.left] [IsUniversalHomeomorphism ΦX.left]
  [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left]

/-- **The Leray isomorphism for Weil objects** (blueprint `lem-trf-weil-shriek-operator-fibres`,
the global operators): the compactly supported cohomology of `Rf_! K` is that of `K`,
`RΓ_c(Y, Rf_! K) ≅ RΓ_c(X, K)`, as Weil objects for the identity of the base point. In
particular the global operators of `K` and of `Rf_! K` have the same trace. -/
theorem Slop.nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso
    (K : WeilBoundedConstructible ℓ ΦX) :
    Nonempty ((weilCompactCohomology ℓ ΦY).obj
        ((weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf).obj K) ≅
      (weilCompactCohomology ℓ ΦX).obj K) :=
  sorry

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] {ΦZ : Z ⟶ Z} [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]
  {i : Z ⟶ X} (hi : ΦZ ≫ i = i ≫ ΦX) {y : RationalPoint Y} (hy : y ≫ ΦY = y)
  (hZ : IsPullback i (toPoint Z) f y)

include hZ in
/-- **Proper base change for Weil objects** (blueprint `lem-trf-weil-shriek-operator-fibres`, the
stalks): for a rational point `y` of `Y` fixed by `Φ_Y` with fibre `Z = X ×_Y y` carrying a
Frobenius `Φ_Z` compatible with `Φ_X`, the stalk at `y` of `Rf_! K` is the compactly supported
cohomology of the restriction of `K` to the fibre, `(Rf_! K)_ȳ ≅ RΓ_c(Z, K|_Z)`, as Weil objects
for the identity of the base point. In particular the local Frobenius of `Rf_! K` at `y` and the
global operator of `K|_Z` have the same trace. -/
theorem Slop.nonempty_weilStalk_weilLowerShriekOfFrobenius_iso (K : WeilBoundedConstructible ℓ ΦX) :
    Nonempty ((weilStalk ℓ ΦY y hy).obj
        ((weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf).obj K) ≅
      (weilCompactCohomology ℓ ΦZ).obj ((weilUpperStar ℓ ΦZ ΦX i hi).obj K)) :=
  sorry

end Compatibilities

end AlgebraicGeometry.ProEtale.CondensedRing
