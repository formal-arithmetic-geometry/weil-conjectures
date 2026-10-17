/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek

/-!

# Weil objects for an endomorphism

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
objects `X : Over (Spec (.of k))`, separated and of finite type over `Spec k`, and the
coefficients are the bounded constructible derived categories `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` of `ℚ̄_ℓ`-sheaves,
`ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`.

The Frobenius of the trace formula is the *model Frobenius* `Φ = F₀ × 𝟙` of `X = X₀ ×_{𝔽_q} k`,
the base change of the `q`-power Frobenius `F₀` of a model `X₀`. It is an endomorphism of `X`
over `Spec k`, a finite universal homeomorphism, but not an automorphism. The Weil objects of
`WeilConjectures.WeilObject.BoundedConstructible.Defs` are defined for automorphisms, so this
file defines their analogue for an endomorphism, for use in the trace formula only:

* a *Weil object* for `Φ : X ⟶ X` is an object `K` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with an isomorphism
  `φ : LΦ^* K ≅ K` (`ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd`);
* its *iterate* `(K, φ_m)` is a Weil object for `Φ_m = Φ^m`
  (`ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd.iterate`);
* a Weil object for the identity is an object with an automorphism, its *Frobenius*
  (`ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd.frobenius`). The stalk of a Weil object
  at a fixed point and its compactly supported cohomology are Weil objects of this kind over the
  base point `s = Spec k` (`WeilConjectures.TraceFormula.Statement`).

## Sorried inputs

The following comparison isomorphisms of the six functors are not on this branch yet. They are
stated with value `sorry`, to be replaced by their constructions:

- `ProEtale.CondensedRing.boundedConstructibleUpperStarId`: `L(𝟙 X)^* ≅ 𝟭`, the restriction of
  the identity isomorphism of the derived pullback on module objects.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl`: `Rf_! ≅ Rf_*`
  for `f` proper, from the independence of the compactification and the trivial
  compactification `X ⟶[𝟙] X ⟶[f] Y`.
- `ProEtale.CondensedRing.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction`:
  topological invariance, `Lr^*` is an equivalence for a finite universal homeomorphism `r`
  (blueprint `i-topology`).

## Main definitions

- `ProEtale.CondensedRing.point`: the base point `s = Spec k`, terminal in `Over (Spec (.of k))`.
- `ProEtale.CondensedRing.toPoint`: the structure morphism `a_X : X ⟶ s`.
- `ProEtale.CondensedRing.RationalPoint`: the `k`-rational points `s ⟶ X`.
- `ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd`: Weil objects for an endomorphism.
- `ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd.frobenius`: the automorphism of a Weil
  object for the identity.
- `ProEtale.CondensedRing.frobeniusIterate`: the iterate `Φ_m = Φ^m` of an endomorphism.
- `ProEtale.CondensedRing.WeilBoundedConstructibleOfEnd.iterate`: the Weil object `(K, φ_m)`
  for `Φ_m` (blueprint `def-trf-iterated-weil-map`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The base point -/

section Point

variable (k : Type u) [Field k]

/-- The base point `s = Spec k` of `Over (Spec (.of k))`: the object `Spec k` with the identity
as structure morphism. It is terminal (`ProEtale.CondensedRing.isTerminalPoint`). -/
noncomputable abbrev point : Over (Spec (.of k)) :=
  Over.mk (𝟙 (Spec (.of k)))

instance : LocallyOfFiniteType (point k).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))

instance : QuasiCompact (point k).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

instance : IsSeparated (point k).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

/-- The base point is terminal in `Over (Spec (.of k))`. -/
noncomputable def isTerminalPoint : IsTerminal (point k) :=
  Over.mkIdTerminal

variable {k}

/-- The structure morphism `a_X : X ⟶ s` of a scheme over `Spec k`. -/
noncomputable def toPoint (X : Over (Spec (.of k))) : X ⟶ point k :=
  Over.homMk X.hom (by simp)

@[simp]
lemma toPoint_left (X : Over (Spec (.of k))) : (toPoint X).left = X.hom :=
  rfl

/-- Two morphisms to the base point are equal. -/
lemma toPoint_ext {X : Over (Spec (.of k))} (f g : X ⟶ point k) : f = g :=
  (isTerminalPoint k).hom_ext f g

@[simp]
lemma comp_toPoint {X Y : Over (Spec (.of k))} (f : X ⟶ Y) : f ≫ toPoint Y = toPoint X :=
  toPoint_ext _ _

/-- The `k`-rational points of `X`: the morphisms `s ⟶ X` of `Over (Spec (.of k))`, that is the
sections of the structure morphism `a_X`. -/
abbrev RationalPoint (X : Over (Spec (.of k))) : Type u :=
  point k ⟶ X

end Point

/-! ### Sorried comparison isomorphisms of the six functors -/

section Inputs

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]


variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **Topological invariance** of the bounded constructible derived category: for a finite
universal homeomorphism `r`, the unit `𝟭 ⟶ Lr^* ⋙ Rr_*` of the adjunction `Lr^* ⊣ Rr_*` is an
isomorphism, so that `Lr^*` is an equivalence with inverse `Rr_*` (blueprint `i-topology`). -/
theorem isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction
    [IsFinitenessCoefficient ℓ Λ] (r : X ⟶ Y)
    [IsFinite r.left] [IsUniversalHomeomorphism r.left] :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ r).unit :=
  sorry


end Inputs

/-! ### Weil objects for an endomorphism -/

section WeilObject

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (Φ : X ⟶ X)

/-- A *Weil object* of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for an endomorphism `Φ : X ⟶ X` over `Spec k` is an object
`K` together with an isomorphism `φ_K : LΦ^* K ≅ K`, where
`LΦ^* = boundedConstructibleUpperStar ℚ̲̄_ℓ ℓ Φ` is the derived pullback along `Φ`. The
isomorphism `φ_K` is structure data, and morphisms are morphisms of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` commuting
with the structure isomorphisms. For an automorphism `e`, these are the Weil objects
`ProEtale.CondensedRing.WeilBoundedConstructible ℓ e` for `Φ = e.hom`. -/
abbrev WeilBoundedConstructibleOfEnd : Type _ :=
  IsoAlgebra (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)

namespace WeilBoundedConstructibleOfEnd

/-- The forgetful functor from Weil objects for `Φ` to `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def forget :
    WeilBoundedConstructibleOfEnd ℓ Φ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  IsoAlgebra.forget (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)

variable {ℓ}

/-- The *Frobenius* of a Weil object `(K, φ_K)` for the identity `𝟙 X`: the automorphism
```
K --(L(𝟙 X)^* ≅ 𝟭)⁻¹--> L(𝟙 X)^* K --φ_K--> K.
```
For the stalk of a Weil object at a fixed point and for its compactly supported cohomology,
Weil objects for the identity of the base point, this is the Frobenius operator of the trace
formula. -/
noncomputable def frobenius (K : WeilBoundedConstructibleOfEnd ℓ (𝟙 X)) :
    K.carrier ≅ K.carrier :=
  ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app K.carrier).symm ≪≫
    K.str

end WeilBoundedConstructibleOfEnd

end WeilObject

/-! ### Iterates -/

section Iterate

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (Φ : X ⟶ X)

/-- The `m`-th iterate `Φ_m = Φ^m : X ⟶ X` of an endomorphism `Φ`. -/
noncomputable def frobeniusIterate (m : ℕ) : X ⟶ X :=
  End.asHom (End.of Φ ^ m)

@[simp]
lemma frobeniusIterate_zero : frobeniusIterate Φ 0 = 𝟙 X :=
  rfl

lemma frobeniusIterate_succ (m : ℕ) :
    frobeniusIterate Φ (m + 1) = Φ ≫ frobeniusIterate Φ m := by
  rw [frobeniusIterate, pow_succ]
  rfl

@[simp]
lemma frobeniusIterate_one : frobeniusIterate Φ 1 = Φ := by
  rw [frobeniusIterate_succ, frobeniusIterate_zero, Category.comp_id]

end Iterate

section WeilIterate

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {Φ : X ⟶ X}

namespace WeilBoundedConstructibleOfEnd

/-- The iterate `φ_m : LΦ_m^* K ≅ K` of the Weil structure `φ` of a Weil object `(K, φ)`:
`φ_0` is the identity isomorphism `L(𝟙 X)^* K ≅ K` and `φ_{m+1}` is the composite
```
LΦ_{m+1}^* K = L(Φ ≫ Φ_m)^* K ≅ LΦ^* LΦ_m^* K --LΦ^* φ_m--> LΦ^* K --φ--> K
```
(blueprint `def-trf-iterated-weil-map`). -/
noncomputable def iterateStr (K : WeilBoundedConstructibleOfEnd ℓ Φ) :
    (m : ℕ) → (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K.carrier ≅ K.carrier
  | 0 => (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app K.carrier
  | m + 1 =>
    eqToIso (by rw [frobeniusIterate_succ]) ≪≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Φ
        (frobeniusIterate Φ m)).app K.carrier ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).mapIso
        (iterateStr K m) ≪≫
      K.str

/-- The `m`-th iterate `(K, φ_m)` of a Weil object `(K, φ)` for `Φ`: a Weil object for the
iterate `Φ_m` with the same underlying complex. -/
noncomputable def iterate (K : WeilBoundedConstructibleOfEnd ℓ Φ) (m : ℕ) :
    WeilBoundedConstructibleOfEnd ℓ (frobeniusIterate Φ m) :=
  IsoAlgebra.mk K.carrier (K.iterateStr m)

@[simp]
lemma iterate_carrier (K : WeilBoundedConstructibleOfEnd ℓ Φ) (m : ℕ) :
    (K.iterate m).carrier = K.carrier :=
  IsoAlgebra.mk_carrier _ _

end WeilBoundedConstructibleOfEnd

end WeilIterate

end AlgebraicGeometry.ProEtale.CondensedRing
