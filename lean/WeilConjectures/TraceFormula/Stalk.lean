/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.TraceFormula.Frobenius

/-!

# Stalks of Weil objects and the local Frobenius

Let `Φ : X ⟶ X` be an endomorphism of a scheme over `Spec k` and `x : s ⟶ X` a rational point
fixed by `Φ`, `x ≫ Φ = x`. The square
```
   s ──x──▶ X
   │𝟙       │Φ
   ▼        ▼
   s ──x──▶ X
```
commutes, so the derived pullback `Lx^*` of Weil objects
(`ProEtale.CondensedRing.weilUpperStar`) sends a Weil object `(K, φ)` for `Φ` to a Weil object
`(K_x̄, φ_x̄)` for the identity of the base point: the *stalk functor*
```
ProEtale.CondensedRing.weilStalk :
  WeilBoundedConstructible ℓ Φ ⥤ WeilBoundedConstructible ℓ (𝟙 s).
```
Its structure isomorphism is
```
L(𝟙 s)^* Lx^* K ≅ Lx^* LΦ^* K --Lx^* φ--> Lx^* K,
```
and the Frobenius `WeilBoundedConstructible.frobenius` of this Weil object for the identity is the
*local Frobenius* at `x`.

For a point `x` fixed by `Φ_m` the local Frobenius of the iterate `(K, φ_m)` is the operator
`F_{x,m} = (φ_m)_x̄` on the geometric stalk `K_x̄ = Lx^* K` of the trace formula
(`ProEtale.CondensedRing.WeilBoundedConstructible.stalkFrobenius`, blueprint `sk-d-weil`).

The stalks at `x` and at its Frobenius translate `x ≫ Φ` are isomorphic Weil objects
(`ProEtale.CondensedRing.WeilBoundedConstructible.stalkTransport`), so their local Frobenii are
conjugate and have the same trace (blueprint `lem-trf-local-frobenius-conjugacy`); and at a point
fixed by `Φ_d` the operator `F_{x,dn}` is the `n`-th power of `F_{x,d}` (blueprint
`lem-trf-frobenius-degree-formula`).

## Main definitions

- `ProEtale.CondensedRing.weilStalk`: the stalk functor of Weil objects at a fixed point.
- `ProEtale.CondensedRing.WeilBoundedConstructible.iterateStalk`: the stalk `(K_x̄, (φ_m)_x̄)` of
  the iterate `(K, φ_m)` at a point fixed by `Φ_m`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.stalkFrobenius`: the local Frobenius
  `F_{x,m}` on `K_x̄`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.stalkTransport`: the isomorphism of Weil
  objects between the stalks at `x ≫ Φ` and at `x`.

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.stalkFrobenius_mul`: `F_{x,dn} = F_{x,d}ⁿ`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.trace_stalkFrobenius_comp`:
  `tr(F_{x ≫ Φ, m}) = tr(F_{x,m})`.

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

/-! ### The stalk functor -/

section Stalk

variable (Φ : X ⟶ X)

/-- The *stalk functor* at a rational point `x` fixed by `Φ`: the derived pullback `Lx^*` of
Weil objects along the square `𝟙 s ≫ x = x ≫ Φ`, from Weil objects for `Φ` on `X` to Weil
objects for the identity of the base point `s`. -/
noncomputable def weilStalk (x : RationalPoint X) (hx : x ≫ Φ = x) :
    WeilBoundedConstructible ℓ Φ ⥤ WeilBoundedConstructible ℓ (𝟙 (point k)) :=
  weilUpperStar ℓ (𝟙 (point k)) Φ x (by rw [Category.id_comp, hx])

@[simp]
lemma weilStalk_obj_carrier (x : RationalPoint X) (hx : x ≫ Φ = x)
    (K : WeilBoundedConstructible ℓ Φ) :
    ((weilStalk ℓ Φ x hx).obj K).carrier =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier :=
  rfl

/-- The stalk functor lifts the derived pullback `Lx^*` along the forgetful functors. -/
lemma weilStalk_comp_forget (x : RationalPoint X) (hx : x ≫ Φ = x) :
    weilStalk ℓ Φ x hx ⋙ WeilBoundedConstructible.forget ℓ (𝟙 (point k)) =
      WeilBoundedConstructible.forget ℓ Φ ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x :=
  rfl

end Stalk

/-! ### The local Frobenius -/

namespace WeilBoundedConstructible

variable {ℓ} {Φ : X ⟶ X}

/-- The stalk `(K_x̄, (φ_m)_x̄)` at a rational point `x` fixed by `Φ_m` of the iterate `(K, φ_m)`
of a Weil object `(K, φ)`: a Weil object for the identity of the base point. -/
noncomputable def iterateStalk (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) : WeilBoundedConstructible ℓ (𝟙 (point k)) :=
  (weilStalk ℓ (frobeniusIterate Φ m) x hx).obj (K.iterate m)

/-- The *local Frobenius* `F_{x,m} = (φ_m)_x̄` of a Weil object `(K, φ)` at a rational point `x`
fixed by `Φ_m`: the Frobenius of the stalk at `x` of the iterate `(K, φ_m)`, an automorphism of
the geometric stalk `K_x̄ = Lx^* K`. Explicitly it is the composite
```
Lx^* K ≅ L(𝟙 s)^* Lx^* K ≅ Lx^* LΦ_m^* K --Lx^* φ_m--> Lx^* K
```
(blueprint `sk-d-weil`). -/
noncomputable def stalkFrobenius (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier :=
  (K.iterateStalk m x hx).frobenius.hom

/-- The local Frobenius is invertible. -/
instance isIso_stalkFrobenius (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) : IsIso (K.stalkFrobenius m x hx) :=
  Iso.isIso_hom (K.iterateStalk m x hx).frobenius

/-- **The degree formula** (blueprint `lem-trf-frobenius-degree-formula`): at a point `x` fixed
by `Φ_d`, the local Frobenius of degree `d * n` is the `n`-th power of the local Frobenius of
degree `d`, `F_{x,dn} = F_{x,d}ⁿ`. -/
lemma stalkFrobenius_mul (K : WeilBoundedConstructible ℓ Φ) {d : ℕ} {x : RationalPoint X}
    (hx : x ≫ frobeniusIterate Φ d = x) (n : ℕ) :
    K.stalkFrobenius (d * n) x
        (by rw [frobeniusIterate_mul]; exact comp_frobeniusIterate_of_comp hx n) =
      (show End ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
          K.carrier) from K.stalkFrobenius d x hx) ^ n :=
  sorry

/-- The iterate `φ_m` of a Weil structure commutes with `φ`: `φ ∘ LΦ^* φ_m = φ_m ∘ LΦ_m^* φ`
along `L(Φ ≫ Φ_m)^* = L(Φ_m ≫ Φ)^*`. -/
lemma iterateStr_comm (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) :
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Φ
        (frobeniusIterate Φ m)).hom.app K.carrier ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        (K.iterateStr m).hom ≫ K.str.hom =
    eqToHom (show (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (Φ ≫ frobeniusIterate Φ m)).obj K.carrier = _ by rw [comp_frobeniusIterate_comm]) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
        (frobeniusIterate Φ m) Φ).hom.app K.carrier ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (frobeniusIterate Φ m)).map K.str.hom ≫ (K.iterateStr m).hom := by
  have hcongr : ∀ {n n' : ℕ} (h : n = n'), (K.iterateStr n).hom =
      eqToHom (show (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (frobeniusIterate Φ n)).obj K.carrier = _ by rw [h]) ≫ (K.iterateStr n').hom := by
    intro n n' h
    subst h
    simp
  exact PullbackFamily.commute
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X)
    (fun a K ↦ boundedConstructibleUpperStarComp_id_right_app _ ℓ a K)
    (frobeniusIterate_zero Φ) (frobeniusIterate_succ Φ 0) (frobeniusIterate_succ Φ m)
    (frobeniusIterate_add Φ 1 m) (by rw [Nat.add_comm]) (comp_frobeniusIterate_comm Φ m)
    K.str.hom (K.iterateStr m).hom (K.iterateStr 0).hom (K.iterateStr 1).hom
    (K.iterateStr (m + 1)).hom (K.iterateStr (1 + m)).hom (Category.id_comp _).symm rfl rfl
    (iterateStr_add K 1 m) (hcongr (Nat.add_comm m 1))

/-- The isomorphism underlying the Frobenius transport `stalkTransport`:
```
L(x ≫ Φ)^* K ≅ Lx^* LΦ^* K --Lx^* φ--> Lx^* K.
```
It is stated on the carrier `(K.iterate m).carrier` of the iterate, equal to `K.carrier`; the
casts are explicit (`eqToIso`), since checking this equality by unfolding is expensive.
-/
noncomputable def stalkTransportIso (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    (K.iterateStalk m (x ≫ Φ) (comp_comp_frobeniusIterate hx)).carrier ≅
      (K.iterateStalk m x hx).carrier :=
  (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x Φ).app
      (K.iterate m).carrier ≪≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).mapIso
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).mapIso
        (eqToIso (K.iterate_carrier m)) ≪≫ K.str ≪≫ eqToIso (K.iterate_carrier m).symm)

/-- The *Frobenius transport* between the stalks at `x ≫ Φ` and at `x` of the iterate
`(K, φ_m)`, for `x` fixed by `Φ_m`: the isomorphism of Weil objects for the identity of `s` whose
underlying isomorphism is `stalkTransportIso`,
```
L(x ≫ Φ)^* K ≅ Lx^* LΦ^* K --Lx^* φ--> Lx^* K.
```
It intertwines the local Frobenii since `φ_m` commutes with `φ`. -/
noncomputable def stalkTransport (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) :
    K.iterateStalk m (x ≫ Φ) (comp_comp_frobeniusIterate hx) ≅ K.iterateStalk m x hx :=
  IsoAlgebra.isoMk (K.stalkTransportIso m x hx) (by
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom]
    dsimp only [iterateStalk, weilStalk]
    rw [weilUpperStar_obj_str, weilUpperStar_obj_str, iterate_str]
    simp only [stalkTransportIso, weilUpperStarComparison,
      boundedConstructiblePullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv, Functor.map_comp,
      eqToHom_map, NatTrans.comp_app, eqToHom_app, Category.assoc]
    have hψ := K.iterateStr_comm m
    exact PullbackFamily.transport_eqToHom
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
      (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k))
      (fun b K ↦ boundedConstructibleUpperStarComp_id_left_app _ ℓ b K)
      (fun a b c K ↦ boundedConstructibleUpperStarComp_assoc_app _ ℓ a b c K) hx
      (comp_frobeniusIterate_comm Φ m) (K.iterate_carrier m) K.str.hom (K.iterateStr m).hom hψ
      _ _ _ _ _ _ _ _ _ _)

attribute [local instance] boundedConstructibleBraiding in
/-- **Conjugacy of the local Frobenii** (blueprint `lem-trf-local-frobenius-conjugacy`): the
local Frobenii at `x` and at its Frobenius translate `x ≫ Φ` have the same trace. -/
theorem trace_stalkFrobenius_comp (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)]
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ Φ)).obj
      K.carrier)] :
    trace (K.stalkFrobenius m (x ≫ Φ) (comp_comp_frobeniusIterate hx)) =
      trace (K.stalkFrobenius m x hx) :=
  trace_eq_of_iso
    (X := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ Φ)).obj K.carrier)
    (X' := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier)
    ((IsoAlgebra.forget _).mapIso (K.stalkTransport m x hx)) _ _
    (frobenius_hom_naturality (K.stalkTransport m x hx).hom)

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
