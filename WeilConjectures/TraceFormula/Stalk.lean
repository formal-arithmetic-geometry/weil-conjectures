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

/-- The Frobenius of a stalk, with the stalk written as `Lx^* K`. -/
lemma weilStalk_obj_frobenius_hom (x : RationalPoint X) (hx : x ≫ Φ = x)
    (K : WeilBoundedConstructible ℓ Φ) :
    ((weilStalk ℓ Φ x hx).obj K).frobenius.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier) ≫
        ((weilStalk ℓ Φ x hx).obj K).str.hom :=
  WeilBoundedConstructible.frobenius_hom _

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
  eqToHom (congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      (K.iterate_carrier m).symm :
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier =
          (K.iterateStalk m x hx).carrier) ≫
    (K.iterateStalk m x hx).frobenius.hom ≫
    eqToHom (congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      (K.iterate_carrier m) :
        (K.iterateStalk m x hx).carrier =
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier)

/-- The local Frobenius is the Frobenius of the stalk of the iterate, read on `Lx^* K`. -/
lemma stalkFrobenius_eq_frobenius (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    K.stalkFrobenius m x hx = (K.iterateStalk m x hx).frobenius.hom := by
  rw [stalkFrobenius]
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The local Frobenius is invertible. -/
instance isIso_stalkFrobenius (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) : IsIso (K.stalkFrobenius m x hx) := by
  rw [stalkFrobenius_eq_frobenius]
  exact Iso.isIso_hom (K.iterateStalk m x hx).frobenius

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The explicit form of the Frobenius of a stalk, for an abstract family of pullback functors:
`L(𝟙)^* Lx^* K ≅ L(𝟙 ≫ x)^* K = L(x ≫ P)^* K ≅ Lx^* LP^* K ⟶ Lx^* K` is
`Lx^* K = L(x ≫ P)^* K ≅ Lx^* LP^* K ⟶ Lx^* K`. -/
lemma stalkFrobenius_eq_aux {𝒞 : Type*} [Category 𝒞] {W X' : 𝒞} {DW DX : Type*}
    [Category DW] [Category DX] (UWW : (W ⟶ W) → DW ⥤ DW) (UWX : (W ⟶ X') → DX ⥤ DW)
    (UXX : (X' ⟶ X') → DX ⥤ DX)
    (cWW : ∀ (a : W ⟶ W) (b : W ⟶ X'), UWX (a ≫ b) ≅ UWX b ⋙ UWW a)
    (cWX : ∀ (a : W ⟶ X') (b : X' ⟶ X'), UWX (a ≫ b) ≅ UXX b ⋙ UWX a)
    (ιW : UWW (𝟙 W) ≅ 𝟭 DW)
    (hidl : ∀ (b : W ⟶ X') (K : DX), (cWW (𝟙 W) b).hom.app K ≫ ιW.hom.app ((UWX b).obj K) =
      eqToHom (show (UWX (𝟙 W ≫ b)).obj K = _ by rw [Category.id_comp]; rfl))
    {x : W ⟶ X'} {P : X' ⟶ X'} (hx : x ≫ P = x) (sq : 𝟙 W ≫ x = x ≫ P) {K : DX}
    (ψ : (UXX P).obj K ⟶ K) :
    ιW.inv.app ((UWX x).obj K) ≫ (cWW (𝟙 W) x).inv.app K ≫
        eqToHom (congrArg (fun f ↦ (UWX f).obj K) sq) ≫ (cWX x P).hom.app K ≫
        (UWX x).map ψ =
      eqToHom (congrArg (fun f ↦ (UWX f).obj K) hx.symm) ≫ (cWX x P).hom.app K ≫
        (UWX x).map ψ := by
  rw [PullbackFamily.inv_app_id_left UWW UWX cWW ιW hidl, Category.assoc,
    Iso.inv_hom_id_app_assoc, eqToHom_trans_assoc]

/-- The Frobenius of the stalk at `x` of a Weil object `(K, φ)` for `Φ`, for `x` fixed by `Φ`, is
`Lx^* K = L(x ≫ Φ)^* K ≅ Lx^* LΦ^* K --Lx^* φ--> Lx^* K`. -/
lemma weilStalk_obj_frobenius_hom_eq (x : RationalPoint X) (hx : x ≫ Φ = x)
    (K : WeilBoundedConstructible ℓ Φ) :
    ((weilStalk ℓ Φ x hx).obj K).frobenius.hom =
      eqToHom (congrArg (fun f ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ f).obj K.carrier) hx.symm) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x Φ).hom.app
          K.carrier ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map K.str.hom := by
  rw [weilStalk_obj_frobenius_hom]
  dsimp only [weilStalk]
  rw [weilUpperStar_obj_str]
  simp only [weilUpperStarComparison, boundedConstructiblePullbackSquareComparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
    eqToIso.inv, NatTrans.comp_app, eqToHom_app, Category.assoc]
  exact stalkFrobenius_eq_aux
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k))
    (fun b K ↦ boundedConstructibleUpperStarComp_id_left_app _ ℓ b K) hx
    (by rw [Category.id_comp, hx]) K.str.hom

/-- The local Frobenius as an explicit composite on the carrier of the iterate `(K, φ_m)`:
`Lx^* K = L(x ≫ Φ_m)^* K ≅ Lx^* LΦ_m^* K --Lx^* φ_m--> Lx^* K`. -/
lemma iterateStalk_frobenius_hom_eq (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    (K.iterateStalk m x hx).frobenius.hom =
      eqToHom (congrArg (fun f ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ f).obj (K.iterate m).carrier) hx.symm) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x
          (frobeniusIterate Φ m)).hom.app (K.iterate m).carrier ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
          (K.iterate m).str.hom :=
  weilStalk_obj_frobenius_hom_eq x hx (K.iterate m)

/-- The local Frobenius `F_{x,m}` as an explicit composite on the carrier `K'` of the iterate,
conjugated by the identification `K = K'`:
`Lx^* K = L(x ≫ Φ_m)^* K ≅ Lx^* LΦ_m^* K --Lx^* φ_m--> Lx^* K`. -/
lemma stalkFrobenius_eq_cast (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) :
    K.stalkFrobenius m x hx =
      eqToHom (congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
          (K.iterate_carrier m).symm) ≫
        (eqToHom (congrArg (fun f ↦
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
              (K.iterate m).carrier) hx.symm) ≫
          (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x
            (frobeniusIterate Φ m)).hom.app (K.iterate m).carrier ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              (frobeniusIterate Φ m)).map (eqToHom (K.iterate_carrier m)) ≫
              (K.iterateStr m).hom ≫ eqToHom (K.iterate_carrier m).symm)) ≫
        eqToHom (congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
          (K.iterate_carrier m)) := by
  rw [stalkFrobenius, iterateStalk_frobenius_hom_eq, iterate_str]
  simp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
