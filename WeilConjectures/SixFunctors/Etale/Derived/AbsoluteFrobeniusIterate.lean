/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SchemeGaloisIterate

/-!
# Iterates of the absolute Frobenius on the derived étale topos

For a scheme `X` of characteristic `p`, the identifications `θ_n : L(F_X^n)^* ≅ L(𝟙 X)^*` of
`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso` are compatible with the
iterates `F_X^{m + n} = F_X^m ≫ F_X^n`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso_add`). Consequently, for
`Φ = F_X^n ≫ γ`, the iterates `κ_m : L(Φ^m)^* ≅ L(γ^m)^*` of the induced identification
`κ : LΦ^* ≅ Lγ^*` become, after pullback along a morphism `x : S ⟶ X`, the identifications
`L(F_S^{nm})^* ≅ L(𝟙 S)^*`.

## Main results

- `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso_add`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso_add`: compatibility of the
  identifications `F_X^* ≅ (𝟙 X)^*` with the iterates.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso_zero_hom_app`: the
  identification for `F_X^0 = 𝟙 X` is the identity.
- `leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarIterateHomIso_hom_app`: the iterates
  `κ_m` at a point.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Sheaf

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {p : ℕ} (hp : p.Prime) {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (m n : ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- The base change form of `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso_add`: the
isomorphisms `V ×_{X, 𝟙} X ≅ V ×_{X, F_X^k} X` of
`AlgebraicGeometry.Etale.overPullbackIterateFrobeniusIso` are compatible with the iterates
`F_X^{m + n} = F_X^m ≫ F_X^n`. -/
lemma overPullbackIterateFrobeniusIso_add (V : MorphismProperty.Over @Etale ⊤ X) :
    (overPullbackIterateFrobeniusIso hp hX m).hom.app V ≫
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) (X.iterateFrobenius hp hX m)
        (𝟙 X) (X.iterateFrobenius hp hX m) (Category.comp_id _).symm).hom.app V ≫
      (MorphismProperty.Over.pullback @Etale ⊤ (X.iterateFrobenius hp hX m)).map
        ((overPullbackIterateFrobeniusIso hp hX n).hom.app V) ≫
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) (X.iterateFrobenius hp hX m)
        (X.iterateFrobenius hp hX n) (X.iterateFrobenius hp hX (m + n))
        (iterateFrobenius_add hp X hX m n)).inv.app V =
    (overPullbackIterateFrobeniusIso hp hX (m + n)).hom.app V := by
  ext : 1
  apply pullback.hom_ext
  · simp [Scheme.iterateFrobenius_add]
  · simp

set_option backward.isDefEq.respectTransparency false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The pushforward form of `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso_add`: the
isomorphisms `(F_X^k)_* ≅ (𝟙 X)_*` are compatible with the iterates
`F_X^{m + n} = F_X^m ≫ F_X^n`. -/
lemma lowerStarIterateFrobeniusIso_add :
    (lowerStarIterateFrobeniusIso A hp hX (m + n)).hom =
      (lowerStarComp A (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n)
          (X.iterateFrobenius hp hX (m + n)) (iterateFrobenius_add hp X hX m n)).inv ≫
        Functor.whiskerLeft (X.iterateFrobenius hp hX m)_*[A]
          (lowerStarIterateFrobeniusIso A hp hX n).hom ≫
        (lowerStarComp A (X.iterateFrobenius hp hX m) (𝟙 X) (X.iterateFrobenius hp hX m)
          (Category.comp_id _).symm).hom ≫
        (lowerStarIterateFrobeniusIso A hp hX m).hom := by
  refine NatTrans.ext (funext fun G ↦ Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ?_)))
  have hl := Etale.lowerStar_obj_val_map A (X.iterateFrobenius hp hX m) G
    ((overPullbackIterateFrobeniusIso hp hX n).hom.app V.unop)
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_inv_app_hom_app', lowerStarComp_hom_app_hom_app, Functor.whiskerLeft_app,
    lowerStarIterateFrobeniusIso_hom_app_hom_app, hl, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun φ ↦ G.obj.map φ.op)
    (overPullbackIterateFrobeniusIso_add hp hX m n V.unop).symm

/-- The isomorphisms `(F_X^k)^* ≅ (𝟙 X)^*` of
`AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso` are compatible with the iterates
`F_X^{m + n} = F_X^m ≫ F_X^n`: the composite
```
(F_X^{m + n})^* ≅ (F_X^n)^* ⋙ (F_X^m)^* ≅ (𝟙 X)^* ⋙ (F_X^m)^* ≅ (F_X^m)^* ≅ (𝟙 X)^*
```
is the isomorphism for `F_X^{m + n}`. This is conjugate to
`AlgebraicGeometry.Etale.lowerStarIterateFrobeniusIso_add`. -/
theorem upperStarIterateFrobeniusIso_add :
    upperStarComp A (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n)
        (X.iterateFrobenius hp hX (m + n)) (iterateFrobenius_add hp X hX m n) ≪≫
      Functor.isoWhiskerRight (upperStarIterateFrobeniusIso A hp hX n)
        (X.iterateFrobenius hp hX m)^*[A] ≪≫
      (upperStarComp A (X.iterateFrobenius hp hX m) (𝟙 X) (X.iterateFrobenius hp hX m)
        (Category.comp_id _).symm).symm ≪≫
      upperStarIterateFrobeniusIso A hp hX m =
    upperStarIterateFrobeniusIso A hp hX (m + n) := by
  apply (conjugateIsoEquiv (upperStarLowerStarAdjunction A (𝟙 X))
    (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX (m + n)))).injective
  rw [conjugateIsoEquiv_trans _
      ((upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX n)).comp
        (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX m))),
    conjugateIsoEquiv_trans _
      ((upperStarLowerStarAdjunction A (𝟙 X)).comp
        (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX m))),
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX m)),
    conjugateIsoEquiv_iso_symm,
    conjugateIsoEquiv_upperStarComp A _ _ (X.iterateFrobenius hp hX m) (Category.comp_id _).symm,
    conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_upperStarComp A _ _ (X.iterateFrobenius hp hX (m + n))
      (Scheme.iterateFrobenius_add hp X hX m n),
    conjugateIsoEquiv_upperStarIterateFrobeniusIso A hp hX m,
    conjugateIsoEquiv_upperStarIterateFrobeniusIso A hp hX n,
    conjugateIsoEquiv_upperStarIterateFrobeniusIso A hp hX (m + n)]
  ext : 1
  rw [← cancel_epi (lowerStarIterateFrobeniusIso A hp hX (m + n)).hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Iso.hom_inv_id]
  rw [lowerStarIterateFrobeniusIso_add A hp hX m n]
  ext G
  simp

end Sheaf

section Derived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
variable {p : ℕ} (hp : p.Prime) {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (m n : ℕ)

/-- The isomorphisms `L(F_X^k)^* ≅ L(𝟙 X)^*` of
`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso` are compatible with the
iterates `F_X^{m + n} = F_X^m ≫ F_X^n`: the composite
```
L(F_X^{m + n})^* ≅ L(F_X^n)^* ⋙ L(F_X^m)^* ≅ L(𝟙 X)^* ⋙ L(F_X^m)^* ≅ L(F_X^m)^* ≅ L(𝟙 X)^*
```
is the isomorphism for `F_X^{m + n}`. This is the derived form of
`AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso_add`. -/
theorem leftDerivedUpperStarIterateFrobeniusIso_add :
    leftDerivedUpperStarComp A (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n)
        (X.iterateFrobenius hp hX (m + n)) (iterateFrobenius_add hp X hX m n) ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarIterateFrobeniusIso A hp hX n)
        L((X.iterateFrobenius hp hX m)^*[A]) ≪≫
      (leftDerivedUpperStarComp A (X.iterateFrobenius hp hX m) (𝟙 X)
        (X.iterateFrobenius hp hX m) (Category.comp_id _).symm).symm ≪≫
      leftDerivedUpperStarIterateFrobeniusIso A hp hX m =
    leftDerivedUpperStarIterateFrobeniusIso A hp hX (m + n) := by
  have key := congrArg (Functor.leftDerivedFunctorNatIso _)
    (upperStarIterateFrobeniusIso_add A hp hX m n)
  simp only [Functor.leftDerivedFunctorNatIso_trans, Functor.leftDerivedFunctorNatIso_symm]
    at key
  refine Eq.trans ?_ key
  ext : 1
  simp only [leftDerivedUpperStarComp, leftDerivedUpperStarIterateFrobeniusIso, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Functor.isoWhiskerRight_hom, Category.assoc]
  rw [← reassoc_of% (Functor.leftDerivedFunctorNatIso_isoWhiskerRight _
      (upperStarIterateFrobeniusIso A hp hX n) (X.iterateFrobenius hp hX m)^*[A]),
    Iso.hom_inv_id_assoc]


/-- The component form of `AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso_add`,
for the identifications `L(F_X^k)^* ≅ L(𝟙 X)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarIterateFrobeniusIso_trans_leftDerivedUpperStarId_add_hom_app
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarIterateFrobeniusIso A hp hX (m + n) ≪≫
        leftDerivedUpperStarId A X).hom.app M =
      (leftDerivedUpperStarComp A (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n)
          (X.iterateFrobenius hp hX (m + n)) (iterateFrobenius_add hp X hX m n)).hom.app M ≫
        L((X.iterateFrobenius hp hX m)^*[A]).map
          ((leftDerivedUpperStarIterateFrobeniusIso A hp hX n ≪≫
            leftDerivedUpperStarId A X).hom.app M) ≫
        (leftDerivedUpperStarIterateFrobeniusIso A hp hX m ≪≫ leftDerivedUpperStarId A X).hom.app
          M := by
  have h := NatTrans.congr_app (congrArg Iso.hom
    (leftDerivedUpperStarIterateFrobeniusIso_add A hp hX m n)) M
  have hr : (leftDerivedUpperStarComp A (X.iterateFrobenius hp hX m) (𝟙 X)
      (X.iterateFrobenius hp hX m) (Category.comp_id _).symm).inv.app M =
        L((X.iterateFrobenius hp hX m)^*[A]).map ((leftDerivedUpperStarId A X).hom.app M) := by
    rw [← cancel_epi ((leftDerivedUpperStarComp A (X.iterateFrobenius hp hX m) (𝟙 X)
      (X.iterateFrobenius hp hX m) (Category.comp_id _).symm).hom.app M), Iso.hom_inv_id_app,
      leftDerivedUpperStarComp_id_right_hom_app]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, hr] at h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc, ← h]

/-- If an isomorphism `θ : L(g)^* ≅ L(𝟙 X)^*`, for an endomorphism `g = 𝟙 X`, is compatible with
the factorization `g = g ≫ g` in the sense of
`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso_add`, then `θ` is the identity,
up to the identification `g = 𝟙 X`. -/
lemma leftDerivedUpperStar_hom_app_eq_eqToHom_of_comp {g : X ⟶ X} (hg : g = 𝟙 X)
    (θ : L((g)^*[A]) ≅ L((𝟙 X)^*[A])) (hgg : g = g ≫ g)
    (h : leftDerivedUpperStarComp A g g g hgg ≪≫ Functor.isoWhiskerRight θ L((g)^*[A]) ≪≫
      (leftDerivedUpperStarComp A g (𝟙 X) g (Category.comp_id _).symm).symm ≪≫ θ = θ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    θ.hom.app M = eqToHom (by rw [hg]) := by
  subst hg
  have hl (N : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      (leftDerivedUpperStarComp A (𝟙 X) (𝟙 X) (𝟙 X) hgg).hom.app N ≫
        (leftDerivedUpperStarId A X).hom.app (L((𝟙 X)^*[A]).obj N) = 𝟙 _ :=
    leftDerivedUpperStarComp_id_left_hom_app A (𝟙 X) N
  have hr (N : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      (leftDerivedUpperStarComp A (𝟙 X) (𝟙 X) (𝟙 X) (Category.comp_id _).symm).inv.app N =
        L((𝟙 X)^*[A]).map ((leftDerivedUpperStarId A X).hom.app N) := by
    rw [← cancel_epi ((leftDerivedUpperStarComp A (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.comp_id _).symm).hom.app N), Iso.hom_inv_id_app,
      leftDerivedUpperStarComp_id_right_hom_app]
  -- `θ` is the identity on the objects `L(𝟙)^* N`
  have hf (N : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      θ.hom.app (L((𝟙 X)^*[A]).obj N) = 𝟙 _ := by
    have h₁ := NatTrans.congr_app (congrArg Iso.hom h) N
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, hr] at h₁
    have hn₁ := θ.hom.naturality (θ.hom.app N ≫ (leftDerivedUpperStarId A X).hom.app N)
    have hn₂ := (leftDerivedUpperStarId A X).hom.naturality
      (θ.hom.app N ≫ (leftDerivedUpperStarId A X).hom.app N)
    simp only [Functor.id_map, Functor.id_obj] at hn₁ hn₂
    have e : L((𝟙 X)^*[A]).map (θ.hom.app N ≫ (leftDerivedUpperStarId A X).hom.app N) ≫
        θ.hom.app N ≫ (leftDerivedUpperStarId A X).hom.app N =
        (θ.hom.app (L((𝟙 X)^*[A]).obj N) ≫
          (leftDerivedUpperStarId A X).hom.app (L((𝟙 X)^*[A]).obj N)) ≫
          θ.hom.app N ≫ (leftDerivedUpperStarId A X).hom.app N := by
      rw [reassoc_of% hn₁, hn₂, Category.assoc]
    have h₂ : (leftDerivedUpperStarComp A (𝟙 X) (𝟙 X) (𝟙 X) hgg).hom.app N ≫
        (θ.hom.app (L((𝟙 X)^*[A]).obj N) ≫
          (leftDerivedUpperStarId A X).hom.app (L((𝟙 X)^*[A]).obj N)) ≫
          θ.hom.app N ≫ (leftDerivedUpperStarId A X).hom.app N =
        θ.hom.app N ≫ (leftDerivedUpperStarId A X).hom.app N := by
      rw [← e, Functor.map_comp]
      simpa only [Category.assoc] using h₁ =≫ (leftDerivedUpperStarId A X).hom.app N
    rw [← Category.assoc] at h₂
    have h₃ := (cancel_mono _).1 (h₂.trans (Category.id_comp _).symm)
    rw [← hl N, cancel_epi] at h₃
    exact (cancel_mono _).1 (h₃.trans (Category.id_comp _).symm)
  have hn := θ.hom.naturality ((leftDerivedUpperStarId A X).hom.app M)
  rw [hf, Category.id_comp] at hn
  rw [eqToHom_refl]
  exact (cancel_epi _).1 (hn.trans (Category.comp_id _).symm)

/-- The identification `L(F_X^0)^* ≅ L(𝟙 X)^*` of
`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso` is the identity, up to the
identification `F_X^0 = 𝟙 X`. -/
lemma leftDerivedUpperStarIterateFrobeniusIso_zero_hom_app
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarIterateFrobeniusIso A hp hX 0).hom.app M =
      eqToHom (by rw [Scheme.iterateFrobenius_zero]) :=
  leftDerivedUpperStar_hom_app_eq_eqToHom_of_comp A (Scheme.iterateFrobenius_zero hp X hX) _
    (Scheme.iterateFrobenius_add hp X hX 0 0)
    (leftDerivedUpperStarIterateFrobeniusIso_add A hp hX 0 0) M

end Derived

section Point

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The inverse of the composition isomorphism `L(𝟙 ≫ y)^* ≅ Ly^* ⋙ L(𝟙)^*` is the identity
isomorphism `L(𝟙)^* ≅ 𝟭` at `Ly^* K`. -/
lemma leftDerivedUpperStarComp_id_left_inv_app {S T : Scheme.{u}} (y : S ⟶ T)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A (𝟙 S) y y (Category.id_comp y).symm).inv.app K =
      (leftDerivedUpperStarId A S).hom.app (L((y)^*[A]).obj K) := by
  rw [← cancel_epi ((leftDerivedUpperStarComp A (𝟙 S) y y (Category.id_comp y).symm).hom.app K),
    Iso.hom_inv_id_app, leftDerivedUpperStarComp_id_left_hom_app]

/-- The inverse of the composition isomorphism `L(𝟙 ≫ w)^* ≅ Lw^* ⋙ L(𝟙)^*`, for a morphism `z`
equal to `𝟙 ≫ w`, is the identity isomorphism `L(𝟙)^* ≅ 𝟭` up to the cast. -/
lemma leftDerivedUpperStarComp_id_left_inv_app_of_eq {S T : Scheme.{u}} {w z : S ⟶ T}
    (hz : z = 𝟙 S ≫ w) (K : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A (𝟙 S) w z hz).inv.app K =
      (leftDerivedUpperStarId A S).hom.app (L((w)^*[A]).obj K) ≫
        eqToHom (by rw [hz, Category.id_comp]; rfl) := by
  obtain rfl : z = w := hz.trans (Category.id_comp w)
  rw [eqToHom_refl, Category.comp_id]
  exact leftDerivedUpperStarComp_id_left_inv_app _ _ K

/-- The inverse of the composition isomorphism `L(y ≫ 𝟙)^* ≅ L(𝟙)^* ⋙ Ly^*` is `Ly^*` applied to
the identity isomorphism `L(𝟙)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarComp_id_right_inv_app {S T : Scheme.{u}} (y : S ⟶ T)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A y (𝟙 T) y (Category.comp_id y).symm).inv.app K =
      L((y)^*[A]).map ((leftDerivedUpperStarId A T).hom.app K) := by
  rw [← cancel_epi ((leftDerivedUpperStarComp A y (𝟙 T) y (Category.comp_id y).symm).hom.app K),
    Iso.hom_inv_id_app, leftDerivedUpperStarComp_id_right_hom_app]

/-- For an endomorphism `g = 𝟙 S`, the composition isomorphism `L(g ≫ w)^* ≅ Lw^* ⋙ Lg^*`
followed by `Lg^* = L(𝟙)^* ≅ 𝟭` is the identity. -/
lemma leftDerivedUpperStarComp_hom_app_eqToHom_leftDerivedUpperStarId_hom_app {S T : Scheme.{u}}
    {g : S ⟶ S} (hg : g = 𝟙 S) {w y : S ⟶ T} (h : y = g ≫ w) (hy : y = w)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A g w y h).hom.app K ≫ eqToHom (by rw [hg]; rfl) ≫
      (leftDerivedUpperStarId A S).hom.app (L((w)^*[A]).obj K) = eqToHom (by rw [hy]; rfl) := by
  subst hg hy
  rw [eqToHom_refl, Category.id_comp, eqToHom_refl]
  exact leftDerivedUpperStarComp_id_left_hom_app A y K

/-- For endomorphisms `g = 𝟙 X` and `g' = 𝟙 X` and an isomorphism `e : Lg^* ≅ Lg'^*` which is
the identity at `K`, the composite `Ly^* K ≅ Lx^* Lg^* K ≅ Lx^* Lg'^* K ≅ Lz^* K` is the
identity, for `y = x ≫ g` and `z = x ≫ g'`. -/
lemma leftDerivedUpperStarComp_hom_app_map_comp_inv_app_of_eq_id {S X : Scheme.{u}} (x : S ⟶ X)
    {g g' : X ⟶ X} (hg : g = 𝟙 X) (hg' : g' = 𝟙 X) (e : L((g)^*[A]) ≅ L((g')^*[A]))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (he : e.hom.app K = eqToHom (by rw [hg, hg'])) {y z : S ⟶ X} (hy : y = x ≫ g)
    (hz : z = x ≫ g') (hyz : y = z) :
    (leftDerivedUpperStarComp A x g y hy).hom.app K ≫ L((x)^*[A]).map (e.hom.app K) ≫
      (leftDerivedUpperStarComp A x g' z hz).inv.app K = eqToHom (by rw [hyz]) := by
  subst hg hg' hyz hy
  rw [he]
  simp

variable {p : ℕ} (hp : p.Prime) {X S : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0)
  (hS : (p : Γ(S, ⊤)) = 0) (n : ℕ)

/-- Let `Φ = F_X^n ≫ γ` for an endomorphism `γ` of a scheme `X` of characteristic `p`, and let
`κ : LΦ^* ≅ Lγ^*` be the identification
`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfFactor` induced by
`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`. Pulled back along a morphism
`x : S ⟶ X` from a scheme of characteristic `p`, `κ` becomes the identification
`L(F_S^n)^* ≅ L(𝟙 S)^* ≅ 𝟭`, through `x ≫ Φ = F_S^n ≫ x ≫ γ`. -/
lemma leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarIsoOfFactor_hom_app
    {Φ γ : X ⟶ X} (hF : X.iterateFrobenius hp hX n ≫ γ = Φ) (x : S ⟶ X) {x₁ w : S ⟶ X}
    (hx₁ : x₁ = x ≫ Φ) (hw : w = x ≫ γ) (hx₁' : x₁ = S.iterateFrobenius hp hS n ≫ w)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A x Φ x₁ hx₁).hom.app M ≫
      L((x)^*[A]).map ((leftDerivedUpperStarIsoOfFactor A hF
        (leftDerivedUpperStarIterateFrobeniusIso A hp hX n)).hom.app M) ≫
      (leftDerivedUpperStarComp A x γ w hw).inv.app M =
    (leftDerivedUpperStarComp A (S.iterateFrobenius hp hS n) w x₁ hx₁').hom.app M ≫
      (leftDerivedUpperStarIterateFrobeniusIso A hp hS n ≪≫ leftDerivedUpperStarId A S).hom.app
        (L((w)^*[A]).obj M) := by
  have hFx : S.iterateFrobenius hp hS n ≫ x = x ≫ X.iterateFrobenius hp hX n :=
    (comp_iterateFrobenius hp x hX hS n).symm
  have a₁ := leftDerivedUpperStarComp_assoc'_app A x (X.iterateFrobenius hp hX n) γ
    (S.iterateFrobenius hp hS n ≫ x) Φ x₁ hFx hF.symm (by rw [hx₁', hw, Category.assoc]) M
  have a₂ := leftDerivedUpperStarComp_assoc'_app A (S.iterateFrobenius hp hS n) x γ
    (S.iterateFrobenius hp hS n ≫ x) w x₁ rfl hw (by rw [hx₁', hw, Category.assoc]) M
  have n₁ := leftDerivedUpperStarIterateFrobeniusIso_naturality_app A hp hS n hX x hFx
    (L((γ)^*[A]).obj M)
  rw [leftDerivedUpperStarComp_id_right_inv_app, leftDerivedUpperStarComp_id_left_inv_app] at n₁
  have a₂' : (leftDerivedUpperStarComp A (S.iterateFrobenius hp hS n) w x₁ hx₁').hom.app M =
      (leftDerivedUpperStarComp A (S.iterateFrobenius hp hS n ≫ x) γ x₁
          (by rw [hx₁', hw, Category.assoc])).hom.app M ≫
        (leftDerivedUpperStarComp A (S.iterateFrobenius hp hS n) x
          (S.iterateFrobenius hp hS n ≫ x) rfl).hom.app (L((γ)^*[A]).obj M) ≫
        L((S.iterateFrobenius hp hS n)^*[A]).map
          ((leftDerivedUpperStarComp A x γ w hw).inv.app M) := by
    rw [← reassoc_of% a₂, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hϑ := (leftDerivedUpperStarIterateFrobeniusIso A hp hS n ≪≫
    leftDerivedUpperStarId A S).hom.naturality ((leftDerivedUpperStarComp A x γ w hw).inv.app M)
  simp only [Functor.id_map, Functor.comp_obj, Iso.trans_hom, NatTrans.comp_app] at hϑ
  rw [leftDerivedUpperStarIsoOfFactor_hom_app, leftDerivedUpperStarComp_id_left_inv_app]
  simp only [Functor.map_comp, Category.assoc, Iso.trans_hom, NatTrans.comp_app]
  rw [reassoc_of% a₁, reassoc_of% n₁, a₂']
  simp only [Category.assoc]
  rw [Category.assoc] at hϑ
  exact congrArg (fun t ↦ _ ≫ _ ≫ t) hϑ.symm

/-- **The iterates of `κ` at a point.** Let `Φ = F_X^n ≫ γ` for an endomorphism `γ` of a scheme
`X` of characteristic `p`, let `κ : LΦ^* ≅ Lγ^*` be the identification
`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfFactor` induced by
`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`, and let
`κ_m : L(Φ^m)^* ≅ L(γ^m)^*` be its iterates
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateHomIso`). Pulled back along a morphism
`x : S ⟶ X` from a scheme of characteristic `p`, `κ_m` becomes the identification
`L(F_S^{nm})^* ≅ L(𝟙 S)^* ≅ 𝟭`, through `x ≫ Φ^m = F_S^{nm} ≫ x ≫ γ^m`. -/
theorem leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarIterateHomIso_hom_app
    {Φ γ : X ⟶ X} (hF : X.iterateFrobenius hp hX n ≫ γ = Φ) (m : ℕ) (x : S ⟶ X) {y z : S ⟶ X}
    (hy : y = x ≫ ProEtale.iterateHom Φ m) (hz : z = x ≫ ProEtale.iterateHom γ m)
    (hyz : y = S.iterateFrobenius hp hS (n * m) ≫ z)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A x (ProEtale.iterateHom Φ m) y hy).hom.app K ≫
      L((x)^*[A]).map ((leftDerivedUpperStarIterateHomIso (leftDerivedUpperStarIsoOfFactor A hF
        (leftDerivedUpperStarIterateFrobeniusIso A hp hX n)) m).hom.app K) ≫
      (leftDerivedUpperStarComp A x (ProEtale.iterateHom γ m) z hz).inv.app K =
    (leftDerivedUpperStarComp A (S.iterateFrobenius hp hS (n * m)) z y hyz).hom.app K ≫
      (leftDerivedUpperStarIterateFrobeniusIso A hp hS (n * m) ≪≫
        leftDerivedUpperStarId A S).hom.app (L((z)^*[A]).obj K) := by
  induction m generalizing x y z with
  | zero =>
    have hyz' : y = z := by rw [hy, hz, ProEtale.iterateHom_zero, ProEtale.iterateHom_zero]
    revert hyz
    rw [Nat.mul_zero]
    intro hyz
    rw [Iso.trans_hom, NatTrans.comp_app, leftDerivedUpperStarIterateFrobeniusIso_zero_hom_app,
      leftDerivedUpperStarComp_hom_app_eqToHom_leftDerivedUpperStarId_hom_app A
        (Scheme.iterateFrobenius_zero hp S hS) hyz hyz',
      leftDerivedUpperStarComp_hom_app_map_comp_inv_app_of_eq_id A x
        (ProEtale.iterateHom_zero Φ) (ProEtale.iterateHom_zero γ)
        (leftDerivedUpperStarIterateHomIso (leftDerivedUpperStarIsoOfFactor A hF
          (leftDerivedUpperStarIterateFrobeniusIso A hp hX n)) 0) K
        (by rw [leftDerivedUpperStarIterateHomIso_zero]; rfl) hy hz hyz']
  | succ m ih =>
    have hx₁' : x ≫ Φ = S.iterateFrobenius hp hS n ≫ x ≫ γ := by
      rw [← hF]
      simp only [← Category.assoc, comp_iterateFrobenius hp x hX hS n]
    have hy₁ : y = (x ≫ Φ) ≫ ProEtale.iterateHom Φ m := by
      rw [hy, ProEtale.iterateHom_succ, Category.assoc]
    have hz' : z = (x ≫ γ) ≫ ProEtale.iterateHom γ m := by
      rw [hz, ProEtale.iterateHom_succ, Category.assoc]
    have hz₁ : (x ≫ Φ) ≫ ProEtale.iterateHom γ m = S.iterateFrobenius hp hS n ≫ z := by
      rw [hx₁', hz']
      simp only [Category.assoc]
    have hyz₁ : y = S.iterateFrobenius hp hS (n * m) ≫ (x ≫ Φ) ≫ ProEtale.iterateHom γ m := by
      rw [hz₁, hyz, Nat.mul_add_one, Scheme.iterateFrobenius_add, Category.assoc]
    have hyz₂ : y = S.iterateFrobenius hp hS (n * m + n) ≫ z := by
      rw [hyz, Nat.mul_add_one]
    have ih' := ih (x ≫ Φ) hy₁ rfl hyz₁
    rw [← cancel_mono ((leftDerivedUpperStarComp A (x ≫ Φ) (ProEtale.iterateHom γ m)
      ((x ≫ Φ) ≫ ProEtale.iterateHom γ m) rfl).hom.app K)] at ih'
    simp only [Category.assoc, Iso.inv_hom_id_app] at ih'
    have b := leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarIsoOfFactor_hom_app A hp hX
      hS n hF x rfl rfl hx₁' (L((ProEtale.iterateHom γ m)^*[A]).obj K)
    rw [← cancel_mono ((leftDerivedUpperStarComp A x γ (x ≫ γ) rfl).hom.app
      (L((ProEtale.iterateHom γ m)^*[A]).obj K))] at b
    simp only [Category.assoc, Iso.inv_hom_id_app] at b
    have a₁ := leftDerivedUpperStarComp_assoc'_app A x Φ (ProEtale.iterateHom Φ m) (x ≫ Φ)
      (ProEtale.iterateHom Φ (m + 1)) y rfl (ProEtale.iterateHom_succ Φ m) hy₁ K
    have n₂ := ((leftDerivedUpperStarComp A x Φ (x ≫ Φ) rfl).hom.naturality
      ((leftDerivedUpperStarIterateHomIso (leftDerivedUpperStarIsoOfFactor A hF
        (leftDerivedUpperStarIterateFrobeniusIso A hp hX n)) m).hom.app K)).symm
    simp only [Functor.comp_map] at n₂
    have a₃ := map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app A x γ
      (ProEtale.iterateHom γ m) (x ≫ γ) (ProEtale.iterateHom γ (m + 1)) z rfl
      (ProEtale.iterateHom_succ γ m) hz' K
    have a₄ := leftDerivedUpperStarComp_assoc'_app A (S.iterateFrobenius hp hS n) (x ≫ γ)
      (ProEtale.iterateHom γ m) (x ≫ Φ) z ((x ≫ Φ) ≫ ProEtale.iterateHom γ m) hx₁' hz' rfl K
    have n₃ := (leftDerivedUpperStarIterateFrobeniusIso A hp hS n ≪≫
      leftDerivedUpperStarId A S).hom.naturality
        ((leftDerivedUpperStarComp A (x ≫ γ) (ProEtale.iterateHom γ m) z hz').hom.app K)
    simp only [Functor.id_map] at n₃
    have n₄ := (leftDerivedUpperStarIterateFrobeniusIso A hp hS (n * m) ≪≫
      leftDerivedUpperStarId A S).hom.naturality
        ((leftDerivedUpperStarComp A (S.iterateFrobenius hp hS n) z
          ((x ≫ Φ) ≫ ProEtale.iterateHom γ m) hz₁).hom.app K ≫
          (leftDerivedUpperStarIterateFrobeniusIso A hp hS n ≪≫
            leftDerivedUpperStarId A S).hom.app (L((z)^*[A]).obj K))
    simp only [Functor.id_map, Functor.id_obj] at n₄
    have a₅ := leftDerivedUpperStarComp_assoc'_app A (S.iterateFrobenius hp hS (n * m))
      (S.iterateFrobenius hp hS n) z (S.iterateFrobenius hp hS (n * m + n))
      ((x ≫ Φ) ≫ ProEtale.iterateHom γ m) y (Scheme.iterateFrobenius_add hp S hS (n * m) n)
      hz₁ hyz₂ K
    have d := leftDerivedUpperStarIterateFrobeniusIso_trans_leftDerivedUpperStarId_add_hom_app A
      hp hS (n * m) n (L((z)^*[A]).obj K)
    rw [leftDerivedUpperStarIterateHomIso_succ_hom_app]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% a₁, reassoc_of% n₂, reassoc_of% ih', reassoc_of% b, a₃,
      Iso.hom_inv_id_app_assoc, ← reassoc_of% a₄, reassoc_of% n₃, Iso.hom_inv_id_app,
      Category.comp_id, ← n₄, Functor.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% a₅, ← d]
    rfl

end Point

end Etale

end AlgebraicGeometry
