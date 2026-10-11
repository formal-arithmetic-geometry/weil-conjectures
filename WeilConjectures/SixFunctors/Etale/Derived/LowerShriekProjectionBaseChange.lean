/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# The projection map of the compactly supported direct image commutes with base change

For a cartesian square `g' ≫ f = f' ≫ g` and a compactification `c` of `f`, the projection map
`PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)`
(`AlgebraicGeometry.Etale.projectionMapOfCompactification`) commutes with the compactly supported
base change map `Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`), where `c'` is
the base changed compactification, and the tensor comparisons of the derived pullbacks.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

lemma leftDerivedUpperStarComp_symm_trans_eqToIso {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R)
    (k : T ⟶ R) (e : k = a ≫ b) :
    (leftDerivedUpperStarComp A a b).symm ≪≫ eqToIso (congrArg (fun h : T ⟶ R ↦ L((h)^*[A])) e.symm) =
      (leftDerivedUpperStarComp A a b k e).symm := by
  subst e
  ext
  simp

lemma leftDerivedUpperStarCompactificationIso_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    leftDerivedUpperStarCompactificationIso A c =
      (leftDerivedUpperStarComp A c.i c.g f c.comm).symm :=
  leftDerivedUpperStarComp_symm_trans_eqToIso A c.i c.g f c.comm

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : CommSq g' f' f g) (c : Compactification f) (c' : Compactification f') (q : c'.Z ⟶ c.Z)
  (hi : IsPullback g' c'.i c.i q) (hp : CommSq q c'.g c.g g)

/-- The compatibility of the square isomorphisms of the derived pullbacks for the squares of a
compactification `c` of `f` and of a compactification `c'` of its base change `f'`, lying over
`c` through `q`, with the isomorphisms `L(c.i)^* L(c.g)^* ≅ Lf^*` and
`L(c'.i)^* L(c'.g)^* ≅ Lf'^*`. -/
lemma compactification_derivedSquareUpperStarIso
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((c'.i)^*[A]).map ((derivedSquareUpperStarIso A hp).hom.app L) ≫
      (derivedSquareUpperStarIso A hi.toCommSq).hom.app (L((c.g)^*[A]).obj L) ≫
      L((g')^*[A]).map ((leftDerivedUpperStarCompactificationIso A c).hom.app L) ≫
      (derivedSquareUpperStarIso A sq).inv.app L =
    (leftDerivedUpperStarCompactificationIso A c').hom.app (L((g)^*[A]).obj L) := by
  rw [leftDerivedUpperStarCompactificationIso_eq, leftDerivedUpperStarCompactificationIso_eq]
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app_assoc A g' c.i c.g
      (g' ≫ c.i) f (g' ≫ f) rfl c.comm (by rw [Category.assoc, ← c.comm]),
    Iso.hom_inv_id_app_assoc,
    map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app_assoc A
      c'.i q c.g (g' ≫ c.i) (q ≫ c.g) (g' ≫ f) hi.w rfl (by rw [Category.assoc, ← c.comm]),
    Iso.hom_inv_id_app_assoc,
    map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app_assoc A
      c'.i c'.g g f' (q ≫ c.g) (g' ≫ f) c'.comm hp.w sq.w,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]

end Etale

end AlgebraicGeometry
