/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.AbsoluteFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

/-!
# The absolute Frobenius acts trivially on the small pro-étale site

Let `X` be a scheme in which the prime `p` vanishes and `F_X` its `p ^ n`-power absolute
Frobenius. For every object `v : V ⟶ X` of the small pro-étale site the relative Frobenius
`r_V = (F_V, v) : V ⟶ V ×_{X, F_X} X` is a weakly étale universal homeomorphism, hence an
isomorphism (`AlgebraicGeometry.Scheme.isIso_relativeIterateFrobenius`). These isomorphisms are
natural in `V`, so base change along `F_X` is isomorphic to the identity functor of `X_proét`.
Consequently the pushforward `F_{X*}`, the pullback `F_X^*` and the derived pullback `LF_X^*`
are canonically isomorphic to the identity. These trivializations are compatible with base
change along any morphism (in particular with restriction to open subschemes) and with
the iterates `F_X^{(m + n)} = F_X^{(n)} ∘ F_X^{(m)}`.

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.overPullbackIterateFrobeniusIso`: base change along `F_X`
  is isomorphic to the identity of `X_proét`.
- `AlgebraicGeometry.ProEtale.lowerStarIterateFrobeniusIso`,
  `AlgebraicGeometry.ProEtale.upperStarIterateFrobeniusIso`: `F_{X*} ≅ 𝟭` and `F_X^* ≅ 𝟭`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarIterateFrobeniusIso`
  (`lem-trf-absolute-frobenius-site`): the canonical trivialization `LF_X^* ≅ 𝟭`.

## Main statements

- `AlgebraicGeometry.Scheme.ProEt.overPullbackIterateFrobeniusIso_add`: compatibility with the
  iterates.
- `AlgebraicGeometry.Scheme.ProEt.overPullbackIterateFrobeniusIso_overPullback`: compatibility
  with base change along a morphism `f : Y ⟶ X`, e.g. restriction to an open subscheme.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MorphismProperty

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)

namespace Scheme.ProEt

/-- The relative Frobenius `r_V : V ⟶ V ×_{X, F_X} X` of an object `V` of the small pro-étale
site of `X`, as an isomorphism in `X_proét`. -/
noncomputable def relativeIterateFrobeniusIso (V : X.ProEt) :
    V ≅ (Over.pullback @WeaklyEtale ⊤ (X.iterateFrobenius hp hX n)).obj V :=
  Over.isoMk (asIso (relativeIterateFrobenius hp n hX V.hom)) (by simp)

@[simp]
lemma relativeIterateFrobeniusIso_hom_left (V : X.ProEt) :
    (relativeIterateFrobeniusIso hp hX n V).hom.left = relativeIterateFrobenius hp n hX V.hom :=
  rfl

/-- Base change along the absolute Frobenius `F_X` is isomorphic to the identity functor of the
small pro-étale site of `X`, through the relative Frobenius maps. -/
noncomputable def overPullbackIterateFrobeniusIso :
    Over.pullback @WeaklyEtale ⊤ (X.iterateFrobenius hp hX n) ≅ 𝟭 X.ProEt :=
  (NatIso.ofComponents (relativeIterateFrobeniusIso hp hX n) fun {V W} g ↦ by
    ext : 1
    apply pullback.hom_ext
    · simpa using iterateFrobenius_naturality hp n g.left _ _
    · simp).symm

@[simp]
lemma overPullbackIterateFrobeniusIso_inv_app_left (V : X.ProEt) :
    ((overPullbackIterateFrobeniusIso hp hX n).inv.app V).left =
      relativeIterateFrobenius hp n hX V.hom :=
  rfl


/-- The relative Frobenius maps are compatible with the iterates: `r^{(m + n)}_V` is the
composite of `r^{(m)}_V` and the base change of `r^{(n)}_V` along `F_X^{(m)}`, read through
`V ×_{X, F^{(m + n)}} X ≅ (V ×_{X, F^{(n)}} X) ×_{X, F^{(m)}} X`. -/
lemma relativeIterateFrobeniusIso_add (m : ℕ) (V : X.ProEt) :
    (overPullbackIterateFrobeniusIso hp hX m).inv.app V ≫
        (Over.pullback @WeaklyEtale ⊤ (X.iterateFrobenius hp hX m)).map
          ((overPullbackIterateFrobeniusIso hp hX n).inv.app V) ≫
        (MorphismProperty.Over.pullbackComp (X.iterateFrobenius hp hX m)
          (X.iterateFrobenius hp hX n)).inv.app V ≫
        (MorphismProperty.Over.pullbackCongr (iterateFrobenius_add hp n X hX m)).inv.app V =
      (overPullbackIterateFrobeniusIso hp hX (m + n)).inv.app V := by
  ext : 1
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
      iterateFrobenius_add]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]
end Scheme.ProEt

namespace ProEtale


/-- The pushforward `F_{X*}` along the absolute Frobenius on pro-étale sheaves is isomorphic to
the identity: `(F_{X*} G)(V) = G(V ×_{X, F_X} X) ≅ G(V)` through the relative Frobenius maps. -/
noncomputable def lowerStarIterateFrobeniusIso : (X.iterateFrobenius hp hX n)_*[A] ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (Scheme.ProEt.overPullbackIterateFrobeniusIso hp hX n) A
    (Scheme.ProEt.topology X)

/-- The pullback `F_X^*` along the absolute Frobenius on pro-étale sheaves is isomorphic to the
identity, by uniqueness of left adjoints: both are left adjoint to `F_{X*} ≅ 𝟭`. -/
noncomputable def upperStarIterateFrobeniusIso : (X.iterateFrobenius hp hX n)^*[A] ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction A _)).symm
    (lowerStarIterateFrobeniusIso A hp hX n).symm

lemma conjugateIsoEquiv_upperStarIterateFrobeniusIso :
    conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction A _)
        (upperStarIterateFrobeniusIso A hp hX n) = (lowerStarIterateFrobeniusIso A hp hX n).symm :=
  Equiv.apply_symm_apply _ _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the trivialization `F_{X*} ≅ 𝟭` are the restriction maps along the relative
Frobenius maps `r_V : V ⟶ V ×_{X, F_X} X`. -/
lemma lowerStarIterateFrobeniusIso_hom_app_hom_app (G : Sheaf (ProEt.topology X) A)
    (V : X.ProEtᵒᵖ) :
    ((lowerStarIterateFrobeniusIso A hp hX n).hom.app G).hom.app V =
      G.obj.map ((ProEt.overPullbackIterateFrobeniusIso hp hX n).inv.app V.unop).op := by
  simp [lowerStarIterateFrobeniusIso]

/-- The trivializations `F_{X*} ≅ 𝟭` are compatible with the iterates
`F_X^{(m + n)} = F_X^{(m)} ≫ F_X^{(n)}`. -/
lemma lowerStarIterateFrobeniusIso_add (m : ℕ) :
    lowerStarCongr A (iterateFrobenius_add hp n X hX m) ≪≫
        (lowerStarComp A (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n)).symm ≪≫
        Functor.isoWhiskerLeft _ (lowerStarIterateFrobeniusIso A hp hX n) ≪≫
        Functor.rightUnitor _ ≪≫ lowerStarIterateFrobeniusIso A hp hX m =
      lowerStarIterateFrobeniusIso A hp hX (m + n) := by
  ext G V
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, lowerStarCongr_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarIterateFrobeniusIso_hom_app_hom_app, lowerStar_obj_obj_map',
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  exact ProEt.relativeIterateFrobeniusIso_add hp hX n m V.unop

/-- The trivializations `F_X^* ≅ 𝟭` are compatible with the iterates
`F_X^{(m + n)} = F_X^{(m)} ≫ F_X^{(n)}`: this is conjugate to
`AlgebraicGeometry.ProEtale.lowerStarIterateFrobeniusIso_add`. -/
lemma upperStarIterateFrobeniusIso_add (m : ℕ) :
    upperStarCongr A (iterateFrobenius_add hp n X hX m) ≪≫
        upperStarComp A (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n) ≪≫
        Functor.isoWhiskerRight (upperStarIterateFrobeniusIso A hp hX n) _ ≪≫
        Functor.leftUnitor _ ≪≫ upperStarIterateFrobeniusIso A hp hX m =
      upperStarIterateFrobeniusIso A hp hX (m + n) := by
  apply (conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction A _)).injective
  rw [conjugateIsoEquiv_trans Adjunction.id
      (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX m ≫ X.iterateFrobenius hp hX n)),
    conjugateIsoEquiv_trans Adjunction.id ((upperStarLowerStarAdjunction A _).comp
      (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX m))),
    conjugateIsoEquiv_trans Adjunction.id
      (Adjunction.id.comp (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX m))),
    conjugateIsoEquiv_trans Adjunction.id
      (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX m)),
    conjugateIsoEquiv_upperStarIterateFrobeniusIso, conjugateIsoEquiv_leftUnitor,
    conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_upperStarIterateFrobeniusIso,
    conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_upperStarIterateFrobeniusIso, ← lowerStarIterateFrobeniusIso_add A hp hX n m]
  ext : 1
  simp

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Blueprint `lem-trf-absolute-frobenius-site`: Canonical trivialization of absolute Frobenius
pullback.

Let `X` be a scheme in which the prime `p` vanishes. On the small pro-étale site of `X`, the
derived pullback along the `p ^ n`-power absolute Frobenius `F_X` has a canonical
trivialization `LF_X^* ≅ 𝟭`: the derived functor of the trivialization `F_X^* ≅ 𝟭` of the
(exact) pullback, which comes from the relative Frobenius isomorphisms
`r_V : V ≅ V ×_{X, F_X} X`. Its compatibility with the iterates is
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarIterateFrobeniusIso_add`, and with restriction
along any morphism (e.g. an open immersion) is
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarIterateFrobeniusIso_restrict`. -/
noncomputable def leftDerivedUpperStarIterateFrobeniusIso :
    L((X.iterateFrobenius hp hX n)^*[A]) ≅ 𝟭 _ :=
  Functor.leftDerivedFunctorIsoId _ (upperStarIterateFrobeniusIso A hp hX n)

end ProEtale

end AlgebraicGeometry
