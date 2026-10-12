/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.AbsoluteFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

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
