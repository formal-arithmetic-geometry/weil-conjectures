/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # Smooth-curve abelian level rigidification

Source: Pikaart--de Jong (1995), §§1.1 and 2.3.3--2.3.7, especially Proposition 2.3.4
(blueprint: lem-sfb-smooth-curve-abelian-level-rigidification).

## Main definitions

* `smoothCurveModuliBase`: the existing smooth moduli category over schemes.
* `abelianLevelForgetSmooth`: forget a frame, retaining its actual family.
* `smoothCurveModuliPullback`: the specified pullback family, with no frame chosen.

## Main statement

* `smoothCurveAbelianLevelRigidification`: fine smooth finite-type moduli, constant rank,
  canonical base change, finite etale surjective frame covers, rigidity and 2-fibre products.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Projection of the already defined smooth unpointed moduli category to its base schemes.
Source: Pikaart--de Jong §2.3.3
(blueprint: lem-sfb-smooth-curve-abelian-level-rigidification). -/
def smoothCurveModuliBase (S : Scheme.{u}) (g : ℕ) :
    StablePointedModuli.Smooth S g 0 ⥤ Over S :=
  ObjectProperty.ι _ ⋙ StablePointedModuli.forget S g 0

/-- Forget only the abelian frame; the cartesian family arrow is retained.
Source: Pikaart--de Jong §2.3.3
(blueprint: lem-sfb-smooth-curve-abelian-level-rigidification). -/
def abelianLevelForgetSmooth (S : Scheme.{u}) (g : ℕ) (ℓ : AbelianLevelPrime S) :
    BasedFunctor (BasedCategory.ofFunctor (AbelianLevelModuli.forget S g ℓ))
      (BasedCategory.ofFunctor (smoothCurveModuliBase S g)) where
  obj X := X.family
  map a := a.val

/-- The specified fibre-product family, with smoothness inherited by base change.
Source: Pikaart--de Jong §2.3.3
(blueprint: lem-sfb-smooth-curve-abelian-level-rigidification). -/
def smoothCurveModuliPullback {S : Scheme.{u}} {g : ℕ}
    (X : StablePointedModuli.Smooth S g 0) (T : Over S) (a : T ⟶ X.obj.base) :
    StablePointedModuli.Smooth S g 0 :=
  haveI : Smooth X.obj.projection := X.property
  ⟨X.obj.pullback T a, inferInstanceAs (Smooth (pullback.snd X.obj.projection a.left))⟩

/-- Full abelian level at a prime at least three rigidifies smooth genus-at-least-two curves.
The universal frame and its unique classifying maps express representability of the frame
functor on every test scheme, including the naturality: the arrow `q` is the map between the
specified pullbacks, determined by its base and first-projection equations. `HomCondition`
uses the canonical constant comparison and degree-one exchange, not an arbitrary transport.
The same `P` represents the 2-fibre product over `h_T`. The natural transformation `η`
classifies the actual family `X`: its components are cartesian family arrows over the
Yoneda test maps. Thus the comma comparison is an actual family isomorphism in a fibre.

Source: Pikaart--de Jong (1995), §§1.1 and 2.3.3--2.3.7, Proposition 2.3.4 and Remark 2.3.7
(blueprint: lem-sfb-smooth-curve-abelian-level-rigidification).

Proof plan:
1. By lem-trf-projective-bundle-proper the families are proper. Apply
   lem-sfb-smooth-proper-finite-cohomology-local-system to constant prime coefficients.
   The canonical comparison of lemma-weil-pbc-prime-proper-base-change identifies every
   geometric stalk with fibre cohomology. By thm-sc-proper-cohomology its rank is `2g`.
   Hence an etale cover trivializes the sheaf with exactly that rank, over arbitrary bases.
2. In these trivializations the frame sheaf is the constant finite nonempty set
   GL(2g, F_ell). By lem-galois-flc-representable it is represented by a finite etale `P`.
   By lem-galois-stalk-representable its geometric fibres are nonempty, so it is surjective.
   By lem-galois-inverse-image-representable and canonical base change, its sections on
   every test scheme are exactly the frames of the base-changed family, naturally.
3. In the 2-fibre product an object is `(Y, λ, φ)` with an actual isomorphism
   `φ : Y ≅ X_T'`. Transport `λ` by the inverse of `φ*`. The inverse sends a frame `α`
   to `(X_T', α, id)`. The unique arrow is `(φ')⁻¹ φ`; it preserves frames exactly when
   transported frames agree. Naturality of the canonical exchange gives base naturality.
4. By lem-sfb-abelian-level-coarse-moduli the level category is a smooth finite-type DM
   stack with coarse scheme. By lem-sfb-geometric-curve-level-faithfulness its geometric
   inertia is trivial. By lem-sfb-dm-geometric-inertia-trivial it is an algebraic space,
   and automorphisms are trivial on all test schemes, including nonreduced ones.
5. Apply the coarse universal property with this algebraic space as target to obtain an
   inverse to the coarse map. Uniqueness gives both inverse identities. The coarse scheme
   therefore represents the full category; it is finite type and smooth, as is the stack.
6. Replace the level category in Step 3 by its representative. Together with Step 2 this
   yields the asserted equivalence over `h_T` with the discrete frame functor. No rational
   frame, root of unity or symplectic condition was chosen. The empty base is allowed.
-/
theorem smoothCurveAbelianLevelRigidification (k : Type u) [Field k]
    (g : ℕ) (hg : 2 ≤ g) (ℓ : AbelianLevelPrime (Spec (.of k))) :
    ∃ L : Over (Spec (.of k)),
      Smooth L.hom ∧ LocallyOfFiniteType L.hom ∧ QuasiCompact L.hom ∧
      IsRepresentedByScheme
        (BasedCategory.ofFunctor (AbelianLevelModuli.forget (Spec (.of k)) g ℓ)) L ∧
      (∀ (T : Over (Spec (.of k)))
        (Y : AbelianLevelModuli.Fiber (Spec (.of k)) g ℓ T) (a : Y ⟶ Y), a = 𝟙 Y) ∧
      ∀ X : StablePointedModuli.Smooth (Spec (.of k)) g 0,
        (∃ 𝒰 : X.obj.base.left.Cover.{u} (Scheme.precoverage @Etale),
          ∀ i : 𝒰.I₀,
            Nonempty ((Etale.upperStar
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ.val))) (𝒰.f i)).obj
                (abelianLevelCohomology X.obj.projection ℓ.val) ≅
                  abelianLevelConstant (𝒰.X i) g ℓ.val)) ∧
        (∀ (T : Over (Spec (.of k))) (a : T ⟶ X.obj.base),
          IsIso (abelianLevelBaseChange
            (IsPullback.of_hasPullback X.obj.projection a.left).toCommSq ℓ.val)) ∧
        ∃ (P : Over (Spec (.of k))) (r : P ⟶ X.obj.base),
          IsFinite r.left ∧ Etale r.left ∧ Surjective r.left ∧
          ∃ frameP : abelianLevelConstant P.left g ℓ.val ≅
            abelianLevelCohomology (smoothCurveModuliPullback X P r).obj.projection ℓ.val,
            (∀ (T : Over (Spec (.of k))) (a : T ⟶ X.obj.base)
              (α : abelianLevelConstant T.left g ℓ.val ≅
                abelianLevelCohomology
                  (smoothCurveModuliPullback X T a).obj.projection ℓ.val),
              ∃! b : T ⟶ P, b ≫ r = a ∧
                ∃ q : smoothCurveModuliPullback X T a ⟶ smoothCurveModuliPullback X P r,
                  q.hom.base = b ∧
                  q.hom.map ≫ pullback.fst X.obj.projection r.left =
                    pullback.fst X.obj.projection a.left ∧
                  AbelianLevelModuli.HomCondition
                    (⟨smoothCurveModuliPullback X T a, α⟩ :
                      AbelianLevelModuli (Spec (.of k)) g ℓ)
                    (⟨smoothCurveModuliPullback X P r, frameP⟩ :
                      AbelianLevelModuli (Spec (.of k)) g ℓ) q) ∧
            ∃ t : BasedFunctor (discreteModuli (yoneda.obj X.obj.base))
                (BasedCategory.ofFunctor (smoothCurveModuliBase (Spec (.of k)) g)),
              ∃ η : t.toFunctor ⟶ (Functor.const _).obj X,
                (∀ (z : (discreteModuli (yoneda.obj X.obj.base)).obj),
                  (smoothCurveModuliBase (Spec (.of k)) g).IsHomLift
                  (yoneda.preimage z.hom) (η.app z)) ∧
                ∃ e : BasedFunctor (discreteModuli (yoneda.obj P))
                    (moduliTwoFiberProduct t (abelianLevelForgetSmooth (Spec (.of k)) g ℓ)),
                  e.toFunctor.IsEquivalence ∧
                  Nonempty (ModuliTwoIso
                    (e.comp (moduliTwoFiberFst t
                      (abelianLevelForgetSmooth (Spec (.of k)) g ℓ)))
                    (discreteModuliMap (yoneda.map r))) := by
  sorry

end AlgebraicGeometry
