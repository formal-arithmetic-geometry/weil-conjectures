/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Frobenius squares for an open subscheme over a finite field

Source: Weil conjectures blueprint, `sec-trace-formula/sk-d-weil-push`,
`lem-trf-frobenius-open-square.md`, order 2368; Stacks, Tags 03SM, 01JR and 01JP
(blueprint: lem-trf-frobenius-open-square).

The models are arbitrary schemes over the finite base. The scheme Frobenius is written
using `Over.pullback.map` applied to the existing absolute Frobenius; this is the defining
expression of `relativeFrobenius` without its unnecessary finite-type interface.
The Galois maps are the existing unrestricted `galoisMap`. Powers are taken in `End`
of the category of schemes, so the Galois maps are not assumed to be morphisms over `k`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- The scheme-Frobenius and geometric-Galois-Frobenius squares of an open immersion
are Cartesian for every nonnegative iterate. The last two identities give semilinearity
of the Galois maps with respect to the projections to `Spec k`.
Source: blueprint `sec-trace-formula/sk-d-weil-push/lem-trf-frobenius-open-square.md`,
order 2368; Stacks, Tags 03SM, 01JR and 01JP
(blueprint: lem-trf-frobenius-open-square).

Proof:
1. The structure morphisms make `p` vanish on the models, including empty opens.
   Absolute Frobenius is identity on points and raises sections to `p`-th powers.
   Its `a`-fold iterate therefore raises sections to `q`-th powers. It restricts
   to the same Frobenius on the open subscheme and fixes the finite base field.
2. Its inverse image of the open image of `j₀` is that same open. The inverse-image
   open fibre-product lemma `lem-weil-pbc-open-preimage-fibre-product` identifies
   the model square with a pullback, with exactly these restriction maps.
3. Base change preserves the open immersion by `lem-weil-pbc-open-fibre-product`.
   Compare the two projections to see that the base-changed square commutes.
   Given a compatible pair of maps into it, the model square supplies a unique
   model lift and their common scalar projection supplies the scalar lift.
   The fibre-product universal property then supplies the unique total lift.
4. Geometric field Frobenius fixes the base and has an inverse. Functoriality of
   `Spec` and the fibre product gives inverse coefficient actions on each model's
   scalar extension. Comparing projections shows they commute with `j`. For a
   compatible pair `(u,v)`, the unique lift is the inverse Galois iterate after `u`.
5. The second projection of `id × Spec γ` is the second projection followed by
   `Spec γ`. Iterating proves the two displayed semilinearity identities.
All these arguments include the zeroth iterate, where every endomorphism is identity. -/
theorem frobenius_open_square (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))) (j₀ : X₀ ⟶ Y₀)
    [IsOpenImmersion j₀.left] (m : ℕ) :
    IsPullback
      (End.of (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        (Over.homMk
          (X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a)
          (D.model_frobenius_over X₀.hom))).left) ^ m)
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        j₀).left)
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        j₀).left)
      (End.of (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        (Over.homMk
          (Y₀.left.iterateFrobenius D.prime (D.model_characteristic Y₀.hom) D.a)
          (D.model_frobenius_over Y₀.hom))).left) ^ m) ∧
    IsPullback
      (End.of (D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
        (Fintype.ofFinite D.k₀) _ _ _)) ^ m)
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        j₀).left)
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        j₀).left)
      (End.of (D.galoisMap Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
        (Fintype.ofFinite D.k₀) _ _ _)) ^ m) ∧
    (End.of (D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
        (Fintype.ofFinite D.k₀) _ _ _)) ^ m) ≫
        pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        (End.of (Spec.map (CommRingCat.ofHom
          (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
            (Fintype.ofFinite D.k₀) _ _ _).toRingHom)) ^ m) ∧
    (End.of (D.galoisMap Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
        (Fintype.ofFinite D.k₀) _ _ _)) ^ m) ≫
        pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        (End.of (Spec.map (CommRingCat.ofHom
          (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
            (Fintype.ofFinite D.k₀) _ _ _).toRingHom)) ^ m) :=
  sorry

end WeilConjectures.FiniteFieldDatum
