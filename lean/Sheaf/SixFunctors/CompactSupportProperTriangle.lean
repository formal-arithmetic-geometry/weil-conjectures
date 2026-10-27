/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.SixFunctors.DetSfCompBaseChangeDefs

/-!
# Proper exchange along a commuting triangle

Source: blueprint det-sf-comp-composition-base-change, proof (3), proper mate pasting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Direct-image composition followed by the specified equality of scheme maps.
Source: blueprint det-sf-comp-composition-base-change, proof (3).
(blueprint: lem-sfb-compact-support-proper-triangle). -/
def compactSupportPushforwardTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ C) (q : A ⟶ C)
    (e : a ≫ p = q) :
    R((a)_*⟦Λ⟧) ⋙ R((p)_*⟦Λ⟧) ≅ R((q)_*⟦Λ⟧) :=
  (refinementDerivedLowerStarComp Λ a p).symm ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ e)

/-- Pull back a morphism of triangles to the two literal fibre products.
Source: blueprint det-sf-comp-composition-base-change, proof (3).
(blueprint: lem-sfb-compact-support-proper-triangle). -/
def compactSupportTrianglePullback
    {A B Y Y' : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ Y) (q : A ⟶ Y)
    (e : a ≫ p = q) (v : Y' ⟶ Y) : pullback q v ⟶ pullback p v :=
  pullback.map q v p v a (𝟙 Y') (𝟙 Y) (by simpa using e.symm) (by simp)

/-- The Cartesian square of a pulled-back morphism of triangles.
Source: base change of a refinement, as in Compactification.Refinement.ofIsPullback.
(blueprint: lem-sfb-compact-support-proper-triangle). -/
def compactSupportTrianglePullbackSquare
    {A B Y Y' : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ Y) (q : A ⟶ Y)
    (e : a ≫ p = q) (v : Y' ⟶ Y) :
    ChosenCartesianSquare (pullback.fst q v) (compactSupportTrianglePullback a p q e v)
      a (pullback.fst p v) := by
  have hfst : compactSupportTrianglePullback a p q e v ≫ pullback.fst p v =
      pullback.fst q v ≫ a := by simp [compactSupportTrianglePullback]
  have hp : IsPullback (compactSupportTrianglePullback a p q e v) (pullback.fst q v)
      (pullback.fst p v) a := by
    refine IsPullback.of_right ?_ hfst (IsPullback.of_hasPullback p v).flip
    have hsnd : compactSupportTrianglePullback a p q e v ≫ pullback.snd p v =
        pullback.snd q v := by simp [compactSupportTrianglePullback]
    rw [hsnd, e]
    exact (IsPullback.of_hasPullback q v).flip
  exact
    { toCommSq := hp.flip.toCommSq
      isoPullback := hp.flip.isoPullback
      hom_fst := hp.flip.isoPullback_hom_fst
      hom_snd := hp.flip.isoPullback_hom_snd }

/-- Pasting proper exchange with an arbitrary arrow and a further direct image.

Source: blueprint det-sf-comp-composition-base-change, proof (3), applying the final
proper pushforward; Mathlib's mateEquiv_hcomp and naturality of the right compositor.
(blueprint: lem-sfb-compact-support-proper-triangle).

Proof: first substitute the specified normalization hb of b. Normalize the direct-image
compositor by the K-injective derived units, so it
is the conjugate of the exact pullback compositor. The square for a followed by p
is the horizontal paste of their pullback squares; the pullback compositors identify
its comparison with that paste. Apply mateEquiv_hcomp and conjugate-mate pasting.
This gives the exchange for q as the exchange for p followed by the image of the
exchange for a, with the two displayed triangle compositors. Naturality moves t
across the pulled-back triangle compositor. Associativity of the direct-image
compositor identifies the resulting two maps into the direct image along z: on a
K-injective resolution both are the underived triple compositor, whose associativity
is the ordinary sectionwise associativity. The equality s followed by a' equals r
and the two equations to z identify the structural equality transports. This yields
the formula below. The argument uses no open immersion, compactification, density,
properness, coefficient admissibility or invertibility of an exchange or of t.
It therefore also applies to zero objects and empty schemes. -/
theorem compactSupportProperTriangle_pasting
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B Y Y' W : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ Y) (q : A ⟶ Y)
    (e : a ≫ p = q) (v : Y' ⟶ Y)
    (s : W ⟶ pullback q v) (r : W ⟶ pullback p v) (z : W ⟶ Y')
    (es : s ≫ pullback.snd q v = z) (er : r ≫ pullback.snd p v = z)
    (esr : s ≫ compactSupportTrianglePullback a p q e v = r)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)))
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)))
    (t : (detSfDerivedPullback Λ (pullback.fst q v)).obj M ⟶ R((s)_*⟦Λ⟧).obj N)
    (b : R((p)_*⟦Λ⟧) ⋙ detSfDerivedPullback Λ v ⟶
      detSfDerivedPullback Λ (pullback.fst p v) ⋙ R((pullback.snd p v)_*⟦Λ⟧))
    (hb : b = detSfProperBaseChangeMap Λ p v) :
    (detSfDerivedPullback Λ v).map
        ((compactSupportPushforwardTriangle Λ a p q e).hom.app M) ≫
      (detSfProperBaseChangeMap Λ q v).app M ≫
      R((pullback.snd q v)_*⟦Λ⟧).map t ≫
      (compactSupportPushforwardTriangle Λ s (pullback.snd q v) z es).hom.app N =
    b.app (R((a)_*⟦Λ⟧).obj M) ≫
      R((pullback.snd p v)_*⟦Λ⟧).map
        ((condensedAmbientExchange Λ (compactSupportTrianglePullbackSquare a p q e v)).app M ≫
          R((compactSupportTrianglePullback a p q e v)_*⟦Λ⟧).map t ≫
          (compactSupportPushforwardTriangle Λ s
            (compactSupportTrianglePullback a p q e v) r esr).hom.app N) ≫
      (compactSupportPushforwardTriangle Λ r (pullback.snd p v) z er).hom.app N := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
