/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientData
import WeilConjectures.AlgebraicGeometry.EtaleProperAmbientTransportComposition

/-! # Second-side pasting under a proper ambient change

Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D, proper-projection grid.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

/-- The second side word commutes with the proper change of graph product. -/
theorem etaleGraphProperAmbientSecondSide
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s t : EtaleGraphPresentation f) (pr : t.P ⟶ s.P) [IsProper pr]
    (q : t.U ⟶ s.U) (sq : IsPullback q t.e s.e pr)
    (hz : t.a ≫ q = s.a) (hp : pr ≫ s.p = t.p) :
    (locallyClosedGraphSide₂ s.a s.e s.p c.i c.g
      ((Category.assoc _ _ _).trans (s.fac.trans c.comm)) A).hom ≫
        (s.properAmbientSecondTransport c t pr q sq hz hp A).hom =
      (etaleProperAmbientTransport A s.a s.e s.p t.a t.e t.p pr q sq hz hp).hom ≫
        (locallyClosedGraphSide₂ t.a t.e t.p c.i c.g
      ((Category.assoc _ _ _).trans (t.fac.trans c.comm)) A).hom := by
  let hs := (Category.assoc s.a s.e s.p).trans (s.fac.trans c.comm)
  let ht := (Category.assoc t.a t.e t.p).trans (t.fac.trans c.comm)
  let R := s.properAmbientProduct c t pr hp
  let r := s.properAmbientSecond c t pr q sq hp
  have has : locallyClosedGraphS₂ s.a s.e s.p c.i c.g hs ≫
      pullback.snd (pullback.fst s.p c.g) s.e = s.a := by
    simp only [locallyClosedGraphS₂, pullback.lift_snd]
  have hat : locallyClosedGraphS₂ t.a t.e t.p c.i c.g ht ≫
      pullback.snd (pullback.fst t.p c.g) t.e = t.a := by
    simp only [locallyClosedGraphS₂, pullback.lift_snd]
  have hleft := etaleProperAmbientTransport_comp A s.a s.e s.p
    (locallyClosedGraphS₂ s.a s.e s.p c.i c.g hs) (pullback.fst _ _)
    (pullback.fst s.p c.g ≫ s.p)
    (locallyClosedGraphS₂ t.a t.e t.p c.i c.g ht) (pullback.fst _ _)
    (pullback.fst t.p c.g ≫ t.p)
    (pullback.fst s.p c.g) R (pullback.snd _ _) r
    (IsPullback.of_hasPullback (pullback.fst s.p c.g) s.e).flip
    (s.properAmbientSecond_isPullback c t pr q sq hp)
    has (s.properAmbientSecond_graph c t pr q sq hz hp) rfl
    (s.properAmbientProduct_base c t pr hp)
  have hright := etaleProperAmbientTransport_comp A s.a s.e s.p t.a t.e t.p
    (locallyClosedGraphS₂ t.a t.e t.p c.i c.g ht) (pullback.fst _ _)
    (pullback.fst t.p c.g ≫ t.p)
    pr (pullback.fst t.p c.g) q (pullback.snd _ _)
    sq (IsPullback.of_hasPullback (pullback.fst t.p c.g) t.e).flip
    hz hat hp rfl
  have heq :
      locallyClosedGraphSide₂ s.a s.e s.p c.i c.g hs A ≪≫
        s.properAmbientSecondTransport c t pr q sq hz hp A =
      etaleProperAmbientTransport A s.a s.e s.p t.a t.e t.p pr q sq hz hp ≪≫
        locallyClosedGraphSide₂ t.a t.e t.p c.i c.g ht A := by
    change etaleProperAmbientTransport A _ _ _ _ _ _ _ _ _ _ _ ≪≫
      etaleProperAmbientTransport A _ _ _ _ _ _ _ _ _ _ _ =
      etaleProperAmbientTransport A _ _ _ _ _ _ _ _ _ _ _ ≪≫
        etaleProperAmbientTransport A _ _ _ _ _ _ _ _ _ _ _
    rw [hleft, hright]
    congr 1
    · simp only [R, EtaleGraphPresentation.properAmbientProduct, pullback.lift_fst]
    · simp only [r, EtaleGraphPresentation.properAmbientSecond, pullback.lift_snd]
  exact congrArg Iso.hom heq

end AlgebraicGeometry.Etale
