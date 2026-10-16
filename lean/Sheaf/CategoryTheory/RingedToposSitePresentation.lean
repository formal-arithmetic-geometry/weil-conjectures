/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Continuous
import Sheaf.CategoryTheory.ToposSitePresentation
import Sheaf.CategoryTheory.RingedToposSquareTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Whiskering

/-!
# Presenting a morphism of ringed topoi by a morphism of sites

Source: Stacks Project, Modules on Sites, Tag 03CR, using Sites Tags 03A1, 03CI and 03A2
(blueprint: lem-weil-pbc-ringed-topos-site-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Every morphism of ringed topoi admits a finite-limit site presentation.

Source: Stacks Project, Tag 03CR, clauses (1)-(6)
(blueprint: lem-weil-pbc-ringed-topos-site-presentation).

The commutative ring sheaves are forgotten to ring sheaves only to use the existing
`RingedToposMorphism` interface. Its module direct image is the induced one, not extra
geometric data. The identifications `a` and `b`, together with their counit equations,
express exactly `A' = g_* A` and `B' = e_* B` as transported ring sheaves. Indeed their
adjuncts are ring maps; the equivalence counits are isomorphisms, so this characterizes
the transported ring structures and their canonical structural isomorphisms. No arbitrary
identification of the structural maps is allowed. The last equation says that the inverse
image comparison `alpha` identifies the structural ring maps of the composite morphisms.
Its adjoint mate gives the corresponding direct image comparison.

Proof:
1. `topos_sitePresentation` applies the finite-limit generator closure and comparison
   constructions to `f.inverse`. It supplies the two small finite-limit sites, strong
   precoverages, equivalences, a continuous finite-limit-preserving functor `v`, and
   the direct-image comparison with the original adjunction.
2. Set `H = (E.inverse ⋙ f.inverse) ⋙ G.functor` and let `R` be the continuous site
   pushforward. Conjugating the original adjunction by the equivalence counits gives
   `H ⊣ R`; the displayed `alpha` is its inverse-image comparison.
3. Apply `ringedTopos_squareTransport` to this fixed geometric square. That theorem
   transports the commutative ring sheaves and supplies all three ringed-topos
   morphisms, their induced module direct images, the canonical counit equations,
   and the final structural-map equality.
4. Rewrite the direct functors of the two equivalences using the equalities supplied
   by the transport theorem; their equivalence instances then follow by synthesis.
-/
theorem ringedTopos_sitePresentation
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (A : Sheaf J.toGrothendieck CommRingCat.{u})
    (B : Sheaf K.toGrothendieck CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K.toGrothendieck (forget₂ CommRingCat RingCat)).obj B)) :
    ∃ (C' D' : Type u) (_ : SmallCategory C') (_ : SmallCategory D')
      (J' : Precoverage C') (K' : Precoverage D')
      (_ : J'.HasIsos) (_ : J'.IsStableUnderComposition)
      (_ : J'.IsStableUnderBaseChange) (_ : J'.HasPullbacks)
      (_ : K'.HasIsos) (_ : K'.IsStableUnderComposition)
      (_ : K'.IsStableUnderBaseChange) (_ : K'.HasPullbacks)
      (_ : HasFiniteLimits C') (_ : HasFiniteLimits D')
      (A' : Sheaf J'.toGrothendieck CommRingCat.{u})
      (B' : Sheaf K'.toGrothendieck CommRingCat.{u})
      (g : RingedToposMorphism
        ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj A)
        ((sheafCompose J'.toGrothendieck (forget₂ CommRingCat RingCat)).obj A'))
      (e : RingedToposMorphism
        ((sheafCompose K.toGrothendieck (forget₂ CommRingCat RingCat)).obj B)
        ((sheafCompose K'.toGrothendieck (forget₂ CommRingCat RingCat)).obj B'))
      (h : RingedToposMorphism
        ((sheafCompose J'.toGrothendieck (forget₂ CommRingCat RingCat)).obj A')
        ((sheafCompose K'.toGrothendieck (forget₂ CommRingCat RingCat)).obj B'))
      (v : D' ⥤ C') (_ : PreservesFiniteLimits v)
      (_ : v.IsContinuous K'.toGrothendieck J'.toGrothendieck)
      (a : (sheafCompose J'.toGrothendieck (forget CommRingCat)).obj A' ≅
        g.direct.obj ((sheafCompose J.toGrothendieck (forget CommRingCat)).obj A))
      (b : (sheafCompose K'.toGrothendieck (forget CommRingCat)).obj B' ≅
        e.direct.obj ((sheafCompose K.toGrothendieck (forget CommRingCat)).obj B))
      (alpha : e.inverse ⋙ f.inverse ≅ h.inverse ⋙ g.inverse),
      g.direct.IsEquivalence ∧ e.direct.IsEquivalence ∧
      (∀ (T : D') (R : Presieve T), R ∈ K' T → R.map v ∈ J' (v.obj T)) ∧
      h.direct = v.sheafPushforwardContinuous (Type u)
        K'.toGrothendieck J'.toGrothendieck ∧
      g.ringMap = g.inverse.map a.hom ≫
        g.adj.counit.app ((sheafCompose J.toGrothendieck (forget CommRingCat)).obj A) ∧
      e.ringMap = e.inverse.map b.hom ≫
        e.adj.counit.app ((sheafCompose K.toGrothendieck (forget CommRingCat)).obj B) ∧
      f.inverse.map e.ringMap ≫ f.ringMap =
        alpha.hom.app ((sheafCompose K'.toGrothendieck (forget CommRingCat)).obj B') ≫
          g.inverse.map h.ringMap ≫ g.ringMap := by
  have : PreservesFiniteLimits f.inverse := f.leftExact
  obtain ⟨C', D', hC', hD', J', K', hJiso, hJcomp, hJbase, hJpb,
      hKiso, hKcomp, hKbase, hKpb, hlimC', hlimD', G, E, v, hvlim, hvcont,
      hcover, ⟨θ⟩⟩ := topos_sitePresentation J K f.inverse f.direct f.adj
  let H := (E.inverse ⋙ f.inverse) ⋙ G.functor
  let R := v.sheafPushforwardContinuous (Type u) K'.toGrothendieck J'.toGrothendieck
  let ξ : G.inverse ⋙ (f.direct ⋙ E.functor) ≅ R :=
    Functor.isoWhiskerLeft G.inverse θ ≪≫
      (Functor.associator G.inverse G.functor R).symm ≪≫
        Functor.isoWhiskerRight G.counitIso R ≪≫ Functor.leftUnitor R
  let adjH : H ⊣ R :=
    ((E.symm.toAdjunction.comp f.adj).comp G.toAdjunction).ofNatIsoRight ξ
  have : PreservesFiniteLimits (E.inverse ⋙ f.inverse) := comp_preservesFiniteLimits _ _
  have hH : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  let α : E.inverse ⋙ f.inverse ≅ H ⋙ G.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ G.unitIso ≪≫
      (Functor.associator _ _ _).symm
  obtain ⟨A', B', g, e, h, a, b, alpha, hg, he, hh, hga, heb, halpha⟩ :=
    ringedTopos_squareTransport A B f G E H R adjH hH α
  refine ⟨C', D', hC', hD', J', K', hJiso, hJcomp, hJbase, hJpb,
    hKiso, hKcomp, hKbase, hKpb, hlimC', hlimD', A', B', g, e, h, v, hvlim,
    hvcont, a, b, alpha, ?_, ?_, hcover, hh, hga, heb, halpha⟩
  · rw [hg]
    infer_instance
  · rw [he]
    infer_instance

end CategoryTheory
