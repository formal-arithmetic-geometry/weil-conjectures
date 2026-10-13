/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Sheaf.AlgebraicGeometry.FormalSystemsPullback
import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections
import Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionIso

/-! # Ordinary flat quotient comparisons and adjunction mates

Source: Stacks Project, Tags 088B, 0887, 02KH and 02N7.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Flat base change transports an algebraization isomorphism and its adjunction mate,
and its termwise comparison respects the quotient projections before completion of
pushforward. No completed pushforward or comparison map kappa is involved.
Source: Stacks Project, Tags 088B (completed-base-change paragraph), 0887 and 02KH;
Tag 02N7 for the adjunction mate of the base-change map.
(blueprint: lem-weil-pbc-formal-flat-quotient-mate-data)

Proof: Write q and p for the projections. Choose the tensor-pullback adjunction on p.
The composition comparisons identify g* followed by p* with f* followed by q*;
compare the supplied adjunction on f with the chosen tensor adjunction and absorb
its invertible left-adjoint comparison in this composition isomorphism. Pull beta
through this comparison and the completion-pullback isomorphism for F to obtain
beta zero. The degree-zero flat base-change mate b_M:g*f_*M -> p_*q*M is natural
in M and invertible on quasi-coherent M by 02KH. For F, use its inverse and the
supplied equality F zero = q*F to define b:D -> g*H. Termwise b on the quotients
of F, followed by the inverse completion-pullback comparison, defines t. Naturality
of b at each quotient projection, and the projection normalization of completion
pullback, prove the first displayed equation. The mate identity for b, naturality
at beta, and the adjusted composition comparison prove the second equation.
Naturality of the comparisons makes beta zero and t maps of whole inverse systems.
All constructions use cokernels and adjunctions and also apply to empty schemes,
zero modules, zero ideals and unit ideals; no faithful completion is used. -/
theorem formal_flat_quotient_mate_data
    {X Y S : Scheme.{u}} [IsNoetherian Y] [IsNoetherian S]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f] (g : S ⟶ Y) [Flat g]
    (I : S.IdealSheafData) (hI : J.comap g = I)
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (G₀ : CoherentFormalModule S I) (F₀ : CoherentModules (pullback f g))
    (hG : G₀.obj = G.obj ⋙ Scheme.Modules.tensorPullback g)
    (hF : F₀.obj = (Scheme.Modules.tensorPullback (pullback.fst f g)).obj F.obj) :
    let p := pullback.snd f g
    ∃ (adjR : Scheme.Modules.tensorPullback p ⊣ Scheme.Modules.pushforward p)
      (β₀ : G₀.obj ⋙ Scheme.Modules.tensorPullback p ≅
        formalCompletionSystem (I.comap p) F₀.obj)
      (b : (Scheme.Modules.pushforward p).obj F₀.obj ≅
        (Scheme.Modules.tensorPullback g).obj ((Scheme.Modules.pushforward f).obj F.obj))
      (t : (formalCompletionSystem (J.comap f) F.obj ⋙
          Scheme.Modules.pushforward f) ⋙ Scheme.Modules.tensorPullback g ⟶
        formalCompletionSystem (I.comap p) F₀.obj ⋙ Scheme.Modules.pushforward p),
      (∀ n : ℕ, b.hom ≫ (Scheme.Modules.tensorPullback g).map
          ((Scheme.Modules.pushforward f).map
            (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) ≫ t.app (op n) =
        (Scheme.Modules.pushforward p).map
          (formalModuleQuotientπ (I.comap p) (n + 1) F₀.obj)) ∧
      (∀ n : ℕ, (eqToHom hG).app (op n) ≫
          (Scheme.Modules.tensorPullback g).map
            (adj.unit.app (G.obj.obj (op n)) ≫
              (Scheme.Modules.pushforward f).map (β.hom.app (op n))) ≫ t.app (op n) =
        adjR.unit.app (G₀.obj.obj (op n)) ≫
          (Scheme.Modules.pushforward p).map (β₀.hom.app (op n))) := by sorry

end AlgebraicGeometry
