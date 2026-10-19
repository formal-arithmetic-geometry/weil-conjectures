/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.PurityFrameClass
import Sheaf.Paper.RelativeSupportBottomDescent
import Sheaf.Paper.SupportedCupFunctoriality

/-! # Zariski-local equality criterion for concrete frame classes

Source: main-20261015, lem-pur-frame-independence, steps 2 and 7.
(blueprint: lem-pur-frame-class-local-equality).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] frameBoundaryProduct frameClass

/-- The ordered products of two tuples agree on a neighbourhood of every point.
Source: frame-independence, the local equality test
(blueprint: lem-pur-frame-class-local-equality). -/
def FrameBoundaryProductsLocallyHEq (P : PurityFiniteSetting.{u}) (U : Scheme.{u})
    (a : U ⟶ Spec (.of P.field.k)) (c : ℕ) (f g : Fin c → Γ(U, ⊤)) : Prop :=
  ∀ x : U, ∃ W : U.Opens, x ∈ W ∧
    HEq (P.frameBoundaryProduct W.toScheme (W.ι ≫ a) c (fun k ↦ W.ι.appTop (f k)))
      (P.frameBoundaryProduct W.toScheme (W.ι ≫ a) c (fun k ↦ W.ι.appTop (g k)))

/-- Equality of the concrete boundary products on neighbourhoods of every
point implies equality after canonical transport to the fixed pullback support.
This criterion supplies only locality, with local equality as a hypothesis.

Source: main-20261015, lem-pur-frame-independence.proof.md, first paragraph and
last sentence, using the bottom-degree descent correction in steps 2 and 7
(blueprint: lem-pur-frame-class-local-equality).

Proof: Choose one neighbourhood and its equality at each point; their inclusions
form a Zariski cover, hence an etale cover. Both original tuples and their
restrictions present the same scheme-theoretic inverse-image ideal, so their
zero subschemes on each neighbourhood are canonically identified with the
pullback of Z. The source coefficient isomorphisms are the direct-image
composition and constant-pullback isomorphisms; their normalization on local
constants makes their restriction squares commute. Kummer pullback and boundary
naturality followed by cup pullback identify restriction of each global frame
class with the displayed local ordered boundary product. Thus the hypothesis
identifies their restrictions in the same supported Hom group. The supported-Hom
identification, forgetting scalars, and etale/pro-etale support comparison carry
these to equal local support-cohomology classes. Apply
relative_support_bottom_descent with d=P.level, r=c and degree 2c to this cover.
Its separation clause makes the global classes equal. The comparison maps are
bijections, so the original global Hom representatives are equal. At c=0 this
is ordinary degree-zero sheaf separation; on the empty scheme the empty cover
is allowed. No independence of generators is used in this locality argument. -/
theorem frameClass_eq_of_locally_heq (P : PurityFiniteSetting.{u}) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension P.level v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (U : Scheme.{u}) (e : U ⟶ V) [Etale e] (f g : Fin c → Γ(U, ⊤))
    (tf : U.zeroLocusSubscheme (Set.range f) ⟶ Z)
    (tg : U.zeroLocusSubscheme (Set.range g) ⟶ Z)
    (hf : IsPullback tf (U.zeroLocusSubschemeι (Set.range f)) i e)
    (hg : IsPullback tg (U.zeroLocusSubschemeι (Set.range g)) i e) :
    P.FrameBoundaryProductsLocallyHEq U (e ≫ v ≫ b) c f g →
    (cupSingle P U).map
        (P.frameClosedCoefficientIso (U.zeroLocusSubschemeι (Set.range f))
          (pullback.snd i e) hf.isoPullback hf.isoPullback_hom_snd).inv ≫
      P.frameClass b v i c hcodim
        { U := U, e := e, etale := inferInstance, f := f, toZ := tf, isPullback := hf } =
    (cupSingle P U).map
        (P.frameClosedCoefficientIso (U.zeroLocusSubschemeι (Set.range g))
          (pullback.snd i e) hg.isoPullback hg.isoPullback_hom_snd).inv ≫
      P.frameClass b v i c hcodim
        { U := U, e := e, etale := inferInstance, f := g, toZ := tg, isPullback := hg } := by
  sorry

end WeilConjectures.PurityFiniteSetting
