/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q32
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Pullback of a pointed etale diagram

Source: Stacks Project, Curves, Tag 0CBY, `lemma-etale-local-structure-nodal-family`,
first proof, first paragraph; Morphisms, Tag 01S1
(blueprint: lem-trf-pointed-etale-diagram-pullback).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option autoImplicit false in
/-- A pointed etale chart diagram pulls back through arbitrary base change and open
restrictions. The open subschemes are presented by the open immersions `iX` and `iS`;
`f'` is the restriction of `f`. The projection equations characterize the two canonical
isomorphisms, the induced map `w`, the model map `m`, and its comparison map `r`.

Source: Stacks Project, Curves, Tag 0CBY, `lemma-etale-local-structure-nodal-family`,
first proof, first paragraph, and Morphisms, Tags 02GN, 02GO, 02GP, 01S1
(blueprint: lem-trf-pointed-etale-diagram-pullback).

Proof plan:
1. Use the fibre-product universal property (def-pc-fibre-product) to identify
   U with U0 ×[S0] S' and then with U0 ×[V0] (V0 ×[S0] S'). Each map is uniquely
   determined by its projections; the inverse maps preserve those projections.
2. The two chart projections are base changes of p0 and e0, hence etale by
   lem-weil-pbc-etale-scheme-base-change. Compose with the open immersions using
   lem-weil-pbc-etale-composition-cancellation.
3. Define w by its V0 and S' projections. Define m by the Y projection of m0 and w,
   and r by the Y and V0 projections. The fibre-product universal property shows
   their square with m0 is cartesian (def-pc-fibre-product).
4. Base change of m0 makes m etale (lem-weil-pbc-etale-scheme-base-change).
   The restriction equation and the projection identities give w ≫ e = p ≫ f.
5. Apply lem-weil-pbc-base-change-image to the singleton {u0}: the equality of
   images of u0 and x gives a point of U above both. This also gives p(u) = iX(x).
6. Pullback of global functions is contravariantly functorial (def-pc-scheme),
   giving the asserted identity for every global section of T. -/
theorem exists_pointed_etale_diagram_pullback
    {X0 S0 Y T U0 V0 X S X' S' : Scheme.{u}}
    (f0 : X0 ⟶ S0) (y : Y ⟶ T) (p0 : U0 ⟶ X0) (e0 : V0 ⟶ S0)
    [Etale p0] [Etale e0] (w0 : U0 ⟶ V0) (τ0 : V0 ⟶ T)
    (m0 : U0 ⟶ pullback y τ0) [Etale m0]
    (hw0 : w0 ≫ e0 = p0 ≫ f0) (hm0 : m0 ≫ pullback.snd y τ0 = w0)
    (u0 : U0) (f : X ⟶ S) (iX : X' ⟶ X) (iS : S' ⟶ S)
    [IsOpenImmersion iX] [IsOpenImmersion iS]
    (f' : X' ⟶ S') (hf' : f' ≫ iS = iX ≫ f) (c : S' ⟶ S0)
    (α : X' ≅ pullback f0 c) (hα : α.hom ≫ pullback.snd f0 c = f')
    (x : X') (hx : (α.hom ≫ pullback.fst f0 c) x = p0 u0) :
    Etale (pullback.snd e0 c ≫ iS) ∧
    Etale (pullback.snd p0 (α.hom ≫ pullback.fst f0 c) ≫ iX) ∧
    ∃ (β : pullback p0 (α.hom ≫ pullback.fst f0 c) ≅ pullback (p0 ≫ f0) c)
      (γ : pullback (p0 ≫ f0) c ≅ pullback w0 (pullback.fst e0 c))
      (w : pullback p0 (α.hom ≫ pullback.fst f0 c) ⟶ pullback e0 c)
      (m : pullback p0 (α.hom ≫ pullback.fst f0 c) ⟶
        pullback y (pullback.fst e0 c ≫ τ0))
      (r : pullback y (pullback.fst e0 c ≫ τ0) ⟶ pullback y τ0),
      β.hom ≫ pullback.fst (p0 ≫ f0) c =
        pullback.fst p0 (α.hom ≫ pullback.fst f0 c) ∧
      β.hom ≫ pullback.snd (p0 ≫ f0) c =
        pullback.snd p0 (α.hom ≫ pullback.fst f0 c) ≫ f' ∧
      γ.hom ≫ pullback.fst w0 (pullback.fst e0 c) = pullback.fst (p0 ≫ f0) c ∧
      γ.hom ≫ pullback.snd w0 (pullback.fst e0 c) ≫ pullback.snd e0 c =
        pullback.snd (p0 ≫ f0) c ∧
      w = β.hom ≫ γ.hom ≫ pullback.snd w0 (pullback.fst e0 c) ∧
      Etale m ∧
      w ≫ pullback.snd e0 c ≫ iS =
        pullback.snd p0 (α.hom ≫ pullback.fst f0 c) ≫ iX ≫ f ∧
      m ≫ pullback.snd y (pullback.fst e0 c ≫ τ0) = w ∧
      m ≫ pullback.fst y (pullback.fst e0 c ≫ τ0) =
        pullback.fst p0 (α.hom ≫ pullback.fst f0 c) ≫ m0 ≫ pullback.fst y τ0 ∧
      r ≫ pullback.fst y τ0 = pullback.fst y (pullback.fst e0 c ≫ τ0) ∧
      r ≫ pullback.snd y τ0 =
        pullback.snd y (pullback.fst e0 c ≫ τ0) ≫ pullback.fst e0 c ∧
      IsPullback (pullback.fst p0 (α.hom ≫ pullback.fst f0 c)) m m0 r ∧
      (∃ z : ↥(pullback p0 (α.hom ≫ pullback.fst f0 c)),
        pullback.fst p0 (α.hom ≫ pullback.fst f0 c) z = u0 ∧
        pullback.snd p0 (α.hom ≫ pullback.fst f0 c) z = x ∧
        (pullback.snd p0 (α.hom ≫ pullback.fst f0 c) ≫ iX) z = iX x) ∧
      (∀ a : T.presheaf.obj (Opposite.op ⊤),
        (pullback.fst e0 c).appTop (τ0.appTop a) =
          (pullback.fst e0 c ≫ τ0).appTop a) := by
  sorry

end AlgebraicGeometry
