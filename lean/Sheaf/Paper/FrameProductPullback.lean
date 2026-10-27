/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.Paper.FrameProductOnSupport
public import Sheaf.Paper.SupportedCupFunctoriality

/-! # Restriction of concrete supported boundary products -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting

/-- Concrete boundary products commute with pullback, after the specified support
identifications. This assertion concerns arbitrary tuples and arbitrary schemes;
no smoothness or independence of generators is used.
Source: the pullback compatibility in the local restriction paragraph of frame
independence (blueprint: lem-pur-frame-product-pullback).
Proof: induct on the length of the ordered fold. The empty fold is the restricted
unit, so the unit-normalized closed exchange gives the assertion. For the next
factor, Kummer naturality identifies the pulled-back unit on the principal open.
Naturality of localization identifies its boundary, with the same boundary sign.
The supported-cup pullback law then identifies the appended product. The positive
Tate-product normalization identifies its final coefficient map with frameTensorNext.
The uniquely unit-normalized closed exchanges identify the intersection support
with the zero scheme of the pulled-back tuple. Naturality with respect to the given
support isomorphisms gives the displayed transport on both sides. -/
theorem frameProductOnSupport_pullback (P : PurityFiniteSetting.{u})
    {Z X D Y : Scheme.{u}} (i : Z ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (q : Y ⟶ X) (t : D ⟶ Z)
    (sq : ChosenCartesianSquare t j i q) (a : X ⟶ Spec (.of P.field.k))
    (c : ℕ) (f : Fin c → Γ(X, ⊤))
    (e : X.zeroLocusSubscheme (Set.range f) ≅ Z)
    (he : e.hom ≫ i = X.zeroLocusSubschemeι (Set.range f))
    (d : Y.zeroLocusSubscheme (Set.range (fun k ↦ q.appTop (f k))) ≅ D)
    (hd : d.hom ≫ j = Y.zeroLocusSubschemeι (Set.range (fun k ↦ q.appTop (f k)))) :
    P.functorialCupPullback true i j q t sq a (2 * (c : ℤ)) c
      (P.frameProductOnSupport i a c f e he) =
    P.frameProductOnSupport j (q ≫ a) c (fun k ↦ q.appTop (f k)) d hd := by
  sorry

end WeilConjectures.PurityFiniteSetting
