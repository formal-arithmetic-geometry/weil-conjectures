/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Basic

import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import all Sheaf.AlgebraicGeometry.FormalSystemsPullback
import Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Algebraizing a formal pullback isomorphism with quotient compatibility

Source: Stacks Project, Tag 088B, final complete-base paragraph; Tags 087W and 0883.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A formal pullback isomorphism over a complete affine base lifts to an algebraic
isomorphism, compatibly with the actual quotient projections.
Source: Stacks Project, Tag 088B, final complete-base paragraph; Tags 087W and 0883.
(blueprint: lem-weil-pbc-formal-comparison-algebraization-quotient-lift)

Proof: Tag 087W associates to G its finite module over the completion of A.
Since A is I-adically complete, restrict this module along the isomorphism
A -> its completion and take its tilde, a coherent module A0. The unit and inverse
comparison of the affine equivalence give e from G to the quotient system of A0. Pullback preserves
coherence on the Noetherian proper scheme and commutes with the quotient system;
the comparison is specified by the images of the quotient projections. Compose
it with the pullback of e.inv and beta. Tag 0883 lifts this isomorphism
and its inverse uniquely to maps between p* A0 and F. Injectivity on Hom makes
the lifted composites identities. The resulting isomorphism b has exactly the
displayed projection equation, since the quotient comparison sends the projection
to the pullback of the projection. The zero ring causes no exception: all these
categories and maps are zero. -/
theorem formalComparison_algebraization_quotient_lift
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    {Z : Scheme.{u}} (p : Z ⟶ Spec (CommRingCat.of A)) [IsProper p]
    (G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (F : CoherentModules Z)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback p ≅
      formalCompletionSystem (J.comap p) F.obj) :
    ∃ (A₀ : CoherentModules (Spec (CommRingCat.of A)))
      (e : G.obj ≅ formalCompletionSystem J A₀.obj)
      (b : (Scheme.Modules.tensorPullback p).obj A₀.obj ≅ F.obj),
      ∀ n : ℕ,
        (Scheme.Modules.tensorPullback p).map (formalModuleQuotientπ J (n + 1) A₀.obj) ≫
          (Scheme.Modules.tensorPullback p).map (e.inv.app (op n)) ≫ β.hom.app (op n) =
        b.hom ≫ formalModuleQuotientπ (J.comap p) (n + 1) F.obj := by
  sorry

end
end AlgebraicGeometry
