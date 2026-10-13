/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Algebraization of the comparison over a complete affine base

Source: Stacks Project, Tag 088B, final complete-base paragraph; Tags 087W and 0883.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Over a complete Noetherian affine base the formal comparison is the completion
of an algebraic adjunction map, followed by the pushforward of an isomorphism.

Source: Stacks Project, Tag 088B, paragraph beginning with the complete affine base,
and Tags 087W and 0883.
(blueprint: lem-weil-pbc-formal-comparison-complete-base-algebraization)

Proof: The affine formal-module equivalence identifies G with the completion of the
coherent sheaf associated to its finite module of inverse-limit sections. Completeness
identifies that module over the completion with a module over A itself. Denote its
coherent sheaf by A0. Pullback commutes with quotient systems, so beta identifies the
completion of p* A0 with that of F. Full faithfulness on the proper scheme lifts beta
and its inverse to maps which are mutually inverse: their composites complete to the
identity, and injectivity of completion forces the composites to be identities.
Naturality of the supplied adjunction unit with respect to quotient projections
identifies its completed map with the degreewise units appearing in hAlpha.
Coherence of p* A0 follows from tensor pullback over a Noetherian scheme. The affine
limit cones for A0 and p_* F give the displayed section isomorphisms. Formal functions
identifies the inverse limit of kappa with an isomorphism. Its composites with alpha
and with the completed adjunction map agree at every level by hAlpha and naturality
of quotient projections. Cancel that inverse-limit isomorphism to obtain the square.
No isomorphism of p over any open is needed. For a zero ring the schemes and modules
are empty/zero, and the same equivalence and cancellation argument apply. -/
theorem formalComparison_complete_base_algebraization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    {Z : Scheme.{u}} (p : Z ⟶ Spec (CommRingCat.of A)) [IsProper p]
    (adj : Scheme.Modules.tensorPullback p ⊣ Scheme.Modules.pushforward p)
    (G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (F : CoherentModules Z)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback p ≅
      formalCompletionSystem (J.comap p) F.obj)
    (h : RingedSpace.IsCoherent (Spec (CommRingCat.of A)).toRingedSpace
      ((Scheme.Modules.pushforward p).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward p).obj F.obj) ⟶
      formalCompletionSystem (J.comap p) F.obj ⋙ Scheme.Modules.pushforward p)
    (α : G ⟶ (completion _ J).obj ⟨(Scheme.Modules.pushforward p).obj F.obj, h⟩)
    (hKappa : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward p).obj F.obj) ≫
        κ.app (op n) = (Scheme.Modules.pushforward p).map
          (formalModuleQuotientπ (J.comap p) (n + 1) F.obj))
    (hAlpha : ∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
      adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward p).map (β.hom.app (op n))) :
    ∃ (A₀ : CoherentModules (Spec (CommRingCat.of A)))
      (b : (Scheme.Modules.tensorPullback p).obj A₀.obj ≅ F.obj),
    ∃ eA : limit (G.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A)) ≅
        (moduleSpecΓFunctor (R := CommRingCat.of A)).obj A₀.obj,
    ∃ eD : limit (((completion _ J).obj
        ⟨(Scheme.Modules.pushforward p).obj F.obj, h⟩).obj ⋙
          moduleSpecΓFunctor (R := CommRingCat.of A)) ≅
        (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
          ((Scheme.Modules.pushforward p).obj F.obj),
      lim.map (Functor.whiskerRight α.hom
        (moduleSpecΓFunctor (R := CommRingCat.of A))) ≫ eD.hom =
      eA.hom ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        (adj.unit.app A₀.obj ≫ (Scheme.Modules.pushforward p).map b.hom) := by
  sorry

end AlgebraicGeometry
