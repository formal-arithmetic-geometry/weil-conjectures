/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-adjunction-family). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- A family indexed only by smooth separated finite-type morphisms over the
fixed field. Source: smooth purity (blueprint: def-pur-transport-adjunction-family). -/
abbrev AdjunctionFamily (D : WeilConjectures.FiniteFieldDatum.{u}) :=
  ∀ (c : Coefficient ell) (s : SmoothDatum D), ExplicitAdjunction ell D c s

/-- The natural isomorphism with every specified Brown adjoint restriction,
uniquely characterized by its counit equation. The same explicit adjunction from
the family occurs in that equation.
Source: uniqueness clause (blueprint: def-pur-transport-adjunction-family). -/
def BrownComparison (D : WeilConjectures.FiniteFieldDatum.{u})
    (a : AdjunctionFamily ell D) : Prop :=
  ∀ (c : Coefficient ell) (s : SmoothDatum D)
    (hL : ∀ K, localizing ell c s.X.left K → localizing ell c s.Y.left
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) s.compactification).obj K))
    (G : (localizing ell c s.Y.left).FullSubcategory ⥤
      (localizing ell c s.X.left).FullSubcategory)
    (b : (localizing ell c s.Y.left).lift
      ((localizing ell c s.X.left).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification)
      (fun K ↦ hL K.obj K.property) ⊣ G),
    ∃ hG : ∀ K : c.ctf ell s.Y.left,
      property ell c s.X.left (G.obj ((inclusion ell c s.Y.left).obj K)).obj,
    ∃ bctf : support ell c s.compactification (a c s).support_closed ⊣ exceptional ell c G hG,
      (∀ K : c.ctf ell s.Y.left,
        HEq (bctf.counit.app K).hom
          (b.counit.app ((inclusion ell c s.Y.left).obj K)).hom) ∧
      ∃! gamma : source ell c s.map s.dim (a c s).source_closed ≅ exceptional ell c G hG,
        CounitCompatible (a c s).adjunction bctf gamma

end AlgebraicGeometry.ProEtale.PurityTransport
