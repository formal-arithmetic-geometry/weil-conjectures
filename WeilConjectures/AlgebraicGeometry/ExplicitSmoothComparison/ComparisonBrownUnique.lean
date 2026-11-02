/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ExplicitSmoothAdjunctionData
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAdjunctions
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Identification with the restricted Brown adjoint

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/
sk-thm-purity-transport/sk-prop-sp-comparison-brown-unique.md and its proof
(blueprint: det-sp-comparison-brown-unique).

The statement compares the explicit smooth adjunction with the adjunction obtained by
restricting a Brown right adjoint.  The compact-support functor is written once, as the
literal `support` functor.  The conclusion first asserts that the restricted Brown right
adjoint is a right adjoint of this functor on bounded constructible finite-Tor objects,
with counit the restriction of the ambient Brown counit, and then that there is a unique
counit-compatible isomorphism from the explicit twisted inverse image.  The proof has
three parts.  First the localizing existence statement identifies the ambient
compact-support functor with the compactification composite.  Second the restriction
statement restricts the Brown adjunction along the full inclusions, with the inherited
counit.  Finally `Adjunction.rightAdjointUniq` applied to the two adjunctions supplies
the unique counit-compatible isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ExplicitSmoothComparison

/-- The restricted Brown right adjoint is a right adjoint of the same compact-support
functor on bounded constructible finite-Tor objects, with counit the restricted Brown
counit, and the explicit twisted inverse image is identified with it by a unique
counit-compatible isomorphism.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/
sk-prop-sp-comparison-brown-unique.md`, clauses “Same left adjoint”, “Restriction”, and
“Uniqueness” (blueprint: det-sp-comparison-brown-unique).

The hypotheses are the situation of the node: `a` is the explicit adjunction of
`det-sp-comparison-brown-explicit`, `brown` is the ambient Brown adjunction on the
localizing closures (`det-existence-localizing` (3)) and `hG` says that its right adjoint
`G` sends `Dctf(Y)` into `Dctf(X)` (`det-existence-restriction`), so that
`exceptional ell c G hG` is the restricted `f^!`.  Both adjunctions of the conclusion have
the literal compact-support functor `support ell c s.compactification a.support_closed`.

Proof.
1. Same left adjoint: `det-existence-localizing` (2) identifies the ambient compact-support
   functor with `R p_* ∘ j_!` for the compactification `s.compactification`; its
   restriction to `Dctf(X)` is the functor `support` of the explicit adjunction.
2. Restriction: by `det-existence-restriction` the adjunction `brown` restricts along the
   fully faithful inclusions `Dctf ⊆ Loc(Dctf)`; the Hom bijection is the restriction of
   the ambient one, so the restricted adjunction `brownCtf` has counit the restricted
   Brown counit (the `HEq` clause).
3. Uniqueness: apply `det-sp-unique-right-adjoint`
   (`CategoryTheory.Adjunction.rightAdjointUniq`) to `a.adjunction` and `brownCtf`; its
   components are the `brownCtf`-transposes of the explicit counit, the counit equation is
   `CounitCompatible`, and injectivity of the Hom bijection gives uniqueness. -/
theorem comparisonBrownUnique
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    (c : Coefficient ell) (s : Datum k)
    (a : ExplicitAdjunction ell c s)
    (hL : ∀ K, localizing ell c s.X K → localizing ell c s.Y
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) s.compactification).obj K))
    (G : (localizing ell c s.Y).FullSubcategory ⥤
      (localizing ell c s.X).FullSubcategory)
    (brown : (localizing ell c s.Y).lift
      ((localizing ell c s.X).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification)
      (fun K ↦ hL K.obj K.property) ⊣ G)
    (hG : ∀ K : c.ctf ell s.Y,
      property ell c s.X (G.obj ((inclusion ell c s.Y).obj K)).obj) :
    ∃ brownCtf : support ell c s.compactification a.support_closed ⊣
        exceptional ell c G hG,
      (∀ K : c.ctf ell s.Y,
        HEq (brownCtf.counit.app K).hom
          (brown.counit.app ((inclusion ell c s.Y).obj K)).hom) ∧
      ∃! gamma : source ell c s.map s.dim a.source_closed ≅ exceptional ell c G hG,
        CounitCompatible a.adjunction brownCtf gamma := by
  let iX := inclusion ell c s.X
  let iY := inclusion ell c s.Y
  let hiX : iX.FullyFaithful := by
    dsimp only [iX, PurityTransport.inclusion]
    exact ObjectProperty.fullyFaithfulιOfLE _
  let hiY : iY.FullyFaithful := by
    dsimp only [iY, PurityTransport.inclusion]
    exact ObjectProperty.fullyFaithfulιOfLE _
  let b : support ell c s.compactification a.support_closed ⊣ exceptional ell c G hG :=
    brown.restrictFullyFaithful hiX hiY (Iso.refl _) (Iso.refl _)
  refine ⟨b, ?_, a.adjunction.rightAdjointUniq b, ?_, ?_⟩
  · intro K
    have h := brown.map_restrictFullyFaithful_counit_app hiX hiY
      (L := support ell c s.compactification a.support_closed)
      (R := exceptional ell c G hG) (Iso.refl _) (Iso.refl _) K
    have h' := congrArg (fun f ↦ f.hom) h
    change (b.counit.app K).hom = 𝟙 _ ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) s.compactification).map (𝟙 _) ≫
      (brown.counit.app (iY.obj K)).hom at h'
    exact heq_of_eq (by
      simpa only [CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp] using h')
  · intro K
    exact a.adjunction.rightAdjointUniq_hom_app_counit b K
  · intro gamma hgamma
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply (b.homEquiv _ K).symm.injective
    simpa only [Adjunction.homEquiv_counit,
      Adjunction.rightAdjointUniq_hom_app_counit] using hgamma K

end AlgebraicGeometry.ProEtale.ExplicitSmoothComparison
