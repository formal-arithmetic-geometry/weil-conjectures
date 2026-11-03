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

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
sk-prop-sp-comparison-brown-unique.md`, clauses “Same left adjoint”, “Restriction”, and
“Uniqueness” (blueprint: det-sp-comparison-brown-unique).

The hypotheses are the situation of the node: `f` is the actual smooth morphism of
pure relative dimension `d`, `c` is a listed admissible coefficient presentation,
and `a` is the explicit adjunction of `det-sp-comparison-brown-explicit` for the
literal compactification functor. The ambient Brown adjunction is `brown`
(`det-existence-localizing` (3)), and `hG` is its preservation of Dctf
(`det-existence-restriction`). Thus `exceptional ell c G hG` is the restricted
`f^!`. The old bundled hypotheses are written out without changing their content.

Proof.
1. Same left adjoint: both supplied adjunctions use the actual `Rp_* j_!` associated
   to the same compactification `cf`. Their restrictions have the literal left
   functor `support ell c cf hSupport`.
2. Restriction: restrict `brown` along the fully faithful inclusions
   `Dctf ⊆ Loc(Dctf)`. The Hom bijection is the restriction of the ambient one,
   and its counit is the restricted Brown counit (the `HEq` clause).
3. Uniqueness: apply `det-sp-unique-right-adjoint`
   (`CategoryTheory.Adjunction.rightAdjointUniq`) to `a` and the restricted Brown
   adjunction. Its components are the Brown transposes of the explicit counit;
   the counit equation is `CounitCompatible`. Injectivity of the Hom bijection
   proves uniqueness. -/
theorem comparisonBrownUnique
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    (c : Coefficient ell) {X Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of k)) [LocallyOfFiniteType base] [QuasiCompact base]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (cf : Compactification f)
    (hSupport : ∀ K, property ell c X K → property ell c Y
      ((CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj K))
    (hSource : ∀ K, property ell c Y K → property ell c X
      ((c.smoothSource ell f d).obj K))
    (a : support ell c cf hSupport ⊣ source ell c f d hSource)
    (hL : ∀ K, localizing ell c X K → localizing ell c Y
      ((CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj K))
    (G : (localizing ell c Y).FullSubcategory ⥤ (localizing ell c X).FullSubcategory)
    (brown : (localizing ell c Y).lift
      ((localizing ell c X).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf)
      (fun K ↦ hL K.obj K.property) ⊣ G)
    (hG : ∀ K : c.ctf ell Y,
      property ell c X (G.obj ((inclusion ell c Y).obj K)).obj) :
    ∃ brownCtf : support ell c cf hSupport ⊣ exceptional ell c G hG,
      (∀ K : c.ctf ell Y,
        HEq (brownCtf.counit.app K).hom
          (brown.counit.app ((inclusion ell c Y).obj K)).hom) ∧
      ∃! gamma : source ell c f d hSource ≅ exceptional ell c G hG,
        CounitCompatible a brownCtf gamma := by
  let iX := inclusion ell c X
  let iY := inclusion ell c Y
  let hiX : iX.FullyFaithful := by
    dsimp only [iX, PurityTransport.inclusion]
    exact ObjectProperty.fullyFaithfulιOfLE _
  let hiY : iY.FullyFaithful := by
    dsimp only [iY, PurityTransport.inclusion]
    exact ObjectProperty.fullyFaithfulιOfLE _
  let b : support ell c cf hSupport ⊣ exceptional ell c G hG :=
    brown.restrictFullyFaithful hiX hiY (Iso.refl _) (Iso.refl _)
  refine ⟨b, ?_, a.rightAdjointUniq b, ?_, ?_⟩
  · intro K
    have h := brown.map_restrictFullyFaithful_counit_app hiX hiY
      (L := support ell c cf hSupport)
      (R := exceptional ell c G hG) (Iso.refl _) (Iso.refl _) K
    have h' := congrArg (fun f ↦ f.hom) h
    change (b.counit.app K).hom = 𝟙 _ ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) cf).map (𝟙 _) ≫
      (brown.counit.app (iY.obj K)).hom at h'
    exact heq_of_eq (by
      simpa only [CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp] using h')
  · intro K
    exact a.rightAdjointUniq_hom_app_counit b K
  · intro gamma hgamma
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply (b.homEquiv _ K).symm.injective
    simpa only [Adjunction.homEquiv_counit,
      Adjunction.rightAdjointUniq_hom_app_counit] using hgamma K

end AlgebraicGeometry.ProEtale.ExplicitSmoothComparison
