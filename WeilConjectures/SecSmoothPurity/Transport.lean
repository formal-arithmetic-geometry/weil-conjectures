/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SecSmoothPurity.TransportCompatibility
public import WeilConjectures.SecSmoothPurity.TransportScalarCompatibility
public import WeilConjectures.SecSmoothPurity.TransportAffineNormalization

/-! # Smooth purity for every admissible condensed coefficient

Source: current blueprint, sk-thm-purity-transport, all clauses, including the
2026-10-25 correction of the etale specialization.
(blueprint: sk-thm-purity-transport).
-/
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

/-- The same family of explicit right adjunctions has the prescribed integration
counits, coefficient equations and geometric equations, and gives the unique
counit-compatible natural purity isomorphism to each specified Brown adjoint.
Source: current blueprint sk-thm-purity-transport
(blueprint: sk-thm-purity-transport).
Proof in words. For every finite ring, including nonregular and zero rings, use
the finite normalized counit system and its section-action realization. Reconstruct
the integral adjunction from the normalized positive tower and its transition
counits. Localize the Hom bijections and counits to obtain rational coefficients.
Descend objects and arrows for the algebraic closure to a common finite stage.
The resulting adjunctions have the displayed coefficient, base-change and
composition equations and the affine integration normalization. Restrict the
specified Brown adjunction to finite Tor objects. Uniqueness of right adjoints
with a fixed counit gives the natural gamma, uniquely satisfying its counit
identity. The transported finite and reconstructed comparisons satisfy that
identity and therefore are this same gamma. -/
theorem smooth_purity_transport (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) :
    ∃ a : AdjunctionFamily ell D,
      BrownComparison ell D a ∧
      ScalarCompatible ell D a ∧
      BaseChangeCompatible ell D a ∧
      CompositionCompatible ell D hEll a ∧
      AffineNormalized ell D a := by
  sorry

/-- The d=0 application for an etale map. No assertion that an arbitrary supplied
relative dimension is zero is made, including for the empty scheme.
Source: final paragraph of sk-thm-purity-transport
(blueprint: sk-thm-purity-transport).
Proof in words. Etale is smooth of pure relative dimension zero. Apply the main
family at that zero-dimensional geometric index and compare with the specified
Brown adjoint. The zeroth tensor power is the coefficient unit and the shift is
zero. The canonical inverse-image and tensor unitors identify the explicit source
with the ordinary derived pullback, giving the asserted natural isomorphism. -/
theorem etale_purity_transport (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (c : Coefficient ell)
    (X Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X.left ⟶ Y.left) [f.IsOver (Spec (.of D.k))] [Etale f] [IsSeparated f]
    (cf : Compactification f)
    (hL : ∀ K, localizing ell c X.left K → localizing ell c Y.left
      ((CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj K))
    (G : (localizing ell c Y.left).FullSubcategory ⥤
      (localizing ell c X.left).FullSubcategory)
    (_b : (localizing ell c Y.left).lift
      ((localizing ell c X.left).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf)
      (fun K ↦ hL K.obj K.property) ⊣ G) :
    ∃ (hp : ∀ K, property ell c Y.left K → property ell c X.left
        ((CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor.obj K))
      (hG : ∀ K : c.ctf ell Y.left,
        property ell c X.left (G.obj ((inclusion ell c Y.left).obj K)).obj),
    Nonempty ((property ell c X.left).lift
      ((property ell c Y.left).ι ⋙ (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor)
      (fun K ↦ hp K.obj K.property) ≅ exceptional ell c G hG) := by
  sorry

/-- For a smooth curve the integral exceptional unit is precisely the actual
root-tower Tate sheaf shifted by two, and has no other cohomology sheaves.
Source: last sentence of sk-thm-purity-transport
(blueprint: sk-thm-purity-transport).
Proof in words. Apply the main theorem with integral coefficients and relative
dimension one, at the coefficient unit. Cartesian pullback sends that unit to the
coefficient unit. The tensor unitors and scalar extension along the identity
identify the resulting line with the existing tateModule, so gamma gives the
stated object isomorphism. A single sheaf shifted by two has cohomology only in
degree minus two; transport this vanishing through that same isomorphism. -/
theorem curve_purity_transport (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (C : Over (Spec (.of D.k)))
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [SmoothOfRelativeDimension 1 C.hom] (cf : Compactification C.hom)
    (hL : ∀ K, localizing ell (.integers) C.left K →
      localizing ell (.integers) (Spec (.of D.k))
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          ((Coefficient.integers : Coefficient ell).obj ell) cf).obj K))
    (G : (localizing ell (.integers) (Spec (.of D.k))).FullSubcategory ⥤
      (localizing ell (.integers) C.left).FullSubcategory)
    (_b : (localizing ell (.integers) (Spec (.of D.k))).lift
      ((localizing ell (.integers) C.left).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          ((Coefficient.integers : Coefficient ell).obj ell) cf)
      (fun K ↦ hL K.obj K.property) ⊣ G) :
    ∃ hU : property ell (.integers) (Spec (.of D.k))
      (unit ell (.integers) (Spec (.of D.k))),
    ∃ hG : ∀ K : (Coefficient.integers : Coefficient ell).ctf ell (Spec (.of D.k)),
      property ell (.integers) C.left
        (G.obj ((inclusion ell (.integers) (Spec (.of D.k))).obj K)).obj,
    Nonempty (((exceptional ell (.integers) G hG).obj ⟨_, hU⟩).obj ≅
      ((DerivedCategory.singleFunctor _ 0).obj (tateModule C.left ell)) ⟦(2 : ℤ)⟧) ∧
      ∀ i : ℤ, i ≠ -2 → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((exceptional ell (.integers) G hG).obj ⟨_, hU⟩).obj) := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
