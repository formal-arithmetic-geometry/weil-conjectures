/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalar

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-scalar-line-coordinates). -/

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

/-- Positive scalar Tate-line coordinates are fixed by the coefficient unit and
balanced tensor recursion. Source: coefficient compatibility
(blueprint: def-pur-transport-scalar-line-coordinates). -/
structure ScalarLineCoordinates {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) where
  first : (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X)).obj
    (c.firstLine ell X) ≅ c'.firstLine ell X
  first_normalized : HEq first (scalarFirst ell a ha X)
  power : ∀ d : ℕ, (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X)).obj
    (c.line ell X d) ≅ c'.line ell X d
  power_normalized : ∀ (m : (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X)).Monoidal)
    (_hm : ∀ M N, Mod.tensorObjπ M N ≫
      (Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) (M ⊗ N)).hom ≫
        (m.toOplaxMonoidal.δ M N).hom =
      ((Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) M).hom ⊗ₘ
        (Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) N).hom) ≫
      Mod.tensorObjπ ((Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X)).obj M)
        ((Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X)).obj N)) (d : ℕ),
    letI := m
    HEq (power d) (powerPull (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X))
      (c.firstLine ell X) (c'.firstLine ell X) first d)

/-- The scalar source comparison uses the canonical nonflat scalar/pullback mate,
the K-flat tensorator, and the specified shifted Tate scalar map.
Source: coefficient compatibility (blueprint: def-pur-transport-scalar-line-coordinates). -/
def sourceScalar {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    (p : ScalarLineCoordinates ell a ha X) (K : c.derived ell Y) :
    (scalarSixChange a X).obj ((c.smoothSource ell f d).obj K) ⟶
      (c'.smoothSource ell f d).obj ((scalarSixChange a Y).obj K) :=
  (scalarTensor ell a X _ _).inv ≫
    (Iso.hom
      ((scalarSixChange a X).mapIso
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) f).app K) ≪≫
      (scalarPullbackIso a f).app K ≪≫
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c'.obj ell) f).app _).symm) ⊗ₘ
      scalarLineMap ell a X d (p.power d))

end AlgebraicGeometry.ProEtale.PurityTransport
