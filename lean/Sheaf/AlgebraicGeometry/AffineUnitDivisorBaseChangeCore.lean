/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import Sheaf.AlgebraicGeometry.LocalDvrBaseChange

/-! # Boundary geometry and forward comparison of unit divisors

Source: blueprint thm-sc-constant-invariance, affine unit quotient paragraph.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Boundary geometry, compatible rational maps, and preservation of unit orders.
Source: blueprint thm-sc-constant-invariance, affine unit quotient paragraph.
(blueprint: lem-sc-affine-unit-divisor-base-change-core).

Proof: put V = c.i(C), a nonempty open in the integral compactification X. Define the
restriction map as the inverse of c.i.appIso at the top open, followed by
X.germToFunctionField V; do the same on X'. Naturality of germs and
Scheme.algebraMap_germ_eq_germToFunctionField prove the stated compatibility. Conversely,
compatibility determines each map by evaluating at any point of the nonempty open.
The complement of V is a finite set of closed points: X is a Noetherian integral curve and
V is nonempty. Each boundary point is k-rational by algebraic closedness and finite type.
Scheme.local_dvr_base_change constructs its unique rational closed point above it. The
cartesian open-immersion square says that the complement of V' is the inverse image of
the complement of V. Hence the unique-fibre assignment is a bijection of the boundaries.
At corresponding points, Scheme.local_dvr_base_change also constructs the rational
pullback from the stalk map and proves equality of normalized orders. The two restriction
maps commute with this rational pullback: compare their germs on the common nonempty open
and specialize to the generic points. Thus the order comparison applies to the pulled-back
unit. Use Scheme.div_apply and equality coefficient by coefficient to obtain the Finsupp
equality. The empty boundary case gives the empty equivalence and zero divisors. -/
theorem affine_unit_divisor_base_change_core
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    [IsIntegral c.Z] [IsNoetherian c.Z]
    [IsIntegral (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z]
    [IsNoetherian (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z] :
    ∃ (φ : Γ(C, ⊤) →+* c.Z.functionField)
      (φ' : Γ(CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤) →+*
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.functionField),
      (∀ (x : C) (s : Γ(C, ⊤)) (y : c.Z.presheaf.stalk (c.i.base x)),
        c.i.stalkMap x y = C.presheaf.germ ⊤ x trivial s →
          φ s = algebraMap (c.Z.presheaf.stalk (c.i.base x)) c.Z.functionField y) ∧
      (∀ (x : (CategoryTheory.Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :
          Scheme.{u}))
        (s : Γ(CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤))
        (y : (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.presheaf.stalk
          ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base x)),
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.stalkMap x y =
            (CategoryTheory.Limits.pullback f
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).presheaf.germ
              ⊤ x trivial s →
          φ' s = algebraMap
            ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.presheaf.stalk
              ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base x))
            (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.functionField
            y) ∧
    ∃ e : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base} ≃
        {P : closedPoints (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z //
          P.val ∉
            Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base},
      (∀ P : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base},
        (CategoryTheory.Limits.pullback.fst c.g
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base
            (e P).val.val = P.val.val ∧
          ∀ Q : (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z,
            (CategoryTheory.Limits.pullback.fst c.g
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base Q =
              P.val.val → Q = (e P).val.val) ∧
      (∀ u : Γ(C, ⊤)ˣ,
        Finsupp.subtypeDomain
            (fun P : closedPoints (c.baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z ↦
              P.val ∉
                Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base)
            ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.div
              (Additive.ofMul (Units.map φ'.toMonoidHom
                (Units.map (CategoryTheory.Limits.pullback.fst f
                  (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop.hom.toMonoidHom
                  u)))) =
          Finsupp.domCongr e
            (Finsupp.subtypeDomain (fun P : closedPoints c.Z ↦ P.val ∉ Set.range c.i.base)
              (c.Z.div (Additive.ofMul (Units.map φ.toMonoidHom u))))) := by sorry

end AlgebraicGeometry
