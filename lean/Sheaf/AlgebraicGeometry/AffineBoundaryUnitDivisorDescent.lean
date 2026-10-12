/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import Sheaf.AlgebraicGeometry.DivisorClassCurve
import Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange
import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence

/-! # Descent of principal boundary divisors

Source: blueprint thm-sc-constant-invariance, affine unit quotient paragraph.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Every boundary divisor of a unit after extension descends to a boundary divisor of a unit.
Source: blueprint thm-sc-constant-invariance, affine unit quotient paragraph.
(blueprint: lem-sc-affine-boundary-unit-divisor-descent).

Proof: compatibility with germs determines the supplied maps: on V = c.i(C), the
canonical restriction is c.i.appIso inverse followed by X.germToFunctionField V, and
comparison at any point of the nonempty open proves equality with the supplied map.
Apply this on both curves. A unit and its inverse have regular germs on C', so their
orders there are zero. Extend its boundary divisor by zero to a divisor D' on X'. It is
therefore the full principal divisor of that unit. Transport its boundary coefficients
back along e and extend by zero to D on X. The condition he specifies the actual rational
fibres, not an arbitrary boundary permutation. Flat base change pulls the ideal of each
rational point back to the ideal of its single k' fibre point; dualizing and multiplying
these point ideals proves that O(D) pulls back to O(D'). Every point has degree one, so
D and D' have the same degree. By Scheme.finsum_ord_eq_zero this degree is zero.
The divisor-class/Picard equivalence shows that O(D') is trivial. Form the degree-zero
Picard subgroups on X and X'; degree preservation under pullback restricts the Picard map
to them. Apply picZero_torsion_base_change with n=1, using just its injectivity conclusion.
This is the Jacobian argument: the natural Picard comparison identifies pullback with
J(k) to J(k'), which is injective since Spec k' to Spec k is an epimorphism. Thus O(D) is
trivial. The divisor-class equivalence gives a nonzero rational f with div(f)=D.
All its orders on C vanish, so the divisor exact sequence (or the DVR criterion and gluing
of regular rational functions and their inverses) gives a global unit on C with rational
image f. Germ compatibility identifies this image under the supplied map. Its boundary
divisor transports to the given one, proving range membership. With empty boundary both
ranges contain just zero, represented by the unit one; with singleton boundary the degree
zero condition likewise forces zero. -/
theorem affine_boundary_unit_divisor_descent
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    [IsIntegral c.Z] [IsNoetherian c.Z]
    [IsIntegral (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z]
    [IsNoetherian (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z] 
    (φ : Γ(C, ⊤) →+* c.Z.functionField)
      (φ' : Γ(CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤) →+*
        (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.functionField)
    (e : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base} ≃
        {P : closedPoints (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z //
          P.val ∉
            Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base})
    (hφ : (∀ (x : C) (s : Γ(C, ⊤)) (y : c.Z.presheaf.stalk (c.i.base x)),
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
            y))
    (he : (∀ P : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base},
        (CategoryTheory.Limits.pullback.fst c.g
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base
            (e P).val.val = P.val.val ∧
          ∀ Q : (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z,
            (CategoryTheory.Limits.pullback.fst c.g
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base Q =
              P.val.val → Q = (e P).val.val)) :
    Set.range (fun u' : Γ(CategoryTheory.Limits.pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)ˣ ↦
          Finsupp.subtypeDomain
            (fun P : closedPoints (c.baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z ↦
              P.val ∉
                Set.range (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base)
            ((c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.div
              (Additive.ofMul (Units.map φ'.toMonoidHom u')))) ⊆
      Finsupp.domCongr e ''
          Set.range (fun u : Γ(C, ⊤)ˣ ↦
            Finsupp.subtypeDomain (fun P : closedPoints c.Z ↦ P.val ∉ Set.range c.i.base)
              (c.Z.div (Additive.ofMul (Units.map φ.toMonoidHom u)))) := by sorry

end AlgebraicGeometry
