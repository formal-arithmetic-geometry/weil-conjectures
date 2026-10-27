/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.SpaceGroup
public import Sheaf.AlgebraicGeometry.SpaceRelativeDifferentialsModel
public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.SpaceSquareZeroStalkData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations

/-! # Additivity of the actual square-zero difference coordinate

Source: Stacks Project, Tag 0BF5, generalized to algebraic spaces and arbitrary
square-zero ideals using Tags 0618, 0619 and 04D0
(blueprint: lem-sfb-group-space-square-zero-difference-additive).

The formula is evaluated on every compatible pair of étale charts and every lift of
its chart map. All ring maps are pullbacks of regular functions along scheme maps.
The coefficient is the actual square-zero kernel with its prescribed scalar action.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Yoneda turns a test point into its morphism to the algebraic space.
Source: Stacks, Tag 025Y
(blueprint: lem-sfb-group-space-square-zero-difference-additive). -/
def squareZeroPointMap {S : Scheme.{u}} {G : AlgebraicSpace S}
    {T : Over S} (b : G.obj.obj.obj (op T)) : schemeSpace T ⟶ G :=
  ObjectProperty.homMk ⟨yonedaEquiv.symm b⟩

/-- The kernel of restriction to the reduced scheme, as a set of actual points.
Source: Stacks, Tags 0618 and 0BF5
(blueprint: lem-sfb-group-space-square-zero-difference-additive). -/
def squareZeroGroupKernel {S : Scheme.{u}} {G : AlgebraicSpace S}
    (H : SpaceGroup G) {T₀ T : Over S} (j : T₀ ⟶ T) :=
  {b : G.obj.obj.obj (op T) // G.obj.obj.map j.op b = H.onePoint T₀}

/-- Chartwise meaning of δ(b): the module map applied to 1 ⊗ dz is b♯(z)−e♯(z).
For a compatible reduced chart map q, formal étaleness gives its unique lift along
each of b and e. Quantifying all such lifts gives the actual difference of ring-sheaf
maps on the sites identified by the thickening. The inclusion is injective with image
exactly the kernel, so this specifies the sign and the coefficient map uniquely.
Source: Stacks, Tags 0618 and 0619
(blueprint: lem-sfb-group-space-square-zero-difference-additive). -/
def IsGroupSquareZeroDifference {S : Scheme.{u}} {G : AlgebraicSpace S}
    (H : SpaceGroup G) {T₀ T : Over S} {j : T₀ ⟶ T}
    (W : ThickeningSiteModel (groupSchemeMap j)) (J : SquareZeroIdeal W)
    (D : SpaceRelativeDifferentialsModel (groupSpaceProjection G))
    (b : squareZeroGroupKernel H j)
    (h : (moduleTensorPullback (squareZeroPointMap (H.onePoint T₀))).obj D.omega ⟶ J.obj) :
    Prop :=
  ∀ (V : G.EtaleSite) (q : ModuleChart (squareZeroPointMap (H.onePoint T₀)) V)
    (r s : (W.equivalence.inverse.obj q.left).obj.left ⟶ V.obj.left),
    W.reduction.app q.left ≫ r = q.hom.left →
    W.reduction.app q.left ≫ s = q.hom.left →
    yoneda.map r ≫ V.obj.hom =
      (W.equivalence.inverse.obj q.left).obj.hom ≫ (squareZeroPointMap b.val).hom.hom →
    yoneda.map s ≫ V.obj.hom = (W.equivalence.inverse.obj q.left).obj.hom ≫
      (squareZeroPointMap (H.onePoint T)).hom.hom →
    ∀ z : G.structureSheaf.obj.obj (op V),
      J.inclusion q.left
        (h.val.app (op q.left)
          (moduleTensorSection (squareZeroPointMap (H.onePoint T₀)) D.omega V q 1
            (D.derivation.d z))) =
        Scheme.Γ.map r.left.op z - Scheme.Γ.map s.left.op z

/-- The actual difference coordinate sends the identity to zero and multiplication
to addition, with no commutativity or smoothness assumption.
The affine square-zero thickening is specified by j and its canonical defining ideal;
choosing affine coordinates identifies it with Spec(A/I) → Spec(A), I²=0.
W and J are normalized presentations of its étale-site equivalence and actual ideal,
not free choices of a coefficient or a map. D is Ω¹ characterized by universality.
The existential δ is fixed by its displayed difference formula. Product points are
quantified together with their value equation so no auxiliary closure proof is hidden
in a subtype constructor; every pair has that product by naturality of the group law.
Source: Stacks, Tag 0BF5 and Tags 0618, 0619, 04D0
(blueprint: lem-sfb-group-space-square-zero-difference-additive).

Proof:
1. Apply lem-sfb-space-square-zero-lift-linearization at the identity. Its lifts are
   precisely the kernel and its coordinate is b♯−e♯, an S-derivation. The universal
   property of D and the tensor adjunction give the normalized module map. The identity
   has zero difference, hence zero coordinate. No smoothness is needed.
2. Apply the same linearization to G×_S G at (e,e). Postcomposition with its two
   projections gives a linear map q to M×M. Pairing lifts is its inverse on points,
   so q is bijective. Its inverse is additive by injectivity of q.
3. Postcomposition with multiplication gives a linear map F=m_*q⁻¹:M×M→M.
   Naturality says δ(xy)=F(δ(x),δ(y)). The two unit identities imply F(v,0)=v and
   F(0,w)=w, whence linearity gives F(v,w)=v+w. This uses no commutativity of G.
-/
theorem groupSpace_squareZero_difference_additive {S : Scheme.{u}}
    (G : AlgebraicSpace S) (H : SpaceGroup G) {T₀ T : Over S} (j : T₀ ⟶ T)
    [IsAffine T.left] [IsAffine T₀.left] (hj : IsFirstOrderThickening j.left)
    (W : ThickeningSiteModel (groupSchemeMap j)) (J : SquareZeroIdeal W)
    (D : SpaceRelativeDifferentialsModel (groupSpaceProjection G)) :
    ∃ δ : squareZeroGroupKernel H j →
        ((moduleTensorPullback (squareZeroPointMap (H.onePoint T₀))).obj D.omega ⟶ J.obj),
      (∀ b, IsGroupSquareZeroDifference H W J D b (δ b)) ∧
      (∀ b : squareZeroGroupKernel H j, b.val = H.onePoint T → δ b = 0) ∧
      ∀ x y z : squareZeroGroupKernel H j,
        z.val = H.mulPoint T x.val y.val → δ z = δ x + δ y := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
