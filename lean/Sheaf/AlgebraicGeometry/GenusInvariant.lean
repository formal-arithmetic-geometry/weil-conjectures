/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.AlgebraicGeometry.Curve.ProperProjective
import Sheaf.AlgebraicGeometry.SmoothProjectiveCurve
import Sheaf.AlgebraicGeometry.Variety
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Genus and Jacobians under algebraically closed extension

Source: blueprint, `sec-curve-estimates/sk-prop-ext-invariance`, order 1030
(blueprint: lem-sc-genus-invariant).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint, `sec-curve-estimates/sk-prop-ext-invariance`, order 1030
(blueprint: lem-sc-genus-invariant).

The genus is unchanged, and any two Jacobian identifications are carried to one another
by an isomorphism over the extended field. Compatibility is tested on degree-zero line
bundles over every test scheme: the canonical iterated-pullback isomorphism transports the
line bundle, and the classifying morphisms agree after projection to the original Jacobian.
The maps from line bundles to the Picard sheaf are locally surjective, so this tests equality
of the representing identifications, including on sheafified sections.

Proof, step 1: use def-sc-curves, lem-sc-proper-dim-one-projective,
lem-sc-smooth-regular and lem-weil-pbc-finite-type-over-noetherian to obtain a smooth
projective integral curve. A rational point exists by lem-pc-rational-points-dense over the
separably closed ground field; prop-pc-xk-integral gives geometric integrality. The
base-changed curve is proper, smooth and connected by lem-sc-base-change-curve and
prop-pc-xk-integral, and remains geometrically integral by transitivity of base change.
Step 2: def-sc-genus and lem-sc-flat-base-change-coherent, applied to the structure sheaf
in degree one, give equality of genera (equivalently the dimensions of global differentials).
Step 3: thm-sc-jacobian-representability gives the two Jacobians of def-sc-jacobian.
By cor-pd-pic0-base-change, restrict the first representing identification to the extended
field and transport it through the canonical Picard base-change identification. Compose
with the inverse of the second identification. Yoneda (Stacks Tag 01JF) gives the desired
isomorphism of representing schemes, and its construction gives the asserted square on
line bundles, hence on the Picard sheaves. -/
theorem genus_jacobian_invariant
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let fK := pullback.snd f b
    ∃ (_ : GeometricallyIntegral f) (_ : IsConnectedCurve fK)
      (_ : GeometricallyIntegral fK),
      fK.genus = f.genus ∧
      (∃ (J : Over (Spec (.of k))) (_ : GrpObj J), IsJacobian f J) ∧
      (∃ (J : Over (Spec (.of K))) (_ : GrpObj J), IsJacobian fK J) ∧
      ∀ (J : Over (Spec (.of k))) [GrpObj J] [IsJacobian f J]
        (e : (picardFunctorDegree f 0).obj.RepresentableBy J), IsPicardZeroMul f e →
      ∀ (JK : Over (Spec (.of K))) [GrpObj JK] [IsJacobian fK JK]
        (eK : (picardFunctorDegree fK 0).obj.RepresentableBy JK), IsPicardZeroMul fK eK →
      ∃ i : JK ≅ Over.mk (pullback.snd J.hom b),
      ∀ (T : Over (Spec (.of K))) (L : (pullback f (T.hom ≫ b)).Pic)
        (hL : L ∈ (picardSubfunctorDegree f 0).obj (.op ((Over.map b).obj T))),
      ∃ hLK : Pic.map (pullbackLeftPullbackSndIso f b T.hom).hom L ∈
          (picardSubfunctorDegree fK 0).obj (.op T),
        (eK.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
          (picardSubfunctorDegree fK 0).toFunctor).app (.op T)
            ⟨Pic.map (pullbackLeftPullbackSndIso f b T.hom).hom L, hLK⟩)).left ≫
            i.hom.left ≫ pullback.fst J.hom b =
        (e.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor).app (.op ((Over.map b).obj T))
            ⟨L, hL⟩)).left :=
  sorry

end AlgebraicGeometry
