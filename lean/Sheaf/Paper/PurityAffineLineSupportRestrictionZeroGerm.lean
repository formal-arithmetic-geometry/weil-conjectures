/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.PurityAffineLineOrientation
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-! # Local vanishing of normalized supported restriction

Source: blueprint main-20261015, prop-pur-affine-line-orientation-uniqueness,
proof Steps 2–3; Milne, Theorem 9.4 and Example 9.5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

local instance (P : PurityFiniteSetting.{u}) :
    PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} P.Coefficient)) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

/-- A section of the degree-zero Gysin sheaf with zero geometric germ has zero
supported restriction to that geometric fibre.

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4 (functoriality
for pairs), Theorem 9.7 (excision), and Example 9.5 (evaluation on 1); blueprint
main-20261015, prop-pur-affine-line-orientation-uniqueness, proof Step 2
(blueprint: lem-pur-affine-line-support-restriction-zero-germ).

Proof:
1. A linear map out of the constant-sheaf stalk is determined by its value on 1.
Thus the hypothesis makes the entire stalk map zero. The identity geometric stalk
on Spec Omega is faithful: constant sheaves and global sections are inverse
equivalences there, and the constant-sheaf stalk comparison identifies its
composite with constants with the identity. The inverse-image/stalk comparison
therefore gives y_et^*(b)=0. Equivalently, filtered-colimit equality witnesses the
vanishing on a pointed etale neighbourhood of y.
2. The Gysin Hom-to-sections bijection lifts gysinEvaluate(nu(b) followed by e) to
m:A_Y[0] -> G. Evaluation on 1 is injective on maps from A_Y, by the two defining
adjunctions and linearity, so H0(m), with its canonical source identification,
is exactly nu(b) followed by e. Exact site comparison and coherent pullback give
y_pro^* H0(m)=0. Since G is concentrated in degree zero, choose G isomorphic to
N[0], lift m to a sheaf map using singleFunctor fullness, and apply the exact
pullback. Its cohomology map is zero, so singleFunctor faithfulness gives
y_pro^*(m)=0. This uses no conservativity on arbitrary pro-etale sheaves.
3. Evaluation on 1 identifies Hom from the constant sheaf with global sections,
naturally and additively. Derive this identification and apply the RHom cocycle-roof
comparison to identify hypercohomology with derived Hom, preserving cocycle classes.
Use the specified compactification (id,s). The class adjunction and fully
faithful bounded-below comparison express the finite exceptional Hom as Hom from
the etale supported constant, shifted by minus two. The normalized supported-Hom
identification gives the same representation for the actual kernel-derived
support group. Thus the natural supportIso, in these two coordinates, is a
natural automorphism of this representable functor. Yoneda says it is
precomposition with a fixed endomorphism t of the supported constant. Its exact
value is unnecessary for vanishing: pulling back f after t gives pullback(t)
followed by pullback(f). The cocycle normalization of edge, edge_spec and
support_spec identify D.support(gysinEvaluate(nu(b) followed by e)) with the image
of the canonical adjoint of m under precisely this natural support comparison.
4. Lift m to the bounded-below etale antecedents retained by the class adjunction.
Coherent comparison and faithfulness transport the zero pullback from step 2.
For the ordinary etale closed adjunction S left adjoint R, write its transpose as
S(m) followed by the counit. The finite closed direct-image exchange is invertible
and natural in the source. Its naturality square rewrites the pullback of this
transpose, after precomposition by that exchange inverse, as S' applied to the
zero pullback of m, followed by the pulled-back counit. Hence the pulled-back
transpose is zero. This is ordinary closed direct-image base change, with no
invertibility assertion about exceptional base change.
5. By step 3 its precomposition by t also has zero pullback. Apply supportedHom_pullback
and its coefficient naturality. They identify this pulled-back Hom with the actual
kernel-derived restriction followed by orientationInputPullback. A transport p has
this same derived map: supportUnit_spec determines its support unit after the monic
kernel inclusion, and its terminal map is unique over the pullback of the identity.
The target supported-Hom identification is injective, so the displayed restriction
is zero. All arguments include the zero ring and each pointed component separately;
an empty base has no geometric point, and Omega need not be finite type over k. -/
theorem affineLine_support_restriction_zero_germ (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (D : OrientationSupportData P h Y)
    (H : ProEtale.RetractedSupport.EtSheaves P Y)
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj H ≅
      (DerivedCategory.homologyFunctor
        (ProEtale.RetractedSupport.ProSheaves P Y) 0).obj (P.gysinValue h Y))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (p : proEtaleSupportHomTransport P (zeroSection Y)
      (zeroSection (Spec (CommRingCat.of Ω))) (AffineSpace.map (ULift.{u} (Fin 1)) y))
    (b : P.constantEtale Y ⟶ H)
    (hb : ((Scheme.pointSmallEtale y).sheafFiber.map b)
      (((Scheme.pointSmallEtale y).sheafFiberConstantSheafIso
        (ModuleCat.of P.Coefficient P.Coefficient)).inv 1) = 0) :
    P.orientationSupportRestriction h y p
      (D.support.hom (P.gysinEvaluate Y
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map b ≫
          e.hom))) = 0 := by
  sorry

end WeilConjectures.PurityFiniteSetting
