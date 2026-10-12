/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# Compatibility of Jacobian identifications with base change
Source: blueprint `lem-sc-genus-invariant`, proof step 3.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- The compatibility square for two Jacobian representing objects after base change.
Source: blueprint `lem-sc-genus-invariant`, proof step 3 (Picard base-change and Yoneda).
Proof: on each test scheme T over K, the iterated-pullback isomorphism identifies
C_K ×_K T with C ×_k T. Pullback of invertible modules along this isomorphism preserves
fibrewise degree, because the two fibres and their Euler characteristics agree. Thus it
induces an isomorphism of degree-zero Picard presheaves. Restriction along Over.map b
commutes with fppf sheafification, since covers of T in the two slice sites are the same;
compose this comparison with the sheafification of the presheaf isomorphism to get E.
The units of sheafification commute with E, so E sends the class of L to the class of its
specified pullback. The adjunction Over.map b ⊣ Over.pullback b transports e to a
representation r of the restricted sheaf by J_K. Transport r along E, and compare it with
eK using uniqueness of representing objects (Yoneda). This gives i : JK ≅ J_K with
r.homEquiv (a ≫ i.hom) = eK.homEquiv a. Apply this to the classifying map of the
pullback of L, use the unit compatibility, and invert e.homEquiv. The inverse adjunction
sends a map to J_K to its composite with pullback.fst J.hom b, giving exactly the square.
This construction applies to arbitrary representing identifications, hence also to those
respecting the group laws. Identity extensions and genus-zero curves are included.
(blueprint: lem-sc-jacobian-base-change-compatible) -/
theorem jacobian_compatibility
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    [IsProper f] [GeometricallyIntegral f] :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let fK := pullback.snd f b
    ∀ [hcurve : IsConnectedCurve fK],
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
            ⟨L, hL⟩)).left := by
  sorry

end AlgebraicGeometry
