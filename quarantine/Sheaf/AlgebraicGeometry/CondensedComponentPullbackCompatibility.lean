/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel

/-! # Component pullback and scalar compatibility on contractible affine schemes

Source: Hemo--Richarz--Scholbach, (4.1) and Proposition 4.3(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The component inverse image is coefficient compatible and gives the scalar
comparison square and lisse equivalence of HRS Proposition 4.3(3).

Source: Hemo--Richarz--Scholbach, (4.1), Proposition 4.3(3), and Remark 3.2
(blueprint: lem-zl-condensed-component-pullback-compatibility).

Proof: the universal property of the relative profinite test functor gives the
component site morphism and identifies its composite with restriction from the
condensed point. Take the adjunction mate of this identification and lift it to
abelian sheaves; uniqueness makes it monoidal. Applying it to the coefficient
ring gives alpha and beta with their displayed equality. Inverse image is exact
and commutes with the ordinary tensor product, so its termwise derived functor
is triangulated and symmetric monoidal and preserves the coefficient unit.
The finite-clopen refinement of covers makes the terminal pro-etale object
weakly contractible. The point-basis evaluation formula therefore identifies
its section ring with Lambda(pi_0 T), compatibly with constant sections. On
flat-term K-flat complexes, the ordinary pullback comparison and associativity
of balanced scalar tensors identify the two section-ring realization functors.
The inverse chain maps send b tensor (a tensor p) to ba tensor p and back to
b tensor (1 tensor p); these maps commute with differentials and chain maps.
K-flat tensor descent gives the natural square on unbounded derived categories.
Apply the contractible evaluation equivalences on the profinite component space
and on T. The square identifies component pullback on lisse objects with scalar
transport along the section-ring isomorphism, hence it is an equivalence.
Finally the same inverse-image factorization identifies the realizations from
the scalar ring at the point. Compose it with the scalar associativity square
to obtain the last displayed comparison in `componentComparisons`. The empty
scheme and the zero coefficient ring are included: all these module categories
and comparisons reduce to their zero objects. -/
theorem condensed_component_pullback_compatibility
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
    [(componentTests T).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (Scheme.ProEt.topology T)]
    [(componentInverse T).Braided]
    [PreservesFiniteLimits (componentInverse T)]
    [PreservesFiniteColimits (componentInverse T)] :
    ∃ α : (componentInverse T).mapMon.obj
        (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
        Mon.mk (condensedRingObj Λ.X T),
      (∃ β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
            (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T,
        NatTrans.IsMonoidal β.hom ∧ α.hom.hom = β.hom.app Λ.X) ∧
      componentComparisons Λ.X T α := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
