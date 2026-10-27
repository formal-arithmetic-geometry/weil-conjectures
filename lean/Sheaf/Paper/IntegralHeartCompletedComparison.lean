/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T7
-/
module

public import Sheaf.Paper.IntegralHeartLocalModelData
public import Sheaf.Paper.AdicStratifiedPerfectData
public import Sheaf.Paper.CompletedConstantConstructibility
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Comparing the two presentations of integral scalar realization

Source: the current blueprint, integral-heart-local-model, clause (1), coefficient
identifications preceding application of the local perfect-model theorem.
(blueprint: lem-sfb-integral-heart-completed-comparison)
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The continuous internal and completed sectionwise coefficient presentations have
an exact module equivalence preserving finite constant models and all local scalar
complex comparisons. The latter comparison imposes no boundedness, finiteness or
projectivity on the scalar complex and asserts no existence of local models.

Source: Bhatt--Scholze, Section 6.5, Proposition 6.6.11 and Definition 6.8.10;
the current blueprint integral-heart-local-model, clause (1), coefficient and slice
identifications. (blueprint: lem-sfb-integral-heart-completed-comparison)

Proof: put L equal to the canonical small presentation of E and R equal to the
lifted valuation ring of L. The continuous functions into its integers form the
inverse limit of the discrete positive uniformizer quotients: apply the profinite
tower isomorphism and the universal property of continuous maps out of a profinite
space. At finite level these functions are locally constant, hence the constant
quotient ring sheaf. Pull back to X using the profinite coefficient inverse-image
comparison, with every finite projection fixed. Reconstructing section rings and
applying the section-action module equivalence gives F; restriction along the
coefficient isomorphism is an equivalence, so F is additive and exact.

A finite presentation over the condensed point is a finite scalar matrix. The
normalized coefficient comparison sends its entries to the same constant scalar
sections. Exactness preserves its cokernel, giving the constructibility equivalence
on each chart. The equivalence commutes with inverse image to each stratum and with
slice restriction. Cover families generate covering sieves; conversely use a
quasi-compact refinement of a covering presieve. Retain the strata. Noetherian X
is qcqs, so this is precisely the stratified branch of constructibility.

For the second assertion identify the site sliced at U with the pro-etale site
of U.left. The coefficient comparison there is the inverse image of the one on X:
for the immersion use preservation of the profinite quotient limit, and for U use
slice restriction. The resulting exact equivalence of local module categories
identifies restriction of F(K) with inverse image of K. On scalar modules its
composite with completed constant scalar extension is integralHeartRealization:
both are the sheafified tensor extension along constant continuous functions,
with the same scalar action on pure tensors. The scalar comparison is natural
in every linear map, hence in every differential. Pass these exact equivalences
and natural comparisons to ordinary unbounded derived categories, and preserve
and reflect isomorphisms. This gives the displayed equivalence for arbitrary P
and K. No completion of K is taken. Zero scalar modules, torsion modules, arbitrary
degrees, and the empty scheme are covered by the same constructions. -/
theorem integralHeart_completed_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    let I : Ideal (integralHeartScalars.{u} ℓ E) :=
      Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer ℓ
        (SmallAdicCompletion.Coefficients.field ℓ E))}
    ∃ F : SmallAdicCompletion.Modules ℓ E X ≌
        Scheme.proEtaleRingModules X (Scheme.adicLisseCompletedRing X I),
      letI : F.functor.Additive := Functor.additive_of_preserves_binary_products _
      (∀ M : SmallAdicCompletion.Modules ℓ E X,
        IsConstantModelConstructible
            (SmallAdicCompletion.Coefficients.integerRing ℓ E) X M ↔
          Scheme.IsCompletedConstantStratified X I (F.functor.obj M)) ∧
      ∀ (S : Scheme.{u}) (f : S ⟶ X) [IsImmersion f] (U : S.ProEt)
        (K : integralHeartDerivedCategory.{u} ℓ E X)
        (P : CochainComplex (ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) ℤ),
        Nonempty (Scheme.sfbLocalRestriction f (Scheme.adicLisseCompletedRing X I) U
              (F.functor.mapDerivedCategory.obj K) ≅
            Scheme.sfbLocalRestriction f (Scheme.adicLisseCompletedRing X I) U
              (Scheme.sfbCompletedModel X I P)) ↔
          Nonempty (((CondensedRing.upperStar
              (SmallAdicCompletion.Coefficients.integerRing ℓ E)
              (U.hom ≫ f)).mapDerivedCategory).obj K ≅
            DerivedCategory.Q.obj
              (((integralHeartRealization.{u} ℓ E U.left).mapHomologicalComplex
                (.up ℤ)).obj P)) := by sorry

end AlgebraicGeometry.ProEtale
