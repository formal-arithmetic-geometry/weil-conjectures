/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.TwoTermFreeHomTensorCoordinateMap

/-! # Unit-normalized tensor representatives of integral reduction towers

Source: the finite-free quotient resolution in the first paragraph of the current
blueprint `lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 06YY, 08J7 and 07A6.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The two reduction towers have separate tensor models preserving their units.
This asserts no isomorphism between Hom tensor Q_n and Hom into tensor Q_n.
The only comparison normalization is at the coefficient unit B=R[0].

Source: current blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1,
finite-free construction; Stacks Tags 06YY, 08J7, 07A6 and 08TC
(blueprint: lem-sf-integral-hom-tower-unit-models).

Proof: use Q_n=[R --pi^(n+1)--> R] in degrees -1,0, with transitions (pi,id).
The degree-zero inclusions B=R[0] -> Q_n form a cone. Their composites with
Q_n -> A_n are the ordinary quotient units. These quasi-isomorphisms follow
from regularity of pi on the completed coefficient sheaf and identification
of its quotient. Choose a K-flat A representing K and a K-injective I
representing Q(G). Tensor with Q_n computes each reduction, since Q_n is
bounded free; I tensor Q_n is K-injective because it is a finite cone of
shifts of I. The Hom complexes therefore give the first tower model.
Hom(A,I) tensor Q_n gives the second, using e and the K-flat computation on
q'. Naturality of these calculations for (pi,id) gives s and t. Applying
them also to B gives s0,t0. Naturality for B -> Q_n gives the two separate
augmentation equations hs and ht, using the ordinary scalar unit 1 tensor x
and the canonical resolution-independent augmentation. At B, both tensor
functors identify with their untensored complexes by the right unitor.
A map satisfying IsSignedHomTensor has coefficient degree zero, hence sign
one, and acts as the identity under these unitors: evaluate on every local
section, then use the Hom product projections and sheafification universal
property. Thus its localization identifies t0 with s0 after e inverse,
which is precisely the last displayed equality. None of this proves that
the signed comparison is invertible at Q_n. Zero inputs, n=0 and the empty
scheme cause no exception to the same constructions. -/
theorem reductionTower_unit_models
    (K : completedIntegralDerivedCategory l E Y D hl)
    (P G P' G' : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G) (q' : P' ⟶ G')
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q')
    (e : DerivedCategory.Q.obj G' ≅
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
        (op K, DerivedCategory.Q.obj G)) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    let H := (Functor.curry.obj (hom.{t, u} Y R)).obj (op K)
    let B : CochainComplex (Modules.{t, u} Y R) ℤ :=
      (CochainComplex.singleFunctor (Modules.{t, u} Y R) 0).obj
      (show Modules.{t, u} Y R from SheafOfModules.unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
    ∃ (A I : CochainComplex (Modules.{t, u} Y R) ℤ)
      (Q : ℕᵒᵖ ⥤ CochainComplex (Modules.{t, u} Y R) ℤ),
      (∀ n : ℕ,
        (∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero ((Q.obj (op n)).X k)) ∧
        Nonempty ((Q.obj (op n)).X (-1) ≅ (show Modules.{t, u} Y R from
          SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))) ∧
        Nonempty ((Q.obj (op n)).X 0 ≅ (show Modules.{t, u} Y R from
          SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))) ∧
      let S := (totalTensor.{t, u} Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I) ⋙
          DerivedCategory.Q
      let T := (totalTensor.{t, u} Y R).obj I ⋙
        (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := R)).obj (op A) ⋙ DerivedCategory.Q
      ∃ (ι : (Functor.const ℕᵒᵖ).obj B ⟶ Q)
        (s : integralReductionTower l E Y D hl P ⋙ H ≅ Q ⋙ T)
        (t : integralReductionTower l E Y D hl P' ≅ Q ⋙ S)
        (s0 : H.obj (DerivedCategory.Q.obj G) ≅ T.obj B)
        (t0 : DerivedCategory.Q.obj G' ≅ S.obj B),
        (∀ n : ℕ,
          H.map ((integralReductionTowerCone l E Y D hl q hq).π.app (op n)) ≫
              s.hom.app (op n) = s0.hom ≫ T.map (ι.app (op n))) ∧
        (∀ n : ℕ,
          (integralReductionTowerCone l E Y D hl q' hq').π.app (op n) ≫
              t.hom.app (op n) = t0.hom ≫ S.map (ι.app (op n))) ∧
        ∀ f : ((totalTensor.{t, u} Y R).obj
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I)).obj B ⟶
            homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A
              (((totalTensor.{t, u} Y R).obj I).obj B),
          IsSignedHomTensor.{t, u} Y R A I B f →
            e.inv ≫ t0.hom ≫ DerivedCategory.Q.map f = s0.hom := by sorry

end WeilConjectures.IntegralHom
