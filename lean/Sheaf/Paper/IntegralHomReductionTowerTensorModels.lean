/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels

/-! # Separate tensor representatives of integral reduction towers

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

/-- Both reduction towers have tensor representatives using the same two-term
coefficient tower. The two isomorphisms identify the towers separately; no
comparison between Hom tensor Q and Hom into a tensor is asserted here.

Source: the first paragraph of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`, the free resolution of the quotient;
Stacks Tags 06YY, 08J7, 07A6 and 08TC
(blueprint: lem-sf-integral-hom-tower-tensor-models).

Proof: let R be the completed coefficient sheaf and pi its constant uniformizer.
Use Q_n=[R --pi^(n+1)--> R] in degrees -1 and zero. The maps (pi,id) give a
strict coefficient tower Q. Its augmentation to the actual finite quotient is
a quasi-isomorphism: pi is regular on the completed coefficient sheaf and its
cokernel is the specified quotient. Choose a K-flat representative A of K and
a K-injective representative I of Q(G). Tensoring with the bounded free Q_n
computes derived reduction of any complex. In particular Hom(A,I) tensor Q_n
computes reduction of Hom(K,Q(G)); transport along e and the canonical
K-flat computation for q' gives the second displayed tower isomorphism.
For the first, I tensor Q_n is K-injective: it is a finite cone of shifts of
I, and Hom from any acyclic complex into that cone is acyclic. Thus
Hom(A,I tensor Q_n) represents Hom(K,Res_n(F_n Q(G))). Compute the latter
reductions on q. These identifications are natural for the actual quotient
maps because (pi,id) lifts the quotient transition. Their augmentations and
resolution comparisons commute on pure tensors, by the derived scalar
extension counit and resolution independence. If a strict tensor calculation
requires flat terms, first use flat-term K-flat refinements of q and q', then
transport back by the canonical resolution-independent tower comparison. They assemble into
isomorphisms of towers. The two computations do not use the signed exchange
map, its invertibility, products or completeness. All powers are positive,
including n=0; zero inputs and the empty scheme are allowed. -/
theorem reductionTower_tensor_models
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
      Nonempty (integralReductionTower l E Y D hl P ⋙ H ≅
        Q ⋙ (totalTensor.{t, u} Y R).obj I ⋙
          (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
            (R := R)).obj (op A) ⋙ DerivedCategory.Q) ∧
      Nonempty (integralReductionTower l E Y D hl P' ≅
        Q ⋙ (totalTensor.{t, u} Y R).obj
          (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I) ⋙
            DerivedCategory.Q) := by sorry

end WeilConjectures.IntegralHom
