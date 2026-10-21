/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.ExternalRHomConePairing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose
import WeilConjectures.AlgebraicGeometry.ConstantPullbackCompositionCoherence
import Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Naturality and open restriction of external evaluation

Source: Stacks Project, Cohomology on Sites, Tags 08J9 and 08JB; blueprint
main-20261015, lem-pur-kunneth-supported, proof paragraphs 1 and 3
(blueprint: lem-pur-external-evaluation-transpose-natural).

The existing ExternalRHom definitions give the specified global Hom, evaluation,
constant/pullback comparisons, signed external transpose and restriction maps.
This statement applies to arbitrary unbounded objects.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale.ExternalRHom

/-- The global tensor--Hom bijection, its evaluation normalization, four-variable
naturality of the external evaluation transpose, and both open-restriction squares.

Source: Stacks Project, Cohomology on Sites, Tags 08J9, 08JB, 07A6 and 07A4;
blueprint main-20261015, lem-pur-kunneth-supported, proof paragraphs 1 and 3
(blueprint: lem-pur-external-evaluation-transpose-natural).

Proof:
1. Compose constant/sections adjunction (def-kun-constant-projection-morphism)
   with the closed tensor--Hom adjunction
   (lem-sf-ringed-derived-closed-symmetric-monoidal). Untransposition is
   constant realization followed by evaluation. The identity therefore gives evaluation.
2. Naturality of those adjunctions says that evaluation intertwines a contravariant
   source map and a covariant target map.
3. Form the external composite from the canonical constant-pullback comparisons
   (def-pur-derived-constant-pullback-comparison), the exact pullback tensor comparisons
   (prop-weil-pbc-inverse-image-modules-exact and lem-pur-exact-pullback-signed-comparison),
   and the signed middle interchange. Its sign on degrees s,q is (-1)^(s*q).
   Transpose this composite; this is the existing pairing, without resolution choices.
4. Tensor the evaluation naturality equations. Naturality of every comparison and of
   the signed interchange identifies the two untransposes of the claimed naturality
   square. Injectivity of the composed adjunction gives equality.
5. Identify inverse image along an open with slice restriction using
   lem-weil-pbc-etale-inverse-image-restriction. The sections restriction is the adjunct
   of the pulled-back constant/sections counit, using the canonical constant comparison.
6. Compose that counit identity with the internal evaluation restriction equation
   (lem-weil-pbc-ringed-slice-evaluation-transpose). Thus global evaluation restricts,
   and transposing after restriction equals restricting the transpose.
7. The constant comparisons respect composition: apply
   lem-weil-pbc-constant-pullback-composition-coherence termwise to coefficient complexes
   and localize (def-pur-derived-constant-pullback-comparison).
8. The pullback-composition comparisons respect tensor and the middle interchange
   (lem-kun-derived-pullback-composition-monoidal,
   lem-pur-exact-pullback-signed-comparison and lem-pur-cochain-pullback-tensor-coherence).
   Consequently the external comparison itself restricts to the external comparison.
9. The base change of an open is open (lem-weil-pbc-open-immersion-base-change).
   Tensor the restricted first evaluation with the unchanged second evaluation and
   use step 8. Step 6 and injectivity of transposition prove the X restriction square.
   Restrict the second evaluation instead for Y. These arguments use arbitrary
   unbounded objects throughout and impose no flatness condition. -/
theorem external_evaluation_transpose_natural (A : Type (u + 1)) [CommRing A] :
    (∀ (T : Scheme.{u}) (G M : DerivedCategoryModule A T)
      (Q : DerivedCategory (ModuleCat.{u + 1} A)),
      Function.Bijective (fun f : Q ⟶ ((globalHom A T).obj (op G)).obj M ↦
        ((constant A T).map f ▷ G) ≫ evaluation A G M)) ∧
    (∀ (T : Scheme.{u}) (G M : DerivedCategoryModule A T),
      transpose A G M (((globalHom A T).obj (op G)).obj M) (evaluation A G M) = 𝟙 _) ∧
    (∀ (X Y P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
      (E E' K K' : DerivedCategoryModule A X)
      (H H' L L' : DerivedCategoryModule A Y)
      (f : E' ⟶ E) (g : H' ⟶ H) (s : K ⟶ K') (t : L ⟶ L'),
      (homMap A f s ⊗ₘ homMap A g t) ≫ pairing A a b E' K' H' L' =
        pairing A a b E K H L ≫
          homMap A ((pull A a).map f ⊗ₘ (pull A b).map g)
            ((pull A a).map s ⊗ₘ (pull A b).map t)) ∧
    (∀ (X X' Y P P' : Scheme.{u})
      (a : P ⟶ X) (b : P ⟶ Y) (j : X' ⟶ X) (p : P' ⟶ P) (a' : P' ⟶ X')
      [IsOpenImmersion j] (sq : IsPullback p a' a j)
      (E K : DerivedCategoryModule A X) (H L : DerivedCategoryModule A Y),
      RestrictionSquare A a b j (𝟙 Y) p a' (p ≫ b) sq.w (by simp) E K H L) ∧
    (∀ (X Y Y' P P' : Scheme.{u})
      (a : P ⟶ X) (b : P ⟶ Y) (j : Y' ⟶ Y) (p : P' ⟶ P) (b' : P' ⟶ Y')
      [IsOpenImmersion j] (sq : IsPullback p b' b j)
      (E K : DerivedCategoryModule A X) (H L : DerivedCategoryModule A Y),
      RestrictionSquare A a b (𝟙 X) j p (p ≫ a) b' (by simp) sq.w E K H L) := by
  sorry

end AlgebraicGeometry.Etale.ExternalRHom
