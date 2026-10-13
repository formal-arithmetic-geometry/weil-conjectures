/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergConeGradedNormalizedIso

/-! # Differential compatibility for the normalized column comparison

Source: Stacks Project, Homology, Tag 0133, canonical augmentation, and Tag 012X,
column filtration of a total complex. This is the augmented-cone refinement used
in the parent node's second proof step.
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- Normalized retained-column maps commute with one adjacent differential.
Source: Stacks Project, Tags 012X and 0133; parent comparison, step 3.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-normalized-differential).

Proof: precompose the asserted equality with the two inclusions of the column
cone. In negative resolution degrees both sources are zero, except for K in
cone degree -1. For an I term use the normalization lift in degree m. The
filtration arrow is monic and commutes with the cone differential, so its lift
has the same differential as its ambient diagonal inclusion. The horizontal
differential raises the complex index to p+1 and factors through step p+1;
its graded image is zero. The resolution differential preserves index p and
has coefficient one in the flipped total, and its lift in degree m+1 is the
one in the I normalization equation. On K in degree p-1, the -d_K term
raises index and vanishes in the quotient. The augmentation term is, by haug,
the resolution-zero column inclusion of (a.f p).f 0; normalization in degree p
identifies it with the off-diagonal column-cone differential. Extension by zero
kills all other components. Equality on the cone's jointly epic biproduct
inclusions proves the equality. This uses the specified lifts, never arbitrary
object isomorphisms. -/
theorem cartanEilenberg_cone_graded_normalized_differential
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m m' : ℤ) (hmm' : m + 1 = m')
    (e : (F.gradedPiece p).X m ≅ (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p))
    (e' : (F.gradedPiece p).X m' ≅ (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m' - p))
    (he : CartanEilenbergConeGradedNormalized K I a aug F p m e)
    (he' : CartanEilenbergConeGradedNormalized K I a aug F p m' e') :
    e.inv ≫ (F.gradedPiece p).d m m' =
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).d
        (m - p) (m' - p) ≫ e'.inv := by sorry

end CategoryTheory.Functor
