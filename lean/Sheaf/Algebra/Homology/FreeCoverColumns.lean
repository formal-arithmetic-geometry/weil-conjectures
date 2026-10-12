/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

import Sheaf.Algebra.Homology.FreeComplexCover

/-!
# Successive free-cover columns

Source: Stacks Project, Tag 09KP, the kernel iteration before totalization.
(blueprint: lem-pc-derived-free-cover-columns)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The kernel iteration produces an augmented bicomplex exact on terms and cycles.
Source: Stacks Project, Differential Graded Algebra, Tag 09KP, proof, the successive
short exact sequences before totalization, using Tag 09KN.
(blueprint: lem-pc-derived-free-cover-columns)

Proof. Set `N₀ = M`. Apply `exists_freeComplexCover` to `Nᵢ`, retaining its
short complex `Sᵢ`, map `bᵢ : Sᵢ.X₂ ⟶ Nᵢ`, degreewise and cycle surjectivity,
and split two-step sequence. Put `Pᵢ = Sᵢ.X₂` and take `Nᵢ₊₁ = kernel bᵢ`.
Use `bᵢ₊₁` followed by the kernel inclusion as the map `Pᵢ₊₁ ⟶ Pᵢ`.
Its composite with `bᵢ` is zero. The kernel inclusion is degreewise injective;
the evaluation functors preserve kernels. Degreewise surjectivity of `bᵢ₊₁`
therefore gives exactness at `Pᵢ`. The same argument at `P₀` gives exactness
before the augmentation `b₀`, which is degreewise surjective.

For exactness on cycles, take a cycle in the kernel of the outgoing map. Its
unique lift to the kernel complex is a cycle: apply the injective kernel
inclusion to its differential and use commutation with the differential.
The cycle-surjectivity clause for `bᵢ₊₁` lifts that kernel cycle to a cycle
in `Pᵢ₊₁`. This proves equality of image and kernel on cycles; the other
inclusion follows from the zero composite. The cover of `M` also supplies
surjectivity on cycles at the augmentation.

Place `Pᵢ` at horizontal degree `-i`, set positive columns to the zero complex,
and use the constructed maps for consecutive nonpositive columns and zero
elsewhere. The zero composites give the horizontal complex identities, and
commutation with vertical differentials holds because all maps are cochain maps.
Take `a = b₀`. For each nonpositive column retain `Sᵢ` with its identity
identification of the middle object, its short exactness, all evaluation
splittings, and its two decompositions into coproducts of single copies of `A`.
This construction also works for the zero ring and the zero complex; no
boundedness, finite generation, or nonzero-ring hypothesis is used.
-/
theorem exists_freeCoverColumns {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      ∃ a : K.X 0 ⟶ M,
        (∀ p : ℤ, 0 < p → IsZero (K.X p)) ∧
        (∀ (p q : ℤ), p < -1 →
          Function.Exact ((K.d p (p + 1)).f q).hom ((K.d (p + 1) (p + 2)).f q).hom) ∧
        (∀ q : ℤ, Function.Exact ((K.d (-1) 0).f q).hom (a.f q).hom) ∧
        (∀ q : ℤ, Function.Surjective (a.f q).hom) ∧
        (∀ (p q : ℤ), p < -1 →
          Function.Exact (HomologicalComplex.cyclesMap (K.d p (p + 1)) q).hom
            (HomologicalComplex.cyclesMap (K.d (p + 1) (p + 2)) q).hom) ∧
        (∀ q : ℤ, Function.Exact (HomologicalComplex.cyclesMap (K.d (-1) 0) q).hom
          (HomologicalComplex.cyclesMap a q).hom) ∧
        (∀ q : ℤ, Function.Surjective (HomologicalComplex.cyclesMap a q).hom) ∧
        (∀ p : ℤ, p ≤ 0 →
      ∃ S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ),
        Nonempty (S.X₂ ≅ K.X p) ∧ S.ShortExact ∧
        (∀ k : ℤ,
          Nonempty
            (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)).Splitting) ∧
        ∃ (I₁ I₃ : Type u) (d₁ : I₁ → ℤ) (d₃ : I₃ → ℤ),
          Nonempty (S.X₁ ≅ ∐ (fun i : I₁ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₁ i)).obj
              (ModuleCat.of A A))) ∧
          Nonempty (S.X₃ ≅ ∐ (fun i : I₃ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₃ i)).obj
              (ModuleCat.of A A)))) := by sorry

end CochainComplex
