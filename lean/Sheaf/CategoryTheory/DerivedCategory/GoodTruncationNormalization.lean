/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Sheaf.CategoryTheory.DerivedDegreeZeroNormalization
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Good-truncation normalization and exact functors

Source: Stacks Project, Homology, Tags 0118 and 010N; Derived Categories,
Tags 06XS and 015F (blueprint: lem-pur-good-truncation-exact-normalization).

The projection is constructed using the cycles-to-homology quotient. The normalization
is selected from the landed uniqueness theorem
`DerivedCategory.existsUnique_iso_single_homology_zero`
(blueprint: lem-amb-derived-degree-zero-normalization), not from an undetermined
existence statement.
The comparisons for exact functors, identities and composition are the existing termwise
localization comparisons. All category and localization universes are independent.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]

/-- The quotient of cycles kills the incoming differential of the good truncation.
Source: Stacks Tag 0118 (blueprint: lem-pur-good-truncation-exact-normalization).
Proof: the degree-zero truncation term is the kernel of d⁰. The incoming differential
is d⁻¹ factored through that kernel, and the homology quotient kills its image.
This is Step 1 of the node's proof; it applies to every complex, without concentration. -/
theorem goodTruncationProjection_condition (A : CochainComplex C ℤ) (i : ℤ)
    (hi : (ComplexShape.up ℤ).Rel i 0) :
    (A.truncLE 0).d i 0 ≫ (A.truncLEXIsoCycles 0).hom ≫ A.homologyπ 0 = 0 := by
  sorry

/-- The specified projection τ≤⁰ A → H⁰(A)[0], with the cycles quotient at zero and
zero components elsewhere. Source: Stacks Tag 0118
(blueprint: lem-pur-good-truncation-exact-normalization). -/
noncomputable def goodTruncationProjection (A : CochainComplex C ℤ) :
    A.truncLE 0 ⟶ (CochainComplex.singleFunctor C 0).obj (A.homology 0) :=
  HomologicalComplex.mkHomToSingle
    ((A.truncLEXIsoCycles 0).hom ≫ A.homologyπ 0)
    (goodTruncationProjection_condition A)

/-- The representative-independent good-truncation normalization ε_K: the unique
isomorphism whose H⁰ map, followed by the single-cohomology comparison, is the identity.
It is selected from the uniqueness theorem `existsUnique_iso_single_homology_zero`
(blueprint: lem-amb-derived-degree-zero-normalization), which fixes the morphism.
Source: Stacks Tags 0118 and 06XS(2)
(blueprint: lem-pur-good-truncation-exact-normalization). -/
noncomputable def goodTruncationNormalization (K : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K)) :
    K ≅ (singleFunctor C 0).obj ((homologyFunctor C 0).obj K) :=
  Classical.choose (existsUnique_iso_single_homology_zero K hK).exists

/-- Both arrows in the specified roof are quasi-isomorphisms, and every representative
isomorphism r gives the same ε_K. The equation is the roof formula multiplied by Q(c_A).
Source: Stacks Tags 0118 and 06XS(2)
(blueprint: lem-pur-good-truncation-exact-normalization).
Proof: Step 1 computes Hⁿ(c_A): it is the identity in retained degrees, and the other
cohomology vanishes by hK and the representative isomorphism. The projection has the
identity quotient map on H⁰ and zero cohomology in other degrees. Both arrows are
quasi-isomorphisms. Localize and transport the roof along r; its action on H⁰ is the
identity. The uniqueness theorem, as in Steps 2--3, identifies it with ε_K, independently
of A and r and of kernel/quotient models under their canonical identifications. -/
theorem goodTruncationNormalization_roof (K : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K))
    (A : CochainComplex C ℤ) (r : Q.obj A ≅ K) :
    QuasiIso (A.ιTruncLE 0) ∧ QuasiIso (goodTruncationProjection A) ∧
      Q.map (A.ιTruncLE 0) ≫ r.hom ≫ (goodTruncationNormalization K hK).hom =
        Q.map (goodTruncationProjection A) ≫
          (singleFunctorIsoCompQ C 0).inv.app (A.homology 0) ≫
          (singleFunctor C 0).map
            ((homologyFunctorFactors C 0).inv.app A ≫ (homologyFunctor C 0).map r.hom) := by
  sorry

/-- Naturality, the H⁰ Hom bijection, and the unique-b characterization for the
specified normalization on the full subcategory with cohomology only in degree zero.
Source: Stacks Tag 06XS(2) (blueprint: lem-pur-good-truncation-exact-normalization).
Proof: Step 2 conjugates by the roofs and uses full faithfulness of the single functor.
Applying H⁰ recovers the unique morphism b. This proves the Hom bijection. In Step 3,
both sides of naturality induce H⁰(a), so injectivity identifies them. Conjugating this
equality and using faithfulness of the single functor proves the equivalence for b.
The inverse family is natural by multiplying by inverses. In the zero category all
Hom sets are singletons and the same argument applies (Step 8). -/
theorem goodTruncationNormalization_naturality_hom
    (K L : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K))
    (hL : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj L)) (a : K ⟶ L) :
    a ≫ (goodTruncationNormalization L hL).hom =
      (goodTruncationNormalization K hK).hom ≫
        (singleFunctor C 0).map ((homologyFunctor C 0).map a) ∧
    Function.Bijective (fun f : K ⟶ L ↦ (homologyFunctor C 0).map f) ∧
    ∀ b : (homologyFunctor C 0).obj K ⟶ (homologyFunctor C 0).obj L,
      (singleFunctor C 0).map b =
        (goodTruncationNormalization K hK).inv ≫ a ≫
          (goodTruncationNormalization L hL).hom ↔ b = (homologyFunctor C 0).map a := by
  sorry

/-- Exact functors preserve the full subcategory with cohomology only in degree zero.
Source: Stacks Tag 015F and Homology Tag 010N
(blueprint: lem-pur-good-truncation-exact-normalization).
Proof (Step 4): lem-weil-pbc-exact-functor-complex-cohomology gives the canonical
kernel/image/quotient comparison on complexes. Descend it using the factorization
and localization universal property (lem-weil-pbc-exact-functor-derived-factorization,
lem-weil-pbc-localization-universal-property). In nonzero degrees its source is zero,
since an exact additive functor preserves zero objects. -/
theorem goodTruncationNormalization_exact_concentrated (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K)) :
    ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor D n).obj (F.mapDerivedCategory.obj K)) := by
  sorry

/-- The roof normalization commutes with the canonical exact-functor comparisons χ and σ;
χ is natural on all derived morphisms in the full subcategory.
Source: Stacks Tags 010N, 0118, 015F
(blueprint: lem-pur-good-truncation-exact-normalization).
Proof: Step 5 constructs F(τ≤⁰A) ≅ τ≤⁰(FA) by the preserved-kernel comparison at zero,
the identity below zero, and the zero comparison above. Kernel uniqueness checks the
chain equation. Its square with c_A commutes. Its square with p_A commutes because
lem-weil-pbc-exact-functor-complex-cohomology respects the quotient projections.
Localize the squares and cancel the truncation comparison to obtain the formula on QC.
Step 4 descends the complex cohomology comparison, giving χ and its naturality.
Step 6 transports the formula along any representative isomorphism, using naturality
of ε, χ and the termwise single comparison σ. This proves the formula for all K. -/
theorem goodTruncationNormalization_exact (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K L : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K))
    (hL : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj L)) (a : K ⟶ L) :
    (goodTruncationNormalization (F.mapDerivedCategory.obj K)
      (goodTruncationNormalization_exact_concentrated F K hK)).hom =
      F.mapDerivedCategory.map (goodTruncationNormalization K hK).hom ≫
        (F.mapDerivedCategorySingleFunctor 0).hom.app ((homologyFunctor C 0).obj K) ≫
        (singleFunctor D 0).map ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.app K) ∧
    (F.mapDerivedCategoryHomologyFunctorIso 0).hom.app K ≫
        (homologyFunctor D 0).map (F.mapDerivedCategory.map a) =
      F.map ((homologyFunctor C 0).map a) ≫
        (F.mapDerivedCategoryHomologyFunctorIso 0).hom.app L := by
  sorry

/-- The comparisons for the identity functor are identities under the canonical derived
identity isomorphism. Source: Stacks Tags 010N and 015F, localization Tag 04VG
(blueprint: lem-pur-good-truncation-exact-normalization).
Proof (Step 7): kernel uniqueness makes the identity kernel comparison the identity;
the quotient epimorphism makes the quotient comparison the identity. The single
comparison is the identity degree by degree. Localization uniqueness descends these
identities with the canonical derived identity comparison. -/
theorem goodTruncationNormalization_identity (K : DerivedCategory C) (B : C) :
    (Functor.mapDerivedCategoryHomologyFunctorIso (𝟭 C) 0).hom.app K ≫
        (homologyFunctor C 0).map ((Functor.mapDerivedCategoryIdIso C).hom.app K) =
      𝟙 ((homologyFunctor C 0).obj K) ∧
    ((𝟭 C).mapDerivedCategorySingleFunctor 0).hom.app B =
      (Functor.mapDerivedCategoryIdIso C).hom.app ((singleFunctor C 0).obj B) := by
  sorry

/-- The cohomology and single-complex comparisons for a composite are the composites of
the comparisons for its two factors, with the canonical termwise derived-composition iso.
Source: Stacks Tag 010N, derived Tag 015F, localization Tag 04VG
(blueprint: lem-pur-good-truncation-exact-normalization).
Proof (Step 7): the composite preserved-kernel comparison and the direct one have the
same composite with the kernel inclusion, hence agree. Image and quotient comparisons
agree by mono and epi cancellation (lem-sp-exact-functor-preserves-homology). Thus χ
and σ compose on complexes. The termwise composition iso descends by localization
uniqueness; the natural-transformation part of lem-weil-pbc-localization-universal-property
descends the comparison equalities. Substitution in the exact compatibility formula
also gives its composite form for ε. No nontriviality is used (Step 8). -/
theorem goodTruncationNormalization_composition (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory C) (B : C) :
    (Functor.mapDerivedCategoryHomologyFunctorIso (F ⋙ G) 0).hom.app K ≫
        (homologyFunctor E 0).map ((Functor.mapDerivedCategoryCompIso F G).hom.app K) =
      G.map ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.app K) ≫
        (G.mapDerivedCategoryHomologyFunctorIso 0).hom.app (F.mapDerivedCategory.obj K) ∧
    (Functor.mapDerivedCategoryCompIso F G).hom.app ((singleFunctor C 0).obj B) ≫
        G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app B) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj B) =
      ((F ⋙ G).mapDerivedCategorySingleFunctor 0).hom.app B := by
  sorry

end DerivedCategory
