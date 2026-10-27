/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Injective Hom double cohomology

Source: Stacks Project, Injectives, Tag 0G20, remark-spectral-sequences-ext-variant;
Homology, Tags 0130 and 0135; Derived Categories, Tag 06XR.
(blueprint: lem-trf-injective-hom-double-cohomology).

The first quadrant is encoded by natural indices, equivalently extension by zero
outside the quadrant. The term isomorphisms and differential equations specify the
Hom bicomplex. The restriction equation characterizes the vertical comparison, and
the `extMk` equation characterizes the induced iterated comparison on cocycles.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

/-- The commuting Hom bicomplex into any injective resolution has vertical cohomology
Hom of source cohomology, and iterated cohomology equal to derived Ext, canonically
and linearly. The scalar action on Ext is Mathlib's postcomposition action
(`Abelian.Ext.smul_eq_comp_mk₀`). The last equation makes this normalization explicit.

Source: Stacks Project, Tag 0G20, remark-spectral-sequences-ext-variant; Homology,
Tags 0130 and 0135; Derived Categories, Tag 06XR.
(blueprint: lem-trf-injective-hom-double-cohomology).

Proof:
1. Form the displayed Hom modules. Postcomposition squares to zero, as does signed
   precomposition; the mixed composites commute since they have the same sign
   (def-sp-double-complex-total). At b=0 the missing incoming term is zero because
   M^(u+1)=0.
2. Put a=u-b, Z=ker(d_M^a), B=im(d_M^(a-1)). A vertical cocycle kills B. Restrict
   it to Z and descend to Z/B (def-weil-derived-category-cohomology-functor).
   Boundaries restrict to zero. This procedure preserves sums and scalars.
3. Any Z/B -> I^i extends along Z/B -> M^a/B by injectivity of I^i
   (def-sp-injective-resolutions), proving surjectivity, also for b=0.
4. A cocycle vanishing on Z factors through im(d_M^a). For b>0 extend that map
   to M^(a+1) by injectivity and multiply by (-1)^(b-u) to obtain a preimage
   under the vertical differential. For b=0, Z=M^u and the cocycle is itself zero.
5. Restriction and descent commute with postcomposition: both sides take [z] to
   d_I(f(z)). Thus the vertical comparisons identify the horizontal complexes and
   induce isomorphisms on their cohomology (def-sp-double-complex-total).
6. Use lem-weil-pbc-ext-via-injective-resolution, namely
   InjectiveResolution.extAddEquivCohomologyClass and extMk, to identify the latter
   cohomology with derived Ext. The cocycle h maps to Q(epsilon[i])^(-1) Q(h).
   This includes i=0, with no incoming boundaries.
7. Scalar multiplication on I commutes with the augmentation epsilon, so after
   inverting Q(epsilon) it becomes postcomposition by the scalar on N. The Ext
   comparison is therefore A-linear for the action of def-pc-ext. No finite
   injective dimension, Noetherian or finite-generation assumption is used. -/
theorem exists_injectiveHom_double_cohomology
    (A : Type u) [CommRing A] [HasExt.{w} (ModuleCat.{v} A)]
    (M : CochainComplex (ModuleCat.{v} A) ℤ) (u₀ : ℤ)
    (hM : ∀ a : ℤ, u₀ < a → IsZero (M.X a))
    (N : ModuleCat.{v} A) (I : InjectiveResolution N) :
    ∃ D : HomologicalComplex₂ (ModuleCat.{v} A) (ComplexShape.up ℕ) (ComplexShape.up ℕ),
    ∃ e : ∀ i b : ℕ,
      (D.X i).X b ≅ ModuleCat.of A (M.X (u₀ - (b : ℤ)) ⟶ I.cocomplex.X i),
    ∃ r : ∀ i b : ℕ,
      (D.X i).homology b ≅ ModuleCat.of A (M.homology (u₀ - (b : ℤ)) ⟶ I.cocomplex.X i),
    ∃ t : ∀ b i : ℕ,
      (((HomologicalComplex.homologyFunctor (ModuleCat.{v} A)
        (ComplexShape.up ℕ) b).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology i ≃ₗ[A]
          Abelian.Ext (M.homology (u₀ - (b : ℤ))) N i,
      (∀ (i b : ℕ) (f : (D.X i).X b),
        (e (i + 1) b).hom ((D.d i (i + 1)).f b f) =
          (e i b).hom f ≫ I.cocomplex.d i (i + 1)) ∧
      (∀ (i b : ℕ) (f : (D.X i).X b),
        (e i (b + 1)).hom ((D.X i).d b (b + 1) f) =
          ((b : ℤ) - u₀ + 1).negOnePow •
            (M.d (u₀ - ((b + 1 : ℕ) : ℤ)) (u₀ - (b : ℤ)) ≫ (e i b).hom f)) ∧
      (∀ (i b : ℕ) (z : (D.X i).cycles b) (x : M.cycles (u₀ - (b : ℤ))),
        ((r i b).hom ((D.X i).homologyπ b z))
            (M.homologyπ (u₀ - (b : ℤ)) x) =
          ((e i b).hom ((D.X i).iCycles b z)) (M.iCycles (u₀ - (b : ℤ)) x)) ∧
      (∀ (i b : ℕ) (x : (D.X i).homology b),
        (r (i + 1) b).hom (HomologicalComplex.homologyMap (D.d i (i + 1)) b x) =
          (r i b).hom x ≫ I.cocomplex.d i (i + 1)) ∧
      (∀ (b i : ℕ)
        (z : (((HomologicalComplex.homologyFunctor (ModuleCat.{v} A)
          (ComplexShape.up ℕ) b).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).cycles i)
        (h : M.homology (u₀ - (b : ℤ)) ⟶ I.cocomplex.X i)
        (hh : h ≫ I.cocomplex.d i (i + 1) = 0),
        (r i b).hom ((((HomologicalComplex.homologyFunctor (ModuleCat.{v} A)
          (ComplexShape.up ℕ) b).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).iCycles
            i z) = h →
        t b i ((((HomologicalComplex.homologyFunctor (ModuleCat.{v} A)
          (ComplexShape.up ℕ) b).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homologyπ
            i z) = I.extMk h (i + 1) rfl hh) ∧
      (∀ (b i : ℕ) (c : A)
        (x : (((HomologicalComplex.homologyFunctor (ModuleCat.{v} A)
          (ComplexShape.up ℕ) b).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology i),
        t b i (c • x) = (t b i x).comp (Abelian.Ext.mk₀ (c • 𝟙 N)) (add_zero i)) := by
  sorry

end HomologicalComplex₂
