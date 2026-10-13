/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.BifunctorShift

/-! # Tensor inheritance of a localized module comparison

Source: Stacks Project, perfect.tex, Tag 0DJA(1), and More on Algebra, Tag 0BYJ.
(blueprint: lem-pc-localized-tensor-comparison-inheritance).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
noncomputable section


namespace ModuleCat

/-- Extension of a complex from A to C along the displayed tensor-algebra map.
Source: Stacks, 0DJA(1)
(blueprint: lem-pc-localized-tensor-comparison-inheritance). -/
abbrev localizedTensorExtension (R A B C : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C] :=
  (extendScalars ((algebraMap (A ⊗[R] B) C).comp
    (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)

/-- The cohomological comparison followed by a specified map of C-complexes.
Source: Stacks, equation-bc preceding 0DJ8
(blueprint: lem-pc-localized-tensor-comparison-inheritance). -/
abbrev localizedTensorComparison (R A B C : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    {N : CochainComplex (ModuleCat.{u} C) ℤ}
    (L : BaseDerivedTensorCohomologyModel R A B P C)
    (t : (localizedTensorExtension R A B C).obj P ⟶ N) (i : ℤ) :=
  L.localizedComparison i ≫ HomologicalComplex.homologyMap t i

/-- The scalar-extension tensor isomorphism is pinned on every total-complex summand.
This excludes an arbitrary isomorphism between the same complexes.
Source: Stacks, 0BYJ and 0DJA(1)
(blueprint: lem-pc-localized-tensor-comparison-inheritance). -/
def IsLocalizedTensorComparison (R A B C : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    (E P : CochainComplex (ModuleCat.{u} A) ℤ)
    (γ : (localizedTensorExtension R A B C).obj
        (CochainComplex.mapBifunctor E P (curriedTensor _)) ≅
      CochainComplex.mapBifunctor ((localizedTensorExtension R A B C).obj E)
        ((localizedTensorExtension R A B C).obj P) (curriedTensor _)) : Prop :=
  ∀ (p q n : ℤ) (h : p + q = n),
    (extendScalars ((algebraMap (A ⊗[R] B) C).comp
        (algebraMap A (A ⊗[R] B)))).map
        (HomologicalComplex.ιMapBifunctor E P (curriedTensor _) (.up ℤ) p q n h) ≫
      γ.hom.f n =
    (Functor.Monoidal.μIso
      (extendScalars ((algebraMap (A ⊗[R] B) C).comp
        (algebraMap A (A ⊗[R] B)))) (E.X p) (P.X q)).inv ≫
      HomologicalComplex.ιMapBifunctor
        ((localizedTensorExtension R A B C).obj E)
        ((localizedTensorExtension R A B C).obj P) (curriedTensor _) (.up ℤ) p q n h

/-- Flat localization of a mixed-ring comparison is preserved by tensoring an A-K-flat
complex. All models and the map t are arbitrary subject to their canonical equations.

Source: Stacks Project, perfect.tex, 0DJA(1), using More on Algebra, 0BYJ.
(blueprint: lem-pc-localized-tensor-comparison-inheritance).

Proof: fix P, N and t. For a derived A-module E consider, in every degree i,
the canonical map from H^i((E tensor_A^L P) tensor_R^L B) tensor_(A tensor_R B) C
to H^i((E tensor_A^L C) tensor_C^L N). Compute it on K-flat representatives.
The counit equations of the models, and the summand equations for gamma, identify
this map with the displayed composite. Common K-flat resolutions give naturality
in E and independence of its representative and of L and M. These are the
canonical comparisons, not arbitrary maps between the same objects.

Let V be the class of E for which all these maps are isomorphisms. The source
cohomology groups form a cohomological functor: derived tensor preserves triangles,
its connecting maps commute with both coefficient actions, and tensoring the
resulting long exact sequence over A tensor_R B with C stays exact by hflat.
The target groups likewise form a cohomological functor. The comparison commutes
with the connecting maps, as is checked on mapping cones with the canonical
summand formula for gamma. The five lemma therefore makes V closed under third
triangle objects. Both functors and their comparisons commute with direct sums,
since derived tensors and module cohomology do, and scalar extension commutes
with sums; hence V is closed under coproducts. Naturality makes V closed under
retracts. On E = A[n] the comparison is the input comparison shifted by n,
conjugated by the unit, shift and canonical model isomorphisms; thus h puts
every A[n] in V. DerivedModuleFreeGeneration (Stacks 09PB, via the semi-free
filtration and its telescope triangle) now puts every derived A-module in V.
This argument applies to unbounded complexes without a convergence assumption.

Finally use E's given K-flatness to compute its derived tensors by the total
complex in the statement. Extension of E to C is C-K-flat: restriction preserves
acyclicity and tensor adjunction identifies the underlying tensor with E. Thus
the target is computed by the displayed tensor with N. The defining summand
identity of gamma and the universal counit equations for M identify the comparison
with precisely localizedTensorComparison in the conclusion. Take every degree i. -/
theorem localizedTensorComparison_inheritance
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (hflat : Module.Flat (A ⊗[R] B) C)
    (E P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hE : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor E V (curriedTensor _)).Acyclic)
    (hP : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor P V (curriedTensor _)).Acyclic)
    (N : CochainComplex (ModuleCat.{u} C) ℤ)
    (t : (localizedTensorExtension R A B C).obj P ⟶ N)
    (γ : (localizedTensorExtension R A B C).obj
        (CochainComplex.mapBifunctor E P (curriedTensor _)) ≅
      CochainComplex.mapBifunctor ((localizedTensorExtension R A B C).obj E)
        ((localizedTensorExtension R A B C).obj P) (curriedTensor _))
    (hγ : IsLocalizedTensorComparison R A B C E P γ)
    (L : BaseDerivedTensorCohomologyModel R A B P C)
    (M : BaseDerivedTensorCohomologyModel R A B
      (CochainComplex.mapBifunctor E P (curriedTensor _)) C)
    (h : ∀ i : ℤ, IsIso (localizedTensorComparison R A B C L t i)) :
    ∀ i : ℤ, IsIso (localizedTensorComparison R A B C M
      (γ.hom ≫ HomologicalComplex.mapBifunctorMap (𝟙 _) t (curriedTensor _) (.up ℤ)) i) := by
  sorry

end ModuleCat
