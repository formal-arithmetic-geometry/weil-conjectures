/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-!
# Unbounded K-flat replacements from functorial flat covers

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-def-sfb-derived-categories/def-sfb-left-derived-functor.proof.md`, first paragraph;
Stacks Project, Tags 06Y4 and 06Y3
(blueprint: lem-sfb-unbounded-kflat-resolution-existence).

Only ordered-integer colimits and countable coproducts are assumed. K-flatness is
measured by the binary direct-sum total tensor from the recorded definition node.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

/-- Every unbounded cochain complex has a two-sided K-flat replacement under the explicit
colimit and functorial-flat-cover hypotheses.
Source: blueprint main-20261015, `def-sfb-left-derived-functor.proof.md`, first paragraph;
Stacks Project, Tags 06Y4 and 06Y3; upstream `Abelian.LeftResolution.kFlat_resolutionFunctor_obj`
(blueprint: lem-sfb-unbounded-kflat-resolution-existence).

Here `ObjectProperty.flat` means exactness of both tensor functors. For additive functors
between abelian categories this is equivalent to preservation of short exact sequences.
Likewise `HasExactColimitsOfShape ℤ C` expresses exactness of the colimit functor;
its right exactness is automatic, so preservation of finite limits suffices.
Countable shapes are represented in `Type`: any countable type in a larger universe
is equivalent to its countable small shrink, and colimit preservation is invariant
under this equivalence. The category structure on `ℤ` is its usual order by `≤`.

Proof:
1. The isomorphism-stable class of two-sided flat objects contains every zero object,
   since additive tensor functors preserve zero, and is closed under finite biproducts:
   tensoring with a biproduct is a biproduct of exact tensor functors. Kernels and
   cokernels of the resulting block-diagonal maps are computed componentwise.
   The components of `ε` give epimorphic covers by objects of this class.
2. Apply `lem-sfb-subcategory-truncation-resolution-system` to this class and `K`.
   For each integer `n ≥ 1`, obtain a bounded-above flat-term complex `Eₙ`, a
   quasi-isomorphism `eₙ : Eₙ ⟶ τ≤n K`, and transition maps for which the augmentation
   squares commute as equalities of complex morphisms, not only up to homotopy.
3. Extend the two diagrams by zero for `n < 1`, and form their termwise ordered-`ℤ`
   colimits. The compatible differentials induce a square-zero differential on
   `Q = colim Eₙ`, by the colimit universal property. In each degree `i`, the good
   truncation diagram is constantly `K.X i` with identity transitions once
   `n > max i 0`. Its augmentation is therefore a colimit cocone, naturally in degree.
   This identifies its colimit with `K` and induces the complex morphism `q : Q ⟶ K`.
4. Exactness of ordered-`ℤ` colimits applied to the short exact sequences defining
   cycles, boundaries and their quotient identifies cohomology of a colimit complex
   with the colimit of its cohomology, naturally in complex maps. Each `eₙ` is a
   quasi-isomorphism, including the added zero stages, so every cohomology map of
   `q` is invertible. Thus `q` is a quasi-isomorphism.
5. By `lem-sfb-bounded-above-flat-kflat`, each positive stage `Eₙ` is K-flat.
   The zero stages are K-flat since tensoring with the zero complex gives zero.
6. For a quasi-isomorphism `s : L ⟶ M`, preservation of ordered-`ℤ` colimits by
   tensoring and interchange with the countable total coproduct identify
   `Q ⊗ L` with `colim (Eₙ ⊗ L)` and `L ⊗ Q` with `colim (L ⊗ Eₙ)`.
   In degree `i`, maps from either description are families of maps from
   `Eₙ.X a ⊗ L.X b`, or respectively `L.X a ⊗ Eₙ.X b`, with `a + b = i`,
   compatible in `n`. The two components of the differential are respectively
   `d_E ⊗ 1` and `(-1)^a (1 ⊗ d_L)`, or `d_L ⊗ 1` and `(-1)^a (1 ⊗ d_E)`;
   hence these identifications commute with differentials and the maps induced by `s`.
   The same identifications hold with `M` in place of `L`. Stagewise K-flatness
   makes both tensor maps quasi-isomorphisms, and the cohomology calculation in
   step 4 makes their colimits quasi-isomorphisms. Thus both tensor maps for `Q`
   preserve every quasi-isomorphism, which is `Q.IsKFlatForTotalTensor`. -/
theorem exists_quasiIso_isKFlatForTotalTensor_of_exact_int_colimits
    {C : Type u} [Category.{v} C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C] [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (I : Type) [Countable I] (X : C),
      PreservesColimitsOfShape (Discrete I) (tensorLeft X)]
    [∀ (I : Type) [Countable I] (X : C),
      PreservesColimitsOfShape (Discrete I) (tensorRight X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ (tensorLeft X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ (tensorRight X)]
    (P : C ⥤ C) (hP : ∀ X : C, ObjectProperty.flat (P.obj X))
    (ε : P ⟶ 𝟭 C) [∀ X : C, Epi (ε.app X)] (K : CochainComplex C ℤ) :
    ∃ (Q : CochainComplex C ℤ) (q : Q ⟶ K), Q.IsKFlatForTotalTensor ∧ QuasiIso q := by
  sorry

end CochainComplex
