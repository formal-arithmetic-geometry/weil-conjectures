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
1. Countable coproducts supply the graded binary total tensors. Their preservation
   by both tensor functors supplies the triple and quadruple comparison instances,
   since the indexing sets are subtypes of finite products of integers. Thus the
   monoidal tensor on cochain complexes is available; its two-sided K-flat predicate
   is definitionally `IsKFlatForTotalTensor`.
2. Lift `P` to the full subcategory of flat objects and use `ε` as the augmentation
   of a `LeftResolution`. Flat objects are closed under finite biproducts and retracts.
   Apply `LeftResolution.reduced` to construct a flat resolution whose covering
   functor preserves zero morphisms, without assuming that `P` itself does so.
3. Use the source library's `resolutionFunctor` and `resolutionNatTrans` on `K`.
   They resolve bounded-above truncations by totalizing the termwise resolutions,
   then take the ordered-integer colimit. Exactness of this colimit makes the
   augmentation a quasi-isomorphism (`quasiIso_resolutionNatTrans_app`).
4. The bounded-above flat stages are K-flat by
   `lem-sfb-bounded-above-flat-kflat`. Exact integer colimits preserve K-flatness
   because both tensor functors preserve them. The source theorem
   `LeftResolution.kFlat_resolutionFunctor_obj` applies these facts to the constructed
   resolution. Its K-flatness and the augmentation give the required pair. -/
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
  have (X₁ X₂ X₃ X₄ : GradedObject ℤ C) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by
    intro i j
    infer_instance
  have (X₁ X₂ X₃ : GradedObject ℤ C) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by
    intro i j
    infer_instance
  have (X₁ X₂ X₃ : GradedObject ℤ C) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by
    intro i j
    infer_instance
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) :=
    { F := ObjectProperty.lift _ P hP
      π := ε }
  let Γ := Λ.reduced
  refine ⟨Γ.resolutionFunctor.obj K, Γ.resolutionNatTrans.app K, ?_, ?_⟩
  · exact Γ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K
  · infer_instance

end CochainComplex
