/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleQcqsSubsite
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Site axioms and limits for the qcqs pro-etale subsite

Source: Stacks Project, Tags 09A1 and 098M
(blueprint: lem-weil-pbc-proetale-qcqs-site-limits).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEt

/-- The qcqs full subcategory is a site for finite pro-etale covers; fibre products,
slice finite limits, and (for qcqs base) finite limits are computed in schemes.
Adjoining finitely many arrows to a cover preserves the covering property.
Source: Stacks Project, Tag 09A1, qcqs subsite paragraph, and Tag 098M.
(blueprint: lem-weil-pbc-proetale-qcqs-site-limits)

Proof plan:
1. Every map between objects is weakly etale (`lem-trf-weakly-etale-between-objects`).
   Weakly etale maps are stable under base change and composition
   (`lem-weil-pbc-weakly-etale-composition-base-change`). A map from a qcqs scheme
   to a qcqs scheme is qcqs, and these properties persist under base change and
   composition (`lem-weil-pbc-qcqs-morphism-permanence`). Thus scheme fibre products
   belong to the full subcategory, and their universal properties restrict to it.
2. Isomorphism covers, finite composites of finite covers, and pullbacks of finite
   covers are covers in the full pro-etale site. Step 1 keeps their sources qcqs.
   This gives a pretopology with exactly the prescribed finite covering presieves,
   and inclusion sends covers to covers. Use the pretopology axioms: the stronger
   precoverage classes also quantify over infinite presentations of finite presieves.
3. Over a qcqs object T, the identity is terminal. Products come from step 1.
   The equalizer of a,b : U → V is U ×_(V ×_T V) V, using (a,b) and the diagonal.
   These universal properties hold in schemes over T. Products and equalizers
   construct all finite limits, including the empty limit T. If X is qcqs, X/X
   itself is terminal, giving finite limits over X in the same way.
4. Additional arrows are weakly etale by the between-objects lemma. The original
   finite affine-open witnesses for the fpqc condition still cover each affine
   open after adjoining arrows; the enlarged index set remains finite.
-/
theorem qcqs_site_limits (X : Scheme.{u}) :
    ∃ h : HasPullbacks (Qcqs X),
    ∃ J : @Pretopology (Qcqs X) inferInstance h,
    J.toPrecoverage = qcqsPrecoverage X ∧
    PreservesLimitsOfShape WalkingCospan (qcqsInclusion X) ∧
    PreservesLimitsOfShape WalkingCospan
      (qcqsInclusion X ⋙ ProEt.forget X ⋙ Over.forget X) ∧
    (∀ (T : Qcqs X) (R : Presieve T), R ∈ qcqsPrecoverage X T →
      R.map (qcqsInclusion X) ∈ precoverage X ((qcqsInclusion X).obj T)) ∧
    (∀ T : Qcqs X, HasFiniteLimits (Over T) ∧
      PreservesFiniteLimits
        (Over.post (X := T) (qcqsInclusion X ⋙ ProEt.forget X) ⋙
          Over.iteratedSliceForward ((qcqsInclusion X ⋙ ProEt.forget X).obj T))) ∧
    (CompactSpace X → QuasiSeparatedSpace X →
      HasFiniteLimits (Qcqs X) ∧
        PreservesFiniteLimits (qcqsInclusion X ⋙ ProEt.forget X)) ∧
    (∀ (T : Qcqs X) (R S : Presieve T), R ∈ qcqsPrecoverage X T →
      S ∈ Precoverage.finite (Qcqs X) T → R ⊔ S ∈ qcqsPrecoverage X T) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
