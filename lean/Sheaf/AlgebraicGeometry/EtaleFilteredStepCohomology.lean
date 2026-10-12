/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.Paper.EtaleTermwiseHypercohomology
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Sheaf.CategoryTheory.CartanEilenbergTotalResolution
import Sheaf.CategoryTheory.CartanEilenbergMappedTotal
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple
import Sheaf.CategoryTheory.KInjectiveComputes

/-! # Computing one filtered Cartan--Eilenberg step

Source: Stacks Project, Tags 015J and 0133, applied to the columns in degrees at least q.
(blueprint: lem-weil-pbc-etale-filtered-step-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The cohomology of one filtered total step computes derived global sections of
one fixed stupid truncation, compatibly with its inclusion in the full complex.
Source: Stacks Project, Tag 015J, proof remark (3), and Tag 0133.

Proof: Restrict the augmented bicomplex to complex degrees s >= q and extend by zero.
Its rows remain injective resolutions of the corresponding terms of the stupid
truncation; the other rows are zero. The row augmentations commute with the complex
differential, so their degree-zero summand maps assemble into an augmentation of
K.stupidTrunc(embeddingUpIntGE q) into the restricted total. In total degree n its
only possibly nonzero summands have resolution degree r >= 0 and complex degree
s >= q with r+s=n. There are finitely many, and none when n<q. The total therefore
has injective terms and is bounded below, hence is K-injective. The exact augmented
rows and the finite diagonal filtration give an acyclic augmentation cone (0133),
so this augmentation is a quasi-isomorphism. Apply global sections termwise. Its
restricted total identifies with (T.L.step q): T.filtration_formula identifies the
subobjects degreewise, and their canonical inclusions commute with differentials.
This gives the displayed cohomology isomorphism by the K-injective computation of
RΓ. The inclusion of the restricted resolution into the full total, followed by
T.comparison, is a resolution comparison for the stupid-truncation inclusion:
T.aug_formula fixes the augmentation, and T.over_K makes its composite agree with
T.ρ.map up to homotopy. Naturality of the K-injective derived-functor computation
and T.w_formula then identify the induced map with the map of the truncation
inclusion. Finally T.c_formula fixes the full-total identification, giving the
stated commutative equation. Empty diagonals, the zero complex and negative q
satisfy the same finite-diagonal calculation; no positivity of q is required.
(blueprint: lem-weil-pbc-etale-filtered-step-cohomology-iso). -/
theorem etale_filtered_step_cohomology_iso
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p q : ℤ) :
    Nonempty (((T.L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).homology p) ≅
        (cohomology AddCommGrpCat.{u + 1} X p).obj
          (DerivedCategory.Q.obj (K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE q)))) := by
  sorry

/-- Compatibility of the canonical filtered-step isomorphism with truncation inclusion.
Source: Stacks Project, Tags 015J and 0133; restricted augmented-total comparison.

Proof: Use the restricted augmented Cartan--Eilenberg total from
`etale_filtered_step_cohomology_iso`. The diagonal description of the mapped total
identifies its inclusion into the full mapped total with `(T.L.step q).arrow`.
The augmentation comparison agrees with the truncation inclusion on degree-zero
summands by `T.aug_formula` and `T.over_K`; the K-injective comparison principle
therefore identifies the induced map with the derived map of
`K.obj.ιStupidTrunc`. Applying global sections, homology, and the identifications
`T.w_formula` and `T.c_formula` gives the displayed equality. The argument is
degreewise and also covers empty diagonals, zero terms, and arbitrary integers p,q.
(blueprint: lem-weil-pbc-etale-filtered-step-cohomology-compatibility). -/
theorem etale_filtered_step_cohomology_compatibility
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p q : ℤ) :
    HomologicalComplex.homologyMap (T.L.step q).arrow p ≫ (T.c p).hom =
      (Classical.choice (etale_filtered_step_cohomology_iso X K T p q)).hom ≫
        (cohomology AddCommGrpCat.{u + 1} X p).map
          (DerivedCategory.Q.map (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q))) := by
  sorry

theorem etale_filtered_step_cohomology
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p q : ℤ) :
    ∃ e : ((T.L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).homology p) ≅
        (cohomology AddCommGrpCat.{u + 1} X p).obj
          (DerivedCategory.Q.obj (K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE q))),
      HomologicalComplex.homologyMap (T.L.step q).arrow p ≫ (T.c p).hom =
        e.hom ≫ (cohomology AddCommGrpCat.{u + 1} X p).map
          (DerivedCategory.Q.map (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q))) := by
  let e := Classical.choice (etale_filtered_step_cohomology_iso X K T p q)
  refine ⟨e, ?_⟩
  exact etale_filtered_step_cohomology_compatibility X K T p q


end AlgebraicGeometry.Etale
