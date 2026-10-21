/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedInternalHomFilteredColimitData

/-! # Filtered continuity for the strict internal-Hom roof -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SfbHomFilteredColimit
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]

/-- Continuity and exact coefficient tensor give the colimit-side roof denominator.
Source: Bhatt--Scholze, Lemma 6.8.12 and Remark 6.8.15, steps 2--3 and 8--9 of the
conditional ring-sheaf argument; Stacks Project, Tags 06YN, 08J9 and 079P.
(blueprint: lem-sfb-internal-hom-filtered-continuity).

Proof: sheaf tensor preserves colimits. At each finite-free stage it is a finite sum of
the identity, hence exact; exact filtered colimits show tensor by the colimit coefficient
is exact as well. This proves that tensoring the augmentation of L is a quasi-isomorphism,
and functorial derived Hom preserves it, giving the roof denominator. For the comparison
post map, use a good lower truncation of L with the supplied common lower bound. Exact
stage tensor preserves that bound, so the continuity hypothesis identifies the filtered
colimit of their derived Hom representatives with derived Hom of their colimit. The
augmentation L to its K-injective replacement induces quasi-isomorphisms both at the
stages and at the colimit. Exact filtered colimits preserve those quasi-isomorphisms;
the natural augmentation square and two-out-of-three therefore transport continuity
from L to its possibly unbounded K-injective replacement. Tensor preservation supplies
the last colimit isomorphism. The proof never assumes that the replacement itself has
a lower bound or that Hom(P,I(L)) is bounded. -/
theorem internalHom_filtered_continuity (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (Modules.{u, v, r} J R)]
    [HasExactColimitsOfShape I (Modules.{u, v, r} J R)]
    (T : I ⥤ Modules.{u, v, r} J R)
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty
      (T.obj i ≅ limit (Discrete.functor (fun _ : Fin d ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hcont : Continuous.{u, v, r} J R (I := I) P)
    (b : ℤ) (hL : ∀ n : ℤ, n < b → IsZero (L.X n)) :
    QuasiIso (roofDenominator.{u, v, r} J R P L (colimit T)) ∧
    QuasiIso (colimit.post T
      (tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
        homFixed.{u, v, r} J R P)) ∧
    IsIso (colimit.post T
      (tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L))) := by
  sorry

end WeilConjectures.SfbHomFilteredColimit
