/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

/-!
# Spectral sequence of a filtered complex

Source: Stacks Project, Homology, Definition 12.18.1 and Remark 12.18.2,
used in the proof of Lemma 12.19.2 (Tag 012K) (blueprint:
lem-sp-filtered-complex-associated-spectral-sequence-construction).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- (blueprint: lem-sp-filtered-complex-associated-spectral-sequence-construction)
The spectral sequence of a cochain complex `K` with a decreasing filtration `F` by
subcomplexes (a `DecreasingFiltration` of `K` in the abelian category of cochain
complexes): a cohomological spectral sequence starting at page zero, whose page-`r`
differential has bidegree `(r, 1 - r)`, whose page-zero term at `(p, q)` is identified
with `gr^p K^{p+q} = (F.gradedPiece p).X (p + q)`, and whose page-zero differential is,
under these identifications, the differential of the graded complex `gr^p K` induced by `d`;
for `r ≥ 1` its page-`r` term at `(p, q)` is `Z_r / B_r` for the cycle and boundary
subobjects `F.complexCycles p (p + q) r` and `F.complexBoundaries p (p + q) r` of
`gr^p K^{p+q}`, as in Definition 12.18.1.

Source: Stacks Project, Homology, Definition 12.18.1, Remark 12.18.2 and the proof of
Lemma 12.19.2 (Tag 012K).

Proof.
1. Place `F^{p+1}K^{p+1+q}` in bidegree `(p, q)`. Since each `F^{p+1}K` is a subcomplex, `d` maps
   this component to `F^{p+1}K^{p+2+q}`, a differential of bidegree `(0, 1)` with `d^2 = 0`
   inherited from `K` (def-sp-abelian, def-sp-filtration).
2. The inclusions `F^{p+1}K^{p+1+q} ↪ F^pK^{p+1+q}` form a morphism `α : A → A[-1,1]` of
   differential bigraded objects, commuting with `d` because the filtration is by
   subcomplexes, and injective since they are inclusions of subobjects. The self-map
   construction of Definition 12.18.1 and Remark 12.18.2 gives the associated spectral
   sequence (def-sp-spectral-sequence).
3. With the shifts `S = [0,1]` and `T = [1,-1]`, `T^r S = [r, 1-r]`, so the page-`r`
   differential has bidegree `(r, 1 - r)`. Page zero is the cokernel of the shifted
   inclusion, `Coker(F^{p+1}K^{p+q} → F^pK^{p+q}) = gr^p K^{p+q}`, with the differential
   induced by `d`.
4. For `r ≥ 1` the construction of Definition 12.18.1 has `E_r = Z_r / B_r`, where
   `Z_r` is the image in `gr^p K^{p+q}` of `d⁻¹(α^r A)`, i.e. of
   `F^pK^{p+q} ∩ d⁻¹(F^{p+r}K^{p+q+1})`, and `B_r` is the image of `(α^{r-1})⁻¹(dA)`, i.e.
   of `F^pK^{p+q} ∩ d(F^{p-r+1}K^{p+q-1})`; these are `F.complexCycles p (p + q) r` and
   `F.complexBoundaries p (p + q) r` (def-sp-filtered-complex-subquotients), with
   `B_r ⊆ Z_r` as in Stacks.
-/
theorem filteredComplex_associated_spectralSequence
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) :
    ∃ (E : CohomologicalSpectralSequence C 0)
      (e : ∀ p q : ℤ, (E.page 0).X (p, q) ≅ (F.gradedPiece p).X (p + q)),
      (∀ p q : ℤ, (E.page 0).d (p, q) (p, q + 1) ≫ (e p (q + 1)).hom =
        (e p q).hom ≫ (F.gradedPiece p).d (p + q) (p + (q + 1))) ∧
      ∀ (p q r : ℤ) (hr : 1 ≤ r),
        ∃ hBZ : F.complexBoundaries p (p + q) r ≤ F.complexCycles p (p + q) r,
          Nonempty ((E.page r).X (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ)) := by
  sorry

end CategoryTheory
