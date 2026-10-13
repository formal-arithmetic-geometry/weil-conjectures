/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.EtaleCERowOrdinaryComparison
public import Sheaf.Paper.EtaleCECanonicalRowComparison
public import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology

/-! # Prescribed normalized CE presentations

Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-normalized-row-presentations).
-/

@[expose] public section

universe uNatural
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborate the dependent CE and normalized page data together.
/-- Construct normalized presentations and pin their first-page comparison to the
concrete signed row comparison. No scheme-map naturality is asserted here.
Source: Stacks Project, Tags 015J, 015K, 012K and 06XR.
(blueprint: lem-weil-pbc-ce-normalized-row-presentations).

Proof. Apply exists_hypercohomology_firstPage to each prescribed augmented bicomplex,
retaining I, a, the second filtration and the pinned total augmentation. Use the
canonical K-injective resolution of K and compose the total-homology comparison with
resolutionEtaleCohomologyIso; transport the finite homology-image filtration by this
composite. Build every positive page from filteredComplex_page_differential_exists_unique
and every successor comparison from filteredComplex_normalized_homology. Adjoin the
page-zero graded complex via filteredComplex_graded_homology. Its negative row terms
vanish by extension by zero. The canonical rowComparison identifies the first page
with row homology. Multiply it by (-1)^(pq), and compose with the inverse of the
row resolution isoRightDerivedObj to define eDerived. Define ordinaryComparison as
isoRightDerivedObj followed by ceRowOrdinaryIso. Their intermediate maps cancel,
giving the displayed equation. The signed d1 equation and right-derived naturality
give dDerived; the explicit Ext/sections comparison is natural for coefficient maps,
giving ordinary_naturality. Assemble these witnesses as EtaleTermwiseHypercohomology.
Every positive page is the concrete boundary cokernel, so j is the identity comparison
and successor normalization holds. The construction works at p=0, for zero rows,
negative complex degrees and empty diagonals using the same quotient universal
properties. -/
theorem exists_etaleCE_normalized_row_presentations
    (I : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      HomologicalComplex₂ (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
        (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      ((CochainComplex.single₀
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
         (ComplexShape.up ℤ)).obj K.obj ⟶ I X K)
    (hbelow : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero ((I X K).X s))
    (hrows : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ), QuasiIso ((a X K).f s))
    (hterms : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ) (r : ℕ), Injective (((I X K).X s).X r))
    (hhorizontal : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ) (r : ℕ),
      Injective (((I X K).cycles s).X r) ∧
      Injective ((image ((I X K).d (s - 1) s)).X r) ∧
      Injective (((I X K).homology s).X r))
    (hquasi : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ),
      QuasiIso (HomologicalComplex.cyclesMap (a X K) s) ∧
      QuasiIso (image.map (Arrow.homMk' ((a X K).f (s - 1)) ((a X K).f s)
        ((a X K).comm (s - 1) s))) ∧
      QuasiIso (HomologicalComplex.homologyMap (a X K) s)) :
    ∃ (P : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (δ : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (r : ℤ) (hr : 1 ≤ r),
        FilteredComplexPageDifferential (P X K).sectionsTotal (P X K).L r)
      (j : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (r : ℤ) (hr : 1 ≤ r), (P X K).sequence.page r hr ≅ (δ X K r hr).page),
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        (P X K).I = I X K) ∧
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ),
        FilteredComplexHomologyNormalized (P X K).sectionsTotal (P X K).L r (δ X K r hr) pq
          ((HomologicalComplex.homologyFunctor AddCommGrpCat.{uNatural + 1}
            (ComplexShape.up' (r, 1 - r)) pq).mapIso (j X K r hr).symm ≪≫
            (P X K).sequence.iso r (r + 1) pq rfl hr ≪≫
            (HomologicalComplex.eval AddCommGrpCat.{uNatural + 1}
              (ComplexShape.up' (r + 1, 1 - (r + 1))) pq).mapIso
                (j X K (r + 1) (by omega)))) ∧
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (p : ℕ) (q : ℤ),
        (j X K 1 (by omega)).inv.f (q, (p : ℤ)) ≫ ((P X K).firstPageIso p q).hom =
          ((P X K).signedRowComparison p q).hom ≫
            (ceRowOrdinaryIso X (K.obj.X q) (cePresentationRow (P X K) q) p).hom) := by sorry

end AlgebraicGeometry.Etale
