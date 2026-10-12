/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps
import Sheaf.Algebra.Homology.RestrictedComplementaryTruncationComparison
import Sheaf.Algebra.Homology.FirstQuadrantVerticalConeFiltration
import Sheaf.CategoryTheory.DegreewiseFilteredAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # The quotient of a smart vertical cutoff

Source: Stacks Project, tag 012X, finite-diagonal comparison; Mathlib's complementary
smart truncations in Algebra/Homology/Embedding/AreComplementary.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Smart lower truncation of a column, with extension and restriction at zero. -/
noncomputable def verticalLower (a : ℤ) : CochainComplex C ℕ ⥤ CochainComplex C ℕ :=
  ComplexShape.embeddingUpNat.extendFunctor C ⋙
    (ComplexShape.embeddingUpIntGE a).truncGEFunctor C ⋙
    ComplexShape.embeddingUpNat.restrictionFunctor C

instance verticalLower_preservesZero (a : ℤ) :
    (verticalLower (C := C) a).PreservesZeroMorphisms := by
  unfold verticalLower
  infer_instance

/-- The projection from a reextended column to its smart lower truncation. -/
noncomputable def verticalLowerπ (a : ℤ) :
    verticalReextension (C := C) ⟶ verticalLower a :=
  Functor.whiskerLeft (ComplexShape.embeddingUpNat.extendFunctor C)
    (Functor.whiskerRight
      ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans C)
      (ComplexShape.embeddingUpNat.restrictionFunctor C))

/-- Complementary smart cutoff inclusion followed by lower projection is zero. -/
lemma verticalCutoffι_lowerπ (a : ℤ) :
    verticalCutoffι (C := C) a ≫ verticalLowerπ a = 0 := by
  apply NatTrans.ext
  funext L
  change HomologicalComplex.restrictionMap
    (CochainComplex.ιTruncLE (L.extend ComplexShape.embeddingUpNat) (a - 1))
      ComplexShape.embeddingUpNat ≫
    HomologicalComplex.restrictionMap
      (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a)
      ComplexShape.embeddingUpNat = 0
  rw [← HomologicalComplex.restrictionMap_comp]
  have h : CochainComplex.ιTruncLE (L.extend ComplexShape.embeddingUpNat) (a - 1) ≫
      CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a = 0 :=
    (ComplexShape.Embedding.embeddingUpInt_areComplementary (a - 1) a (by omega)).hom_ext _
  rw [h]
  ext q
  rfl

variable (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- The cutoff inclusion as a morphism of bicomplexes. -/
noncomputable def verticalCutoffBicomplexι (a : ℤ) :=
  ((verticalCutoffι (C := C) a).mapHomologicalComplex (ComplexShape.up ℕ)).app K

/-- The quotient short complex is constructed using the actual categorical cokernel. -/
noncomputable def verticalQuotientShortComplex (a : ℤ) :
    ShortComplex (HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :=
  ShortComplex.mk (verticalCutoffBicomplexι K a)
    (cokernel.π (verticalCutoffBicomplexι K a)) (cokernel.condition _)

/-- The lower projection descends to the cutoff quotient. -/
noncomputable def verticalQuotientToLower (a : ℤ) :
    (verticalQuotientShortComplex K a).X₃ ⟶
      ((verticalLower a).mapHomologicalComplex (ComplexShape.up ℕ)).obj K :=
  cokernel.desc (verticalCutoffBicomplexι K a)
    (((verticalLowerπ a).mapHomologicalComplex (ComplexShape.up ℕ)).app K) (by
      ext p q
      have h := congrArg (fun η ↦ (η.app (K.X p)).f q)
        (verticalCutoffι_lowerπ (C := C) a)
      exact h)

variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
  L.HasTotal (ComplexShape.up ℕ)]

/-- The actual quotient comparison remains a quasi-isomorphism after totalization.
Source: Mathlib's shortComplexTruncLEX₃ToTruncGE, and Stacks Project tag 012X,
Lemma 12.25.3 (finite-diagonal convergence).
(blueprint: lem-sp-double-complex-vertical-quotient-total-comparison).

Proof: evaluate the cokernel defining verticalQuotientShortComplex at a horizontal
index p. Evaluation preserves cokernels, and restriction to the naturals is exact.
Thus its p-th column is the restriction of the cokernel of the smart cutoff inclusion
of the integer extension of K.X p. The descended map is the restriction of Mathlib's
canonical shortComplexTruncLEX₃ToTruncGE at the complementary bounds a-1 and a.
That canonical map is a quasi-isomorphism. Both source and target vanish in negative
vertical degrees, so restriction loses no homology. The comparison is natural in the
column, hence commutes with horizontal differentials. Form its columnwise integer
mapping cone, retaining degree -1. It has acyclic columns and is bounded below in
both directions. The finite-diagonal filtration of Stacks 012X has zero first page,
so its total is acyclic. Totalization identifies this total with the cone of the total
comparison, with the usual sign on the shifted summand. Hence the total comparison
is a quasi-isomorphism. Extension by zero preserves it. This argument includes a<=0
(where the cutoff is zero), a=1, and all negative total homology degrees. -/
theorem verticalQuotientToLower_total_quasiIso (a : ℤ) :
    QuasiIso (HomologicalComplex.extendMap
      (total.map (verticalQuotientToLower K a) (ComplexShape.up ℕ))
      ComplexShape.embeddingUpNat) := by
  let q := verticalQuotientToLower K a
  obtain ⟨F, hbounds, hneg, hgraded⟩ := firstQuadrant_vertical_cone_filtration q
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).mpr
  apply degreewiseFiltered_acyclic _ F (fun n ↦ ⟨0, n + 2, hbounds n⟩)
  intro p n
  apply ((F.gradedPiece p).exactAt_iff_isZero_homology n).mpr
  by_cases hp : p < 0
  · exact hneg p n hp
  · obtain ⟨e⟩ := hgraded p n (by omega)
    have : QuasiIso (q.f p.toNat) := by
      apply CochainComplex.restrictedComplementaryTruncationComparison_quasiIso
        (K.X p.toNat) a _ ((cokernel.π (verticalCutoffBicomplexι K a)).f p.toNat)
        (by
          exact congrArg (fun f ↦ f.f p.toNat)
            (cokernel.condition (verticalCutoffBicomplexι K a)))
      · exact isColimitOfHasCokernelOfPreservesColimit
          (HomologicalComplex.eval (CochainComplex C ℕ) (ComplexShape.up ℕ) p.toNat)
          (verticalCutoffBicomplexι K a)
      · have h : cokernel.π (verticalCutoffBicomplexι K a) ≫ verticalQuotientToLower K a =
            (((verticalLowerπ a).mapHomologicalComplex (ComplexShape.up ℕ)).app K) :=
          cokernel.π_desc _ _ _
        exact congrArg (fun f ↦ f.f p.toNat) h
    have hcol := (CochainComplex.mappingCone.quasiIso_iff_acyclic
      (HomologicalComplex.extendMap (q.f p.toNat) ComplexShape.embeddingUpNat)).mp
        (inferInstance : QuasiIso _)
    exact e.isZero_iff.mpr (hcol (n - p)).isZero_homology

end HomologicalComplex₂
