/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisAdicDataFromFinite
import WeilConjectures.AlgebraicGeometry.GaloisAdicAlgebraicAbelian
import WeilConjectures.AlgebraicGeometry.GaloisAdicAlgebraicMonoidal
import WeilConjectures.AlgebraicGeometry.GaloisAdicAlgebraicScalar
import Mathlib.CategoryTheory.Abelian.Transfer
import WeilConjectures.CategoryTheory.PrescribedMonoidal

/-! # Algebraic and coefficient clauses of the adic correspondence -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped MonoidalCategory

namespace AlgebraicGeometry.Scheme

section Consequences

variable
    {Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q)

private theorem algebraicSheavesAbelian_of_representations
    (h : galoisAlgebraicRepresentationsAbelian y G c l Q d) :
    galoisAlgebraicSheavesAbelian y G c l Q d := by
  obtain ⟨a⟩ := h
  let : Abelian (galoisAdicRepresentations l Q d.P d.δ) := a
  let : Preadditive (LisseAlgebraicSheaf l Y Q) :=
    .ofFullyFaithful d.eA.fullyFaithfulFunctor
  let : HasFiniteProducts (LisseAlgebraicSheaf l Y Q) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence d.eA.functor⟩
  exact ⟨abelianOfEquivalence d.eA.functor⟩

private theorem algebraicMonoidal_of_comparisons
    (hT : galoisAlgebraicTensor y G c l Q d)
    (hU : galoisAlgebraicUnit y G c l Q d) :
    galoisAlgebraicMonoidal y G c l Q d := by
  classical
  choose e he using hT
  let T := d.eA.functor ⋙ ObjectProperty.ι _
  apply Monoidal.nonempty_prescribedMonoidal T (Functor.FullyFaithful.ofFullyFaithful T)
    (lisseAlgebraicTensor l Y Q) (lisseAlgebraicUnit l Y Q)
  · intro F H
    exact Rep.mkIso
      { toLinearEquiv := e F H
        isIntertwining' := fun g ↦ LinearMap.ext (fun z ↦ he F H g z) }
  · exact hU.some.symm

end Consequences

/-- The finite coefficient localization of data with normalized construction comparisons
satisfies the remaining algebraic, scalar-extension, and monoidal clauses.
Source: Deligne, Weil II (1.1.1), (1.1.6), and Stanford Weil II seminar L19,
Proposition 1.1.9, proof steps 8--10.
(blueprint: new-c5-galois-adic-algebraic-properties).

Compress finite coefficient matrices through a subspace retraction or quotient section,
adjoining their finitely many entries to the coefficient field. Product actions use
block-diagonal matrices over the compositum. This gives an abelian full subcategory of
representations; transport this structure across eA. The finite balanced
scalar maps commute with c.γ on germs. Use `hcanon.inverseLimit` to reconstruct their
integral fibre comparisons with the prescribed generator formula, then use
`hcanon.localization` to rationalize. Compute the algebraic tensor at the compositum of
its two finite coefficient models. The normalized `hcanon.colimit` comparisons transfer
the tensor and unit maps to Q. Full faithfulness lifts the tensor maps, associators and
unitors from Rep; Monoidal.induced supplies the coherence laws with the prescribed
tensor objects and unit. The algebraic model scalar formula
and preservation of finite limits and colimits are proved in the parent. -/
theorem galois_adic_algebraic_properties
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q)
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisAlgebraicSheavesAbelian y G c l Q d ∧
    galoisAlgebraicRepresentationsAbelian y G c l Q d ∧
    galoisAlgebraicMonoidal y G c l Q d ∧
    galoisAlgebraicTensor y G c l Q d ∧
    galoisAlgebraicUnit y G c l Q d ∧
    galoisIntegralScalarExtension y G c l Q d ∧
    galoisRationalScalarExtension y G c l Q d := by
  have hAR := galois_adic_algebraic_abelian y G c l Q d
  have hAS := algebraicSheavesAbelian_of_representations y G c l Q d hAR
  obtain ⟨hAT, hAU⟩ := galois_adic_algebraic_tensor_unit y G c l Q d hcanon
  have hAM := algebraicMonoidal_of_comparisons y G c l Q d hAT hAU
  obtain ⟨hIS, hRS⟩ := galois_adic_algebraic_scalar y G c l Q d hcanon
  exact ⟨hAS, hAR, hAM, hAT, hAU, hIS, hRS⟩

end AlgebraicGeometry.Scheme
