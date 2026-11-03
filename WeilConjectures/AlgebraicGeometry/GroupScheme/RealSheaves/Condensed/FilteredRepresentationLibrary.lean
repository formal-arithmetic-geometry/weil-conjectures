/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.CompositionFactors
public import WeilConjectures.RepresentationTheory.ExteriorPowerFiltration
public import WeilConjectures.RepresentationTheory.Dual
public import WeilConjectures.AlgebraicGeometry.GroupScheme.RealSheaves.Condensed.CommonGradedRepresentationFactors
public import WeilConjectures.AlgebraicGeometry.GroupScheme.RealSheaves.Condensed.FilteredRepresentationFactors

/-!
# Tensor and exterior powers of filtered Weil representations

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-determinant-weights/sec-representations-and-filtrations/sk-r-linear-library/_section.md`,
statement and Complement
(blueprint: `sk-r-linear-library`).

The coefficient field is an algebraically closed characteristic-zero field, instantiated by
`\\overline{\\mathbf Q}_\\ell` in the Weil setting.  The representation-theory declarations used
below are the published generic interfaces for filtrations, composition factors, duals and Schur's
lemma; the group parameter is the Weil group in the application.
-/

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct

namespace RealSheaves.Condensed

universe u v w

/-- Tensor and exterior powers of a filtered representation, with the Complement clauses.
Source: the statement and Complement of `sk-r-linear-library`
(blueprint: sk-r-linear-library).
The proof follows the seven steps in the source: choose composition series; apply the tensor
filtration; apply the exterior-power filtration; refine and compare semisimplifications; use the
dual annihilator filtration; apply the zero-or-invertible Schur statement; and identify invertible
endomorphisms with nonzero scalars by Schur's lemma.

Proof steps:
1. Choose composition series for both representations (their existence is the composition-series
   existence theorem), and use Jordan--Hölder and semisimplification.
2. Apply the filtered tensor-product theorem; if a series is empty, the corresponding tensor
   product is zero.
3. Apply the filtered exterior-power theorem, including the out-of-range and empty-tuple cases.
4. Refine filtrations and use independence of semisimplification to obtain the multiplicity
   bijections.
5. Use the dual annihilator filtration, with the contragredient action on each quotient.
6. Apply Schur's zero-or-bijective alternative to irreducible endomorphisms.
7. Apply scalar Schur to identify every bijective endomorphism with a nonzero scalar.
-/
theorem filteredRepresentationLibrary
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {W : Type w} [Group W]
    {V V' : Type v} [AddCommGroup V] [Module k V]
      [AddCommGroup V'] [Module k V']
      [FiniteDimensional k V] [FiniteDimensional k V']
    (ρ : Representation k W V) (ρ' : Representation k W V') (r : ℕ)
    (s : ρ.CompositionSeries) (s' : ρ'.CompositionSeries) :
    (Nonempty ρ.CompositionSeries ∧ Nonempty ρ'.CompositionSeries) ∧
      Representation.HasGradedPieces (ρ.tprod ρ')
        (fun p : Fin s.length × Fin s'.length ↦
          Representation.EquivTo ((s.factor p.1).tprod (s'.factor p.2))) ∧
      Representation.HasGradedPieces (ρ.exteriorPower r)
        (fun n : {n : Fin s.length → ℕ // ∑ i, n i = r} ↦
          Representation.EquivTo
            (Representation.piTprodExteriorPower (fun i ↦ s.factor i) n.1)) ∧
      (∀ n : {n : Fin s.length → ℕ // ∑ i, n i = r},
        (∀ i : Fin s.length,
          n.1 i ≤ Module.finrank k
            ((s.series i.succ).toSubmodule ⧸
              (s.series i.castSucc).toSubmodule.comap
                (s.series i.succ).toSubmodule.subtype)) →
          Nontrivial (⨂[k] i,
            ⋀[k]^(n.1 i)
              ((s.series i.succ).toSubmodule ⧸
                (s.series i.castSucc).toSubmodule.comap
                  (s.series i.succ).toSubmodule.subtype))) ∧
      (∀ t : ∀ p : Fin s.length × Fin s'.length,
          ((s.factor p.1).tprod (s'.factor p.2)).CompositionSeries,
        ∀ c : (ρ.tprod ρ').CompositionSeries,
          ∃ e : Fin c.length ≃ Σ p, Fin (t p).length,
            ∀ p (i : Fin (t p).length),
              Representation.EquivTo ((t p).factor i) (c.factor (e.symm ⟨p, i⟩))) ∧
      (∀ t : ∀ n : {n : Fin s.length → ℕ // ∑ i, n i = r},
          (Representation.piTprodExteriorPower (fun i ↦ s.factor i) n.1).CompositionSeries,
        ∀ c : (ρ.exteriorPower r).CompositionSeries,
          ∃ e : Fin c.length ≃ Σ n, Fin (t n).length,
            ∀ n (i : Fin (t n).length),
              (fun {X Y : Type (max u v)} [AddCommGroup X] [Module k X]
                [AddCommGroup Y] [Module k Y]
                (σ : Representation k W X) (τ : Representation k W Y)
                (a : σ.CompositionSeries) (b : τ.CompositionSeries)
                (j : Fin a.length) (h : Fin b.length) ↦
                  Nonempty ((a.factor j).Equiv (b.factor h)))
                (ρ.exteriorPower r)
                (Representation.piTprodExteriorPower (fun j ↦ s.factor j) n.1)
                c (t n) (e.symm ⟨n, i⟩) i) ∧
      (∀ s₁ s₂ : ρ.CompositionSeries,
        ∃ e : Fin s₁.length ≃ Fin s₂.length,
          ∀ i, Nonempty ((s₁.factor i).Equiv (s₂.factor (e i)))) ∧
      (∀ s₁ s₂ : ρ'.CompositionSeries,
        ∃ e : Fin s₁.length ≃ Fin s₂.length,
          ∀ i, Nonempty ((s₁.factor i).Equiv (s₂.factor (e i)))) ∧
      (Representation.ConstituentsLE (ρ.tprod ρ')
        (s.semisimplification.tprod s'.semisimplification) ∧
        Representation.ConstituentsLE (s.semisimplification.tprod s'.semisimplification)
          (ρ.tprod ρ')) ∧
      (Representation.ConstituentsLE (ρ.exteriorPower r)
        (s.semisimplification.exteriorPower r) ∧
        Representation.ConstituentsLE (s.semisimplification.exteriorPower r)
          (ρ.exteriorPower r)) ∧
      (∀ c : (ρ.tprod ρ').CompositionSeries,
        ∀ c' : (s.semisimplification.tprod s'.semisimplification).CompositionSeries,
        ∃ e : Fin c.length ≃ Fin c'.length,
          ∀ j, (fun {X Y : Type v} [AddCommGroup X] [Module k X]
              [AddCommGroup Y] [Module k Y]
              (σ : Representation k W X) (τ : Representation k W Y)
              (a : σ.CompositionSeries) (b : τ.CompositionSeries)
              (j : Fin a.length) (h : Fin b.length) ↦
                Nonempty ((a.factor j).Equiv (b.factor h)))
              (ρ.tprod ρ') (s.semisimplification.tprod s'.semisimplification)
              c c' j (e j)) ∧
      (∀ c : (ρ.exteriorPower r).CompositionSeries,
        ∀ c' : (s.semisimplification.exteriorPower r).CompositionSeries,
        ∃ e : Fin c.length ≃ Fin c'.length,
          ∀ j, (fun {X Y : Type (max u v)} [AddCommGroup X] [Module k X]
              [AddCommGroup Y] [Module k Y]
              (σ : Representation k W X) (τ : Representation k W Y)
              (a : σ.CompositionSeries) (b : τ.CompositionSeries)
              (j : Fin a.length) (h : Fin b.length) ↦
                Nonempty ((a.factor j).Equiv (b.factor h)))
              (ρ.exteriorPower r) (s.semisimplification.exteriorPower r)
              c c' j (e j)) ∧
      (∀ {X : Type v} [AddCommGroup X] [Module k X]
        (σ : Representation k W X) {ι : Type*} {Y : ι → Type v}
        [∀ i, AddCommGroup (Y i)] [∀ i, Module k (Y i)]
        (τ : ∀ i, Representation k W (Y i)),
        Representation.HasGradedPieces σ
            (fun i ↦ Representation.EquivTo (τ i)) →
          Representation.HasGradedPieces σ.dual
            (fun i ↦ Representation.EquivTo (τ i).dual)) ∧
      (∀ {X : Type v} [AddCommGroup X] [Module k X]
        [FiniteDimensional k X] (σ : Representation k W X),
        σ.IsIrreducible →
        (∀ c : Representation.IntertwiningMap σ σ,
          Function.Bijective c ∨ c = 0) ∧
        (∀ c : Representation.IntertwiningMap σ σ,
          Function.Bijective c →
            ∃ a : k, a ≠ 0 ∧
              c = algebraMap k (Representation.IntertwiningMap σ σ) a)) := by
  classical
  have ht := s.hasGradedPieces_tprod s'
  have hext := s.hasGradedPieces_exteriorPower r
  have hs : Representation.HasGradedPieces s.semisimplification
      (fun i : Fin s.length ↦ Representation.EquivTo (s.factor i)) := by
    refine (Representation.hasGradedPieces_of_monotone
      (fun i : Fin (s.length + 1) ↦ Representation.directSumFiltration
        (fun j ↦ s.factor j) i)
      (Fin.monotone_iff_le_succ.2 fun i ↦
        Representation.directSumFiltration_le_succ _ i)
      (Representation.directSumFiltration_zero _)
      (Representation.directSumFiltration_eq_top _)).mono ?_
    exact fun i {_} {_} {_} _ hi ↦
      hi.trans (Representation.directSumFiltrationEquiv (fun j ↦ s.factor j) i).symm
  have hs' : Representation.HasGradedPieces s'.semisimplification
      (fun i : Fin s'.length ↦ Representation.EquivTo (s'.factor i)) := by
    refine (Representation.hasGradedPieces_of_monotone
      (fun i : Fin (s'.length + 1) ↦ Representation.directSumFiltration
        (fun j ↦ s'.factor j) i)
      (Fin.monotone_iff_le_succ.2 fun i ↦
        Representation.directSumFiltration_le_succ _ i)
      (Representation.directSumFiltration_zero _)
      (Representation.directSumFiltration_eq_top _)).mono ?_
    exact fun i {_} {_} {_} _ hi ↦
      hi.trans (Representation.directSumFiltrationEquiv (fun j ↦ s'.factor j) i).symm
  have hts : Representation.HasGradedPieces
      (s.semisimplification.tprod s'.semisimplification)
      (fun p : Fin s.length × Fin s'.length ↦
        Representation.EquivTo ((s.factor p.1).tprod (s'.factor p.2))) := by
    have h := (hs.tprod_right s'.semisimplification).trans
      (R := fun i j ↦ Representation.EquivTo ((s.factor i).tprod (s'.factor j)))
      (fun _ _ ↦ Representation.isInvariant_equivTo _)
      (fun i {_} {_} {_} _ hi ↦ (hs'.tprod_left (s.factor i)).of_equiv
        (fun _ ↦ Representation.isInvariant_equivTo _) hi.equiv.symm)
    exact h.reindex (Equiv.sigmaEquivProd _ _)
  have hes : Representation.HasGradedPieces (s.semisimplification.exteriorPower r)
      (fun n : {n : Fin s.length → ℕ // ∑ i, n i = r} ↦
        Representation.EquivTo
          (Representation.piTprodExteriorPower (fun i ↦ s.factor i) n.1)) := by
    refine (Representation.hasGradedPieces_exteriorPower_of_monotone s.length
      s.semisimplification
      (fun i : Fin (s.length + 1) ↦ Representation.directSumFiltration
        (fun j ↦ s.factor j) i)
      (Fin.monotone_iff_le_succ.2 fun i ↦
        Representation.directSumFiltration_le_succ _ i)
      (Representation.directSumFiltration_zero _)
      (Representation.directSumFiltration_eq_top _) r).mono ?_
    exact fun n {_} {_} {_} _ hn ↦ hn.trans
      (Representation.Equiv.piTprodExteriorPowerCongr
        (fun i ↦ (Representation.directSumFiltrationEquiv (fun j ↦ s.factor j) i).symm)
        (fun _ ↦ rfl))
  have htc := commonGradedRepresentationFactors
    (fun p : Fin s.length × Fin s'.length ↦ (s.factor p.1).tprod (s'.factor p.2)) ht hts
  have hfin : ∀ n : {n : Fin s.length → ℕ // ∑ i, n i = r},
      FiniteDimensional k (⨂[k] i,
        ⋀[k]^(n.1 i)
          ((s.series i.succ).toSubmodule ⧸
            (s.series i.castSucc).toSubmodule.comap
              (s.series i.succ).toSubmodule.subtype)) := by
    intro n
    exact Module.Finite.of_basis (Basis.piTensorProduct fun i ↦
      Module.finBasis k (⋀[k]^(n.1 i)
        ((s.series i.succ).toSubmodule ⧸
          (s.series i.castSucc).toSubmodule.comap
            (s.series i.succ).toSubmodule.subtype)))
  have hec := commonGradedRepresentationFactors
    (fun n : {n : Fin s.length → ℕ // ∑ i, n i = r} ↦
      Representation.piTprodExteriorPower (fun i ↦ s.factor i) n.1) hext hes
  refine ⟨⟨ρ.exists_compositionSeries, ρ'.exists_compositionSeries⟩, ht, hext,
    ?_, ?_, ?_, Representation.CompositionSeries.jordanHolder,
    Representation.CompositionSeries.jordanHolder, htc.1, hec.1, htc.2, hec.2, ?_, ?_⟩
  · intro n hn
    exact (Representation.nontrivial_piTensorProduct_exteriorPower_iff n.1).2 hn
  · intro t c
    obtain ⟨e, he⟩ := filteredRepresentationFactors
      (fun p : Fin s.length × Fin s'.length ↦
        (s.factor p.1).tprod (s'.factor p.2)) ht t c
    exact ⟨e, he.2⟩
  · intro t c
    obtain ⟨e, he⟩ := filteredRepresentationFactors
      (fun n : {n : Fin s.length → ℕ // ∑ i, n i = r} ↦
        Representation.piTprodExteriorPower (fun i ↦ s.factor i) n.1) hext t c
    exact ⟨e, he.2⟩
  · intro X _ _ σ ι Y _ _ τ h
    exact h.dual
  · intro X _ _ _ σ hσ
    have := hσ
    refine ⟨fun c ↦ Representation.IsIrreducible.bijective_or_eq_zero c, ?_⟩
    intro c hc
    obtain ⟨a, ha⟩ :=
      Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 c
    refine ⟨a, ?_, ha.symm⟩
    intro hzero
    have hc0 : c = 0 := by simpa [hzero] using ha.symm
    have : Subsingleton X := ⟨fun x y ↦ hc.1 (by simp [hc0])⟩
    have := hσ.nontrivial
    exact false_of_nontrivial_of_subsingleton X

end RealSheaves.Condensed
