/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Sheaf.AlgebraicGeometry.NowhereDenseDimensionDrop
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# A lisse open with smaller-dimensional complement

Source: blueprint `sec-purity-real-sheaves/sk-p-real-purity/fin2-lem-lisse-dense-open.md`,
order 2666, with the reviewed DAG's explicit empty-scheme convention
(blueprint: fin2-lem-lisse-dense-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A constructible sheaf over finite commutative coefficients on a finite-type scheme
over a field is lisse on an open subscheme whose complement has strictly smaller
dimension when the scheme is nonempty. On the empty scheme the open is the whole scheme.

Source: blueprint `sec-purity-real-sheaves/sk-p-real-purity/fin2-lem-lisse-dense-open.md`,
order 2666, and the reviewed DAG statement's empty-scheme convention
(blueprint: fin2-lem-lisse-dense-open).

Proof:
1. If X is empty, take the top open. The empty etale cover trivializes the restriction,
   and finite stalks are vacuous, as in `def-weil-pbc-constructible-complexes`.
2. Otherwise Spec k is Noetherian, so X is Noetherian by
   `lem-weil-pbc-finite-type-over-noetherian`. Its dimension is finite by
   `lem-kun-dimension-finite-type`. The chain definitions `def-kun-dimension` and
   `def-kun-topological-krull-dimension` agree, and nonemptiness makes this dimension
   a natural number d.
3. Copy the finite constructible locally closed partition witnessing
   `def-weil-pbc-constructible-complexes` into `def-constructible-stratification`.
   On each stratum, `lem-weil-pbc-finite-locally-constant-module-values` identifies
   finite constant module values with local constancy and finite stalks. Thus the same
   module sheaf is constructible in the sense of `def-constructible-constructible`.
4. Apply `prop-constructible-generic-constancy` in the category of modules over the
   same ring. It gives a dense open U on which the restriction is finite locally
   constant, precisely the lisse condition of `def-weil-pbc-constructible-complexes`.
5. The closed complement of this dense open is nowhere dense. Apply
   `lem-sc-hilbert-nowhere-dense-dimension-drop` to X and that complement to obtain
   the strict inequality. This also covers the empty complement, of dimension bottom.
-/
theorem exists_lisse_open_dimension_drop
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    ∃ U : X.Opens,
      IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F) ∧
      (Nonempty X → topologicalKrullDim {x : X // x ∉ U} < topologicalKrullDim X) ∧
      (IsEmpty X → U = ⊤) := by
  classical
  have hconstructible : IsConstructibleSheaf F := by
    obtain ⟨S, hS⟩ := hF
    exact ⟨⟨S, fun i ↦ (finite_locally_constant_module_values_iff _).1.mp (hS i)⟩⟩
  let := hconstructible
  obtain ⟨U, hU, hFU⟩ := IsConstructibleSheaf.exists_dense_open F
  refine ⟨U, hFU, ?_, ?_⟩
  · intro hnonempty
    let := hnonempty
    let : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    have : CompactSpace X :=
      QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    have htop := topologicalKrullDim_ne_top_of_compactSpace (X ↘ Spec (.of k))
    have hbot : topologicalKrullDim X ≠ ⊥ := by
      apply Order.krullDim_ne_bot_iff.mpr
      exact ⟨⟨closure {Classical.arbitrary X}, isIrreducible_singleton.closure,
        isClosed_closure⟩⟩
    obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim X = (d : WithBot ℕ∞) := by
      generalize topologicalKrullDim X = n at htop hbot ⊢
      induction n using WithBot.recBotCoe with
      | bot => exact False.elim (hbot rfl)
      | coe n =>
        induction n using ENat.recTopCoe with
        | top => exact False.elim (htop rfl)
        | coe n => exact ⟨n, rfl⟩
    rw [hd]
    exact X.topologicalKrullDim_lt_of_isNowhereDense d hd (U : Set X)ᶜ
      U.isOpen.isClosed_compl (U.isOpen.isClosed_compl.isNowhereDense_iff.mpr
        hU.interior_compl)
  · intro hempty
    let := hempty
    ext x
    exact isEmptyElim x

end AlgebraicGeometry.Scheme
