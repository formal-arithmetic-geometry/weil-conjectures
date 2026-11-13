/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.DenseOpenComponentModifications
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# A finite smooth modification of a reduced curve

## References

* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0A3Q](https://stacks.math.columbia.edu/tag/0A3Q)
* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
* [Stacks Project, Tag 0BA8](https://stacks.math.columbia.edu/tag/0BA8)
* [Stacks Project, Tag 0BAJ](https://stacks.math.columbia.edu/tag/0BAJ)
* [Stacks Project, Tag 01WK](https://stacks.math.columbia.edu/tag/01WK)
* [Stacks Project, Tag 0CYI](https://stacks.math.columbia.edu/tag/0CYI)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A reduced finite-type curve admits a finite list of its distinct integral components.
-/
private theorem exists_integral_component_cover_of_reduced_curve
    {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsReduced X] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (n : ℕ) (C : Fin n → Scheme.{u}) (ι : ∀ i, C i ⟶ X),
      (∀ i, IsIntegral (C i) ∧ IsClosedImmersion (ι i) ∧
        topologicalKrullDim (C i) ≤ 1 ∧
        Set.range (ι i) ∈ irreducibleComponents X) ∧
      Function.Injective (fun i => Set.range (ι i)) ∧
      (∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (ι i) = Z) := by
  classical
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  let A := {Z : Set X // Z ∈ irreducibleComponents X}
  have : Fintype A := (finite_irreducibleComponents_of_isNoetherian (X := X)).fintype
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let Z (i : Fin (Fintype.card A)) : TopologicalSpace.Closeds X :=
    ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩
  let I (i : Fin (Fintype.card A)) := Scheme.IdealSheafData.vanishingIdeal (Z i)
  refine ⟨Fintype.card A, fun i => (I i).subscheme, fun i => (I i).subschemeι,
    ?_, ?_, ?_⟩
  · intro i
    have hr : Set.range (I i).subschemeι = (e i).1 := by
      simp [I, Z]
    have hi : IrreducibleSpace (I i).subscheme := by
      exact Subtype.irreducibleSpace (e i).2.1
    have : IsIntegral (I i).subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
    exact ⟨inferInstance, inferInstance,
      ((I i).subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hdim,
      hr.symm ▸ (e i).2⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    simpa [I, Z] using hij
  · intro W hW
    obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
    refine ⟨i, ?_⟩
    simp [I, Z, hi]

/-- Assemble finite smooth modifications of the distinct integral components.
-/
private theorem exists_modification_of_component_modifications
    {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsReduced X]
    (n : ℕ) (C : Fin n → Scheme.{u}) (ι : ∀ i, C i ⟶ X)
    (hC : ∀ i, IsIntegral (C i) ∧ IsClosedImmersion (ι i) ∧
      topologicalKrullDim (C i) ≤ 1 ∧ Set.range (ι i) ∈ irreducibleComponents X)
    (hinj : Function.Injective (fun i => Set.range (ι i)))
    (hcover : ∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (ι i) = Z)
    (Y : Fin n → Scheme.{u}) (ν : ∀ i, Y i ⟶ C i)
    (hν : ∀ i, IsFinite (ν i) ∧ topologicalKrullDim (Y i) ≤ 1 ∧
      Smooth (ν i ≫ ι i ≫ (X ↘ Spec (.of k))) ∧
      ∃ U : (C i).Opens, Dense (U : Set (C i)) ∧ IsIso (ν i ∣_ U)) :
    ∃ (T : Scheme.{u}) (f : T ⟶ X),
      IsFinite f ∧ topologicalKrullDim T ≤ 1 ∧ Smooth (f ≫ (X ↘ Spec (.of k))) ∧
      ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (f ∣_ U) := by
  classical
  have (i : Fin n) : IsClosedImmersion (ι i) := (hC i).2.1
  have (i : Fin n) : IsFinite (ν i) := (hν i).1
  let f : (∐ Y) ⟶ X := CategoryTheory.Limits.Sigma.desc (fun i => ν i ≫ ι i)
  have hf : IsFinite f := inferInstance
  have hs : Smooth (f ≫ (X ↘ Spec (.of k))) := by
    have he : f ≫ (X ↘ Spec (.of k)) =
        CategoryTheory.Limits.Sigma.desc (fun i => ν i ≫ ι i ≫ (X ↘ Spec (.of k))) := by
      ext i
      simp [f]
    rw [he]
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth) (fun i => (hν i).2.2.1)
  have hd : topologicalKrullDim ↥(∐ Y) ≤ 1 := by
    let V (i : Fin n) := (CategoryTheory.Limits.Sigma.ι Y i).opensRange
    apply topologicalKrullDim_le_of_iSup_eq_top V (sigmaOpenCover Y).iSup_opensRange 1
    intro i
    let e := IsOpenImmersion.isoOfRangeEq (CategoryTheory.Limits.Sigma.ι Y i) (V i).ι
      (by simp [V])
    have he := (Scheme.homeoOfIso e).isHomeomorph
    exact (he.topologicalKrullDim_eq _).symm.trans_le (hν i).2.1
  obtain ⟨U, hU, hiso⟩ := exists_dense_open_isIso_component_modifications X n C ι
    (fun i => ⟨(hC i).1, (hC i).2.1, (hC i).2.2.2⟩) hinj hcover Y ν
    (fun i => (hν i).2.2.2)
  exact ⟨∐ Y, f, hf, hd, hs, U, hU, hiso⟩

/-- Normalize an integral curve of dimension at most one. Finiteness, dimension preservation,
and the dense-open isomorphism come from the source normalization module. Its normal stalks
are regular in dimension at most one, and regular finite-type schemes over a perfect field
are smooth. -/
private theorem integral_curve_modification
    {k : Type u} [Field k] [IsAlgClosed k] (C : Scheme.{u}) [IsIntegral C]
    (q : C ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ C),
      IsFinite ν ∧ topologicalKrullDim Y ≤ 1 ∧ Smooth (ν ≫ q) ∧
      ∃ U : C.Opens, Dense (U : Set C) ∧ IsIso (ν ∣_ U) := by
  have := C.isFinite_fromNormalization_of_locallyOfFiniteType q
  have : IsLocallyNoetherian C.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (C.fromNormalization ≫ q)
  have hK (x : Spec C.functionField) :
      IsIntegrallyClosed ((Spec C.functionField).presheaf.stalk x) := by
    let := TopCat.Presheaf.algebra_section_stalk (Spec C.functionField).presheaf
      (⟨x, trivial⟩ : (⊤ : (Spec C.functionField).Opens))
    have := (isAffineOpen_top (Spec C.functionField)).isLocalization_stalk ⟨x, trivial⟩
    have : IsIntegrallyClosed Γ(Spec C.functionField, ⊤) :=
      .of_equiv (Scheme.ΓSpecIso C.functionField).commRingCatIsoToRingEquiv.symm
    exact isIntegrallyClosed_of_isLocalization _ _
      ((isAffineOpen_top _).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
  have hdim' : topologicalKrullDim C.normalization ≤ 1 :=
    (C.topologicalKrullDim_normalization q).trans_le hdim
  have : IsRegular C.normalization := IsRegular.of_isIntegrallyClosed_stalk
    (fun y => ⟨inferInstance, C.fromSpecFunctionField.isIntegrallyClosed_stalk_normalization
      hK y⟩) hdim'
  obtain ⟨U, hU, hiso⟩ := C.exists_isIso_fromNormalization_restrict q
  exact ⟨C.normalization, C.fromNormalization, inferInstance, hdim',
    smooth_of_isRegular _, U, U.isOpen.dense hU, hiso⟩

/-- A reduced separated finite-type scheme of dimension at most one over an algebraically
closed field admits a finite modification from a smooth separated finite-type scheme of
dimension at most one, which is an isomorphism over a dense open. -/
theorem exists_finite_smooth_modification_of_reduced_curve
    {k : Type u} [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsReduced X]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (h_dim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X),
      IsSeparated (ν ≫ (X ↘ Spec (.of k))) ∧
      LocallyOfFiniteType (ν ≫ (X ↘ Spec (.of k))) ∧
      QuasiCompact (ν ≫ (X ↘ Spec (.of k))) ∧
      topologicalKrullDim Y ≤ 1 ∧ Smooth (ν ≫ (X ↘ Spec (.of k))) ∧
      IsFinite ν ∧ ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (ν ∣_ U) := by
  classical
  obtain ⟨n, C, ι, hC, hinj, hcover⟩ :=
    exists_integral_component_cover_of_reduced_curve (k := k) X h_dim
  have hm (i : Fin n) : ∃ (Y : Scheme.{u}) (ν : Y ⟶ C i),
      IsFinite ν ∧ topologicalKrullDim Y ≤ 1 ∧
      Smooth (ν ≫ (ι i ≫ (X ↘ Spec (.of k)))) ∧
      ∃ U : (C i).Opens, Dense (U : Set (C i)) ∧ IsIso (ν ∣_ U) := by
    have : IsIntegral (C i) := (hC i).1
    have : IsClosedImmersion (ι i) := (hC i).2.1
    exact integral_curve_modification (C i) (ι i ≫ (X ↘ Spec (.of k))) (hC i).2.2.1
  choose Y ν hν using hm
  obtain ⟨T, f, hf, hT, hs, U, hdense, hiso⟩ :=
    exists_modification_of_component_modifications (k := k) X n C ι hC hinj hcover Y ν hν
  have : IsFinite f := hf
  exact ⟨T, f, inferInstance, inferInstance, inferInstance, hT, hs, hf, U, hdense, hiso⟩

end AlgebraicGeometry
