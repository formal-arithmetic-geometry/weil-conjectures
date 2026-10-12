/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.FieldTheory.Separable
import Sheaf.RingTheory.FibrePrimesResidueFields
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.FilteredEtaleFiberStructure
import Sheaf.RingTheory.FilteredEtaleFiberSeparableImage
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Finite separable fibres of a Noetherian filtered colimit of etale algebras

Source: Stacks Project, More on Algebra, Lemma Tag 0AH1
(blueprint: lem-weil-pbc-henselization-finite-separable-fibres).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- A Noetherian filtered colimit of etale algebras has finitely many primes over each
base prime; its fibre is canonically the product of their residue fields, each a
separable algebraic extension of the base residue field.
Source: Stacks Project, More on Algebra, Lemma Tag 0AH1
(blueprint: lem-weil-pbc-henselization-finite-separable-fibres).

Mathlib's `Ideal.Fiber` uses `κ(p) ⊗[A] B`; tensor symmetry identifies this with
`B ⊗[A] κ(p)` in the source. The component `ψ q` sends `λ ⊗ b` to `λ̄ b̄`.
`Algebra.IsSeparable` includes algebraicity; no finiteness of these extensions is claimed.

Proof:
1. The fibre is a filtered colimit of the stage fibres by
   `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise`.
2. By `lem-weil-pbc-etale-ring-base-change` and
   `lem-weil-pbc-etale-algebra-over-field-product`, each stage fibre is a finite
   product of finite separable field extensions.
3. A finite product of fields is reduced; its primes are precisely the kernels
   of projections, hence both minimal and maximal.
4. Lift a nilpotent element to a stage and its vanishing power to a later stage;
   reducedness there shows the element vanishes in the colimit fibre.
5. Comparable primes of the fibre contract to equal primes at every stage.
   Since every element comes from a stage, the two primes are equal. Thus all
   primes of the fibre are minimal and maximal.
6. By `lem-weil-pbc-fibre-ring-noetherian` the fibre is Noetherian, so
   `lem-weil-pbc-noetherian-finitely-many-minimal-primes` makes its primes finite.
7. By `lem-weil-pbc-zero-locus-eq-iff-radical-eq` their intersection is zero.
   Apply `lem-weil-pbc-product-of-localizations-at-maximal`: the fibre is the
   product of its localizations. Each localization is reduced and has just one
   prime, whose ideal is therefore zero; it is its own residue field.
8. By `lem-weil-pbc-fibre-ring-primes-residue-fields`, these primes correspond
   exactly to the primes of B over p, and the residue-field identifications
   turn this decomposition into the canonical product map `RingHom.pi ψ`.
9. Every element of a resulting residue field comes from a stage fibre and hence
   from one of its finite separable field factors. Its minimal polynomial is
   preserved under that field embedding, proving separable algebraicity as in
   `def-weil-pbc-separable-algebraic-extension`. -/
theorem finite_separable_fibers_of_etale_colimit
    (A : Type u) [CommRing A]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommAlgCat.{v} A) [HasColimit D]
    (hD : ∀ i : I, Algebra.Etale A (D.obj i))
    [IsNoetherianRing ↥(colimit D)] (p : PrimeSpectrum A) :
    let B := ↥(colimit D)
    let F := PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}
    let ρ : (q : F) → p.asIdeal.ResidueField →ₐ[A] q.1.asIdeal.ResidueField := fun q ↦
      Ideal.ResidueField.mapₐ p.asIdeal q.1.asIdeal (Algebra.ofId A B)
        congr($(q.2.symm).asIdeal)
    let ψ : (q : F) → p.asIdeal.Fiber B →+* q.1.asIdeal.ResidueField := fun q ↦
      (Algebra.TensorProduct.lift (ρ q)
        (IsScalarTower.toAlgHom A B q.1.asIdeal.ResidueField)
        (fun _ _ ↦ Commute.all _ _)).toRingHom
    Finite F ∧ Function.Bijective (RingHom.pi ψ) ∧
      ∀ q : F,
        letI := (ρ q).toRingHom.toAlgebra
        Algebra.IsSeparable p.asIdeal.ResidueField q.1.asIdeal.ResidueField := by
  classical
  dsimp only
  let B := ↥(colimit D)
  let C := p.asIdeal.Fiber B
  let F := PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}
  let ρ : (q : F) → p.asIdeal.ResidueField →ₐ[A] q.1.asIdeal.ResidueField := fun q ↦
    Ideal.ResidueField.mapₐ p.asIdeal q.1.asIdeal (Algebra.ofId A B)
      congr($(q.2.symm).asIdeal)
  let ψ : (q : F) → C →+* q.1.asIdeal.ResidueField := fun q ↦
    (Algebra.TensorProduct.lift (ρ q)
      (IsScalarTower.toAlgHom A B q.1.asIdeal.ResidueField)
      (fun _ _ ↦ Commute.all _ _)).toRingHom
  obtain ⟨hred, hdim⟩ := filteredEtale_fiber_structure A D hD p
  let : IsReduced C := hred
  let : Ring.KrullDimLE 0 C := hdim
  let : IsNoetherianRing C := Ideal.isNoetherianRing_fiber p.asIdeal
  let : IsArtinianRing C := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  obtain ⟨e, _, _, hθ⟩ := PrimeSpectrum.fibre_primes_residue_fields A B p
  let : Finite F := Finite.of_equiv (PrimeSpectrum C) e.toEquiv
  have hbij : Function.Bijective (RingHom.pi ψ) := by
    let eM : MaximalSpectrum C ≃ F :=
      IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm.trans e.toEquiv
    let θ (q : F) := (hθ q).choose
    have hθ' (q : F) := (hθ q).choose_spec
    let g (q : F) : (C ⧸ (eM.symm q).asIdeal) ≃+* q.1.asIdeal.ResidueField := by
      change (C ⧸ (e.symm q).asIdeal) ≃+* q.1.asIdeal.ResidueField
      exact (RingEquiv.ofBijective
        (algebraMap (C ⧸ (e.symm q).asIdeal) (e.symm q).asIdeal.ResidueField)
        ((e.symm q).asIdeal.bijective_algebraMap_quotient_residueField)).trans (θ q)
    let E := (IsArtinianRing.equivPi C).toRingEquiv.trans
      ((RingEquiv.piCongrLeft' (fun m : MaximalSpectrum C ↦ C ⧸ m.asIdeal) eM).trans
        (RingEquiv.piCongrRight g))
    have hE : E.toRingHom = RingHom.pi ψ := by
      apply RingHom.ext
      intro x
      funext q
      change θ q (algebraMap (C ⧸ (e.symm q).asIdeal)
        (e.symm q).asIdeal.ResidueField (Ideal.Quotient.mk _ x)) = ψ q x
      rw [Ideal.algebraMap_quotient_residueField_mk]
      exact congrArg (fun f : C →+* q.1.asIdeal.ResidueField ↦ f x) (hθ' q)
    rw [← hE]
    exact E.bijective
  refine ⟨inferInstance, hbij, ?_⟩
  intro q
  let := (ρ q).toRingHom.toAlgebra
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hbij.surjective (Function.update 0 q y)
  have hxy : ψ q x = y := by
    simpa using congrArg (fun z ↦ z q) hx
  rw [← hxy]
  apply filteredEtale_fiber_image_isSeparable A D hD p _ (ψ q)
  intro r
  change (Algebra.TensorProduct.lift (ρ q)
    (IsScalarTower.toAlgHom A B q.1.asIdeal.ResidueField) _)
      (TensorProduct.tmul A r (1 : B)) = ρ q r
  simp

end CommAlgCat
