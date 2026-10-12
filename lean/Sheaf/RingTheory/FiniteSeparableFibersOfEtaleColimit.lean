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
import Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise

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
  sorry

end CommAlgCat
