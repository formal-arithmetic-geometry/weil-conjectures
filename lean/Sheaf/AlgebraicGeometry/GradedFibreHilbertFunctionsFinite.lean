/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.GradedSheafGeneration
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.AffinePushforwardFreeEvaluation
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Sheaf.RingTheory.NoetherianAlgebraModuleGenericFreeness
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Finitely many graded fibre Hilbert functions

Source: Stacks Project, Tags 0ASY (lemma-generic-flatness-stratification)
and 00K0 (lemma-graded-module-fg); Bourbaki Expose 221, Lemma 3.5
(blueprint: lem-sfb-graded-fibre-hilbert-functions-finite).

The Hilbert function records residue-field dimensions of the homogeneous stalks.
The tensor factors use extension-of-scalars order, canonically isomorphic by
commutativity to the order in the node. The finite set contains whole functions,
so the assertion is simultaneous in every nonnegative degree.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The complete fibre Hilbert function of a family of module sheaves at a point.
The scalar algebra is the canonical residue map from the actual local ring.
Source: Stacks Project, Tag 0ASY and Bourbaki Expose 221, Lemma 3.5
(blueprint: lem-sfb-graded-fibre-hilbert-functions-finite). -/
noncomputable def gradedFibreHilbertFunction {S : Scheme.{u}} (L : ℕ → S.Modules)
    (s : S) : ℕ → ℕ :=
  letI := (S.residue s).hom.toAlgebra
  fun d : ℕ ↦ Module.finrank (S.residueField s)
    ((S.residueField s) ⊗[S.presheaf.stalk s]
      ((RingedSpace.moduleStalkFunctor S.toRingedSpace s).obj (L d)))

/-- Every homogeneous piece is coherent and only finitely many entire fibre Hilbert
functions occur, for a finite graded module over a standard graded algebra on a
Noetherian scheme. The finite set can be empty when the scheme is empty.
Source: Stacks Project, Tags 0ASY, 00K0, 051R and 00NX; Bourbaki Expose 221, Lemma 3.5
(blueprint: lem-sfb-graded-fibre-hilbert-functions-finite).

Proof:
1. Choose finite local degree-one generators x_i for the algebra and homogeneous
   generators e_j of degrees b_j for L. For fixed d, the monomials x^a e_j with
   |a|=d-b_j form a finite local generating family of L_d. There are none from
   b_j>d. Quasi-coherence and pqf-lem-coherent-ft-locnoeth give coherence.
2. Cover S by finitely many affine charts Spec A on which these generators exist.
   The affine free-evaluation lemma applied to the identity, degree by degree,
   gives a finite-type graded A-algebra C and a finite graded C-module M with
   each M_d finite over A. The affine module-germ localization lemma and the
   fraction formula m/u tensor z maps to m tensor u^{-1}z identify the displayed
   fibre dimensions with dim over kappa(p) of M_d tensor_A kappa(p).
3. For an ideal I of A let P(I) mean that finitely many entire functions occur
   over V(I). If P fails, ACC (lem-weil-pbc-noetherian-finite-module-acc) gives
   a maximal bad I. It is proper. The Noetherian quotient has finitely many
   minimal primes by lem-weil-pbc-noetherian-finitely-many-minimal-primes.
   If I is not prime their inverse images strictly contain I and their closed
   sets cover V(I). The finite union of their finite sets contradicts badness.
4. Thus R=A/I is a Noetherian domain. Set D=C tensor_A R and N=M tensor_A R.
   The componentwise tensor/direct-sum isomorphism preserves the grading.
   The fixed generators make D finite type and N finite over D. By
   lem-pur-noetherian-algebra-module-generic-freeness a single nonzero a in R
   makes all of N_a free over R_a, possibly with infinite rank. Localization
   preserves the grading, making each (N_d)_a a direct summand of N_a.
5. Each (N_d)_a is finite. The images of its finite generators in a basis of N_a
   have finite combined support T_d. Its inclusion factors through R_a^{T_d};
   the degree-d projection restricts to a retraction. Hence it is finite
   projective. By lem-weil-pbc-finite-projective-rank-locally-constant its
   fibre rank is locally constant. Spec R_a is irreducible (R_a is a domain),
   so the rank is constant. This gives one whole function on Spec R_a.
6. Lift a to A. The complement inside V(I) is V(I+(a)), whose ideal strictly
   contains I; it has finitely many functions by maximality. Quotienting and
   localizing preserve residue fields and fibres: the maps send
   (m tensor b) tensor z to m tensor bz, and m tensor z back to
   (m tensor 1) tensor z. The localization identification uses the fraction
   formula in step 2. Adjoining the one function from step 5 contradicts
   badness. Therefore P(0) holds on this affine chart.
7. Take the union of the finite sets over the finite affine cover. It contains
   every complete fibre function by step 2. For the empty scheme use the empty
   cover and H empty. Empty generating families and zero modules cause no
   exception in any step. -/
theorem graded_fibre_hilbert_functions_finite
    (S : Scheme.{u}) [IsNoetherian S] (B L : ℕ → S.Modules)
    (A : GradedSheafAlgebra B) (M : GradedSheafModule A L)
    (hB : ∀ d : ℕ, SheafOfModules.IsQuasicoherent.{u} (B d))
    (hzero : IsIso A.unit)
    (hone : RingedSpace.IsCoherent S.toRingedSpace (B 1))
    (hgen : A.IsGeneratedInDegreeOne)
    (hL : ∀ d : ℕ, SheafOfModules.IsQuasicoherent.{u} (L d))
    (hM : M.IsLocallyFinitelyGenerated) :
    (∀ d : ℕ, RingedSpace.IsCoherent S.toRingedSpace (L d)) ∧
      ∃ H : Set (ℕ → ℕ), H.Finite ∧
        (∀ s : S, gradedFibreHilbertFunction L s ∈ H) ∧ (IsEmpty S → H = ∅) := by
  sorry

end AlgebraicGeometry
