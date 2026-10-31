/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import WeilConjectures.AlgebraicGeometry.HilbertSamuelInvariant
public import WeilConjectures.RingTheory.FormalInitialDiagram
public import WeilConjectures.RingTheory.DiagonalJets
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.JetDiagramHilbertControl
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # A simultaneous local upper bound for extended Taylor Hilbert functions

Source: Bierstone--Milman, Invent. Math. 128 (1997), Remarks 9.1, Lemma 9.3,
and the completion of Theorem 9.6, pp.275--277, 282; Stacks Tags 00FN, 00FP, 07ZC.
The finite-witness pointwise refinement is the argument recorded in the DAG.
ILO VIII 2.3.11--2.3.13 supplies the surrounding desingularization route
(blueprint: lem-trf-extended-hilbert-local-upper-bound).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory

namespace AlgebraicGeometry.HilbertCoefficient

/-- The principal-parts module of the closed affine subscheme, restricted to the ambient ring.
This is the existing diagonal-jet construction, not a choice of a module with the right rank.

Source: BM 1997, Remarks 9.1; the principal-parts clause of
(blueprint: lem-trf-extended-hilbert-local-upper-bound). -/
def closedPrincipalParts (k : Type u) (R : Type v) [CommRing k] [CommRing R]
    (c : k →+* R) (I : Ideal R) (q : ℕ) : ModuleCat R :=
  letI := c.toAlgebra
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (R ⧸ I) (DiagonalJets.principalParts k (R ⧸ I) q))

/-- Finite modules on the affine neighbourhood have finite presentations. Their dimension
sublevels are open unions of the nonvanishing loci of presentation minors, including negative
bounds and zero or oversized minors.

Source: Stacks Tags 00FN, 00FP, 07ZC; BM 1997, Remarks 9.1
(blueprint: lem-trf-extended-hilbert-local-upper-bound).

Proof: Step 1 uses `lem-weil-pbc-lft-affine-pairs` to make the affine section ring finite type
and `lem-weil-pbc-finite-type-algebra-noetherian` to make it Noetherian. Apply
`lem-sc-noetherian-finite-module-finite-presentation` and the finite-free presentation in
`def-sc-finitely-presented-module`. Step 2 tensors this right exact presentation with the
residue field (`lem-weil-pbc-tensor-right-exact`). Quotient dimension plus matrix rank equals
the number of rows (`lem-trf-vector-space-quotient-dimension`, `def-weil-matrix-rank`). Thus a
bound b requires rank at least v-b. Descend from a maximal nonzero minor by Laplace expansion
to obtain a minor of that size. Step 3: determinants commute with residue evaluation, so their
nonvanishing defines basic opens. A negative bound gives the empty set; a bound at least v
uses the empty determinant 1. Unavailable positive minors give the empty union.
-/
theorem extendedHilbert_presentation_loci
    {k : Type u} [Field k] [CharZero k] (U : Scheme.{u})
    [U.Over (Spec (CommRingCat.of k))]
    [Smooth (U ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k))]
    (U₀ : U.Opens) (hU₀ : IsAffineOpen U₀)
    (M : ModuleCat.{v} Γ(U, U₀)) (hM : Module.Finite Γ(U, U₀) M) :
    Module.FinitePresentation Γ(U, U₀) M ∧
    ∃ (m n : ℕ) (B : Matrix (Fin n) (Fin m) Γ(U, U₀))
      (π : (Fin n → Γ(U, U₀)) →ₗ[Γ(U, U₀)] M),
      Function.Surjective π ∧ Function.Exact B.mulVecLin π ∧
      ∀ b : ℤ,
        IsOpen {y : U₀ | (Module.finrank (U.residueField y.val)
          ((ModuleCat.extendScalars (U.evaluation U₀ y.val y.property).hom).obj M) : ℤ) ≤ b} ∧
        {y : U₀ | (Module.finrank (U.residueField y.val)
          ((ModuleCat.extendScalars (U.evaluation U₀ y.val y.property).hom).obj M) : ℤ) ≤ b} =
        {y : U₀ | 0 ≤ b ∧ ∃ (rows : Fin (n - b.toNat) ↪ Fin n)
          (cols : Fin (n - b.toNat) ↪ Fin m),
          U.evaluation U₀ y.val y.property (B.submatrix rows cols).det ≠ 0} := by
  sorry

/-- A finite list of bad values supplies finitely many witnessing degrees. Their dimension
sublevels cut out exactly the pointwise bounded locus, which also gives the lexicographic bound.
Additional finitely many bounds holding at the center can be imposed simultaneously, including
a finite set of degrees separating every pair of local values.

Source: BM 1997, Remarks 9.1 and Lemma 9.3; agent finite-witness refinement, DAG steps 4--5
(blueprint: lem-trf-extended-hilbert-local-upper-bound).

Proof: Apply steps 1--3, recorded by `extendedHilbert_presentation_loci`, to every realizing
module. For each value h not pointwise bounded by H_a, choose Q(h) with h(Q(h)) > H_a(Q(h)).
Intersect the finitely many open sublevels H_y(Q(h)) ≤ H_a(Q(h)). The center belongs to each.
A point failing any degree bound has a bad value h=H_y and fails its chosen test, a
contradiction. Conversely all degree bounds imply all chosen tests. Thus the intersection is
exactly the bounded locus; with no bad values it is U₀. At the least differing degree,
pointwise comparison gives lexicographic comparison. Every further bound b(q) ≥ H_a(q)
already contains this locus. Finally choose one distinguishing degree for each distinct pair
in the finite set of values. This is a finite set of degrees, not an infinite intersection.
-/
theorem extendedHilbert_local_upper_bound
    {k : Type u} [Field k] [CharZero k] (U : Scheme.{u}) [IsAffine U]
    [U.Over (Spec (CommRingCat.of k))]
    [Smooth (U ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k))]
    {d : ℕ} (c : MvPolynomial (Fin d) k →+* Γ(U, ⊤))
    (hc : c.comp MvPolynomial.C = (U ↘ Spec (CommRingCat.of k)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
    [Etale (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c))]
    (I : U.IdealSheafData) (a : I.subscheme)
    (T : ∀ y : U, Γ(U, ⊤) →+* MvPowerSeries (Fin d) (U.residueField y))
    (hT : ∀ y : U, isTaylorMap c (U.Γevaluation y).hom (T y))
    (H : U → ℕ → ℕ)
    (hH : ∀ (y : U) (q : ℕ), H y q = Module.finrank (U.residueField y)
      (MonomialDiagram.truncation (taylorIdeal (RingHom.ker I.subschemeι.appTop.hom) (T y)) q))
    (U₀ : U.Opens) (hU₀ : IsAffineOpen U₀) (ha : I.subschemeι a ∈ U₀)
    (ℋ : Finset (ℕ → ℕ)) (hℋ : (ℋ : Set (ℕ → ℕ)) = H '' (U₀ : Set U))
    (M : ℕ → ModuleCat.{v} Γ(U, U₀))
    (hM : ∀ q : ℕ, Module.Finite Γ(U, U₀) (M q))
    (hdim : ∀ (y : U) (hy : y ∈ U₀) (q : ℕ), H y q =
      Module.finrank (U.residueField y)
        ((ModuleCat.extendScalars (U.evaluation U₀ y hy).hom).obj (M q))) :
    ∃ Q : (ℕ → ℕ) → ℕ,
      (∀ h ∈ ℋ, (¬ ∀ q : ℕ, h q ≤ H (I.subschemeι a) q) →
        H (I.subschemeι a) (Q h) < h (Q h)) ∧
      ∃ V : U.Opens, I.subschemeι a ∈ V ∧ V ≤ U₀ ∧
        (∀ y : U, y ∈ V ↔ y ∈ U₀ ∧ ∀ h ∈ ℋ,
          (¬ ∀ q : ℕ, h q ≤ H (I.subschemeι a) q) → H y (Q h) ≤ H (I.subschemeι a) (Q h)) ∧
        (∀ y : U, y ∈ V ↔ y ∈ U₀ ∧ ∀ q : ℕ, H y q ≤ H (I.subschemeι a) q) ∧
        (∀ y ∈ V, HilbertSamuel.le (H y) (H (I.subschemeι a))) ∧
        (∀ (E : Finset ℕ) (b : ℕ → ℕ), (∀ q ∈ E, H (I.subschemeι a) q ≤ b q) →
          ∀ y ∈ V, ∀ q ∈ E, H y q ≤ b q) ∧
        ∃ E : Finset ℕ, ∀ h ∈ ℋ, ∀ h' ∈ ℋ,
          h ≠ h' → ∃ q ∈ E, h q ≠ h' q := by
  sorry

/-- The Taylor functions vanish off X and locally satisfy the finite-value and finite-module
hypotheses, with the specified principal-parts modules of X, extended along its closed immersion.
All d variables are kept, without a closed-point or reducedness assumption.

Source: BM 1997, Remarks 9.1, Lemma 9.3; DAG step 6
(blueprint: lem-trf-extended-hilbert-local-upper-bound).

Proof: Use `lem-trf-jet-diagram-hilbert-control`: the complementary-monomial count turns its
locally finite diagrams into finitely many functions. Shrink to an affine neighbourhood.
For R=O(U₀), A=R/I, the diagonal module P^q_{A/k} is finite and its residue fibre at every
point of X agrees with the full-variable Taylor quotient. Restrict scalars along R→A; the
same generators remain finite, and Noetherianity gives finite presentation. Outside X choose
f in the ideal with nonzero residue. It annihilates the restricted module and acts invertibly
on the residue field, so the fibre vanishes. Its Taylor series has nonzero constant term and
is a unit by the formal geometric series, so the Taylor quotient also vanishes there. These
arguments include nonclosed points, zero and unit ideals, q=0 and d=0.
-/
theorem extendedHilbert_principal_parts_realization
    {k : Type u} [Field k] [CharZero k] (U : Scheme.{u}) [IsAffine U]
    [U.Over (Spec (CommRingCat.of k))]
    [Smooth (U ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k))]
    {d : ℕ} (c : MvPolynomial (Fin d) k →+* Γ(U, ⊤))
    (hc : c.comp MvPolynomial.C = (U ↘ Spec (CommRingCat.of k)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
    [Etale (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c))]
    (I : U.IdealSheafData)
    (T : ∀ y : U, Γ(U, ⊤) →+* MvPowerSeries (Fin d) (U.residueField y))
    (hT : ∀ y : U, isTaylorMap c (U.Γevaluation y).hom (T y))
    (H : U → ℕ → ℕ)
    (hH : ∀ (y : U) (q : ℕ), H y q = Module.finrank (U.residueField y)
      (MonomialDiagram.truncation (taylorIdeal (RingHom.ker I.subschemeι.appTop.hom) (T y)) q)) :
    (∀ y : U, y ∉ Set.range I.subschemeι → H y = 0) ∧
    ∀ a : I.subscheme, ∃ U₀ : U.Opens, IsAffineOpen U₀ ∧ I.subschemeι a ∈ U₀ ∧
      (H '' (U₀ : Set U)).Finite ∧
      ∀ q : ℕ,
        Module.Finite Γ(U, U₀)
          (closedPrincipalParts k Γ(U, U₀)
            (((U.presheaf.map (homOfLE le_top).op).hom.comp c).comp MvPolynomial.C)
            (I.idealOfOpens U₀) q) ∧
        Module.FinitePresentation Γ(U, U₀)
          (closedPrincipalParts k Γ(U, U₀)
            (((U.presheaf.map (homOfLE le_top).op).hom.comp c).comp MvPolynomial.C)
            (I.idealOfOpens U₀) q) ∧
        ∀ (y : U) (hy : y ∈ U₀), H y q = Module.finrank (U.residueField y)
          ((ModuleCat.extendScalars (U.evaluation U₀ y hy).hom).obj
            (closedPrincipalParts k Γ(U, U₀)
              (((U.presheaf.map (homOfLE le_top).op).hom.comp c).comp MvPolynomial.C)
              (I.idealOfOpens U₀) q)) := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
