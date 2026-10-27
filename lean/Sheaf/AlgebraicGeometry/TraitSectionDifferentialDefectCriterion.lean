/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length
import Mathlib.RingTheory.PrincipalIdealDomain
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.AlgebraicGeometry.StrictHenselizationDVR
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.SmoothAtPointDifferentialCriterion

/-!
# Differential defect of a section over a trait

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §3.3, opening paragraph and Lemma 1,
printed p.65 (blueprint: lem-sfb-trait-section-differential-defect-criterion).

The section module and its torsion length use the actual tensor pullback and global sections.
The theorem is local on the image of the closed point, without a quasi-compactness hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Global sections of the pullback of relative differentials along an affine section,
with the canonical scalar action through `A ≅ Γ(Spec A, ⊤)`.
Source: BLR, Néron Models, §3.3 opening paragraph, printed p.65
(blueprint: lem-sfb-trait-section-differential-defect-criterion). -/
noncomputable def traitSectionDifferentials {R A : Type u} [CommRing R] [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (a : Spec (.of A) ⟶ X) : ModuleCat.{u} A :=
  (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
    ((Scheme.Modules.tensorPullback a).obj f.relativeDifferentials)

/-- The differential defect is the length of the torsion submodule of the actual section
module. Over a domain the non-zero-divisors used in `Submodule.torsion` are precisely
its nonzero elements. The value is in `ℕ∞`; the criterion below proves it finite.
Source: BLR, Néron Models, §3.3 opening paragraph, printed p.65
(blueprint: lem-sfb-trait-section-differential-defect-criterion). -/
noncomputable def traitSectionDifferentialDefect {R A : Type u} [CommRing R] [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (a : Spec (.of A) ⟶ X) : ℕ∞ :=
  Module.length A (Submodule.torsion A (traitSectionDifferentials f a))

/-- The strict henselization is a DVR, the section's differential module is finite, its
torsion has finite length, and that length vanishes precisely at a smooth closed image.
Source: BLR, Néron Models, §3.3 opening paragraph and Lemma 1, printed p.65;
Stacks Tags 0AP3, 01UT, 01V0, 01V2, 01V9, 02FZ, 02G1
(blueprint: lem-sfb-trait-section-differential-defect-criterion).

Proof:
1. A DVR is Noetherian (lem-weil-pbc-pid-noetherian-normal). Identify the chosen
   algebraic strict henselization with the geometric strict local ring using
   lem-exc-affine-strict-local-ring-comparison. By lem-sc-strict-henselization-dvr,
   A is a DVR and R → A is flat, local and injective. Thus the generic section image
   lies in the generic fibre. An affine neighbourhood of the closed image contains
   the entire section: its inverse image is an open of a local spectrum containing
   the closed point, hence is the whole spectrum.
2. On this affine neighbourhood Spec B, relative differentials are the tilde of
   Ω[B/R], finite on the differentials of finitely many algebra generators
   (lem-trf-relative-differential-sheaf-base-change). The affine pullback formula
   (lem-weil-pbc-module-pullback-affine-sections) identifies the section module with
   Ω[B/R] ⊗[B] A. These generators therefore give finite generation over A.
   Base change identifies its generic and special fibres with the differential fibres.
3. Present the section module as a quotient of A^n. Apply
   lem-sfb-pid-submodule-smith-bases to the kernel and A^n. The coordinate quotient
   identifies the result with a free module plus finitely many A/(c_i), c_i ≠ 0.
   Its torsion is exactly the sum of those cyclic factors.
4. A has dimension one (lem-sc-dvr-dimension-one), and each A/(c_i) has finite length
   by lem-weil-pbc-dim-le-one-principal-quotient-finite-length. Add lengths using
   lem-weil-pbc-length-additive-short-exact. Length zero means the torsion is zero
   (def-weil-pbc-module-length), equivalently the section module is free.
5. Smoothness at the closed image gives a neighbourhood with free differentials by
   lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension. The whole section
   factors through it, so its differential module is free and the defect is zero.
6. Conversely, zero defect makes that module A^d. The generic fibre is smooth, so
   lem-weil-pbc-smooth-over-field-dimension-differentials identifies d with its local
   fibre dimension at the generic image. Base change to the residue field gives
   differential-fibre dimension d at the closed image too. Field extension preserves
   the cardinality of a finite basis; neither image needs rational residue field.
7. The generic image generalizes the closed image. Apply
   lem-weil-pbc-local-fibre-dimension-open to bound d by the special local fibre dimension.
8. Lift a basis of the special differential fibre. By lem-weil-pbc-nakayama-local-generators
   its d lifts generate the differential stalk. The base is locally Noetherian, so
   pqf-lem-lft-fp-locnoeth gives local finite presentation. Flatness is assumed; now
   lem-trf-smooth-at-point-differential-criterion gives smoothness at the closed image.
9. All arguments concern this one section and one affine neighbourhood. They require
   neither quasi-compactness of X nor a uniform bound over all sections. The zero module,
   zero rank, empty torsion sum and unit Smith coefficients are included. -/
theorem trait_section_differential_defect_criterion
    (R K ksep A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field ksep] [Algebra (IsLocalRing.ResidueField R) ksep]
    [IsSepClosure (IsLocalRing.ResidueField R) ksep]
    [Algebra R ksep] [IsScalarTower R (IsLocalRing.ResidueField R) ksep]
    [CommRing A] [Algebra R A]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} R ksep A)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) [Flat f] [LocallyOfFiniteType f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (a : Spec (.of A) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ (_ : IsDomain A) (_ : IsDiscreteValuationRing A),
      Module.Finite A (traitSectionDifferentials f a) ∧
      traitSectionDifferentialDefect f a ≠ ⊤ ∧
      (traitSectionDifferentialDefect f a = 0 ↔
        ∃ U : X.Opens, a (IsLocalRing.closedPoint A) ∈ U ∧ Smooth (U.ι ≫ f)) := by
  sorry

end AlgebraicGeometry
