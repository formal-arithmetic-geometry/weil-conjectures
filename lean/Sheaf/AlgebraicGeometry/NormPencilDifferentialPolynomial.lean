/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # The differential of a pencil and its polynomial nonvanishing locus

Source: Stacks Project, Tags 00RV, 02G1, 02KH; the local-frame and polynomial argument
in lem-sfb-separating-pair-open, steps 11--13
(blueprint: lem-sfb-norm-pencil-differential-polynomial).

The auxiliary declarations only spell out the objects and clauses of this statement.
Scalar extension uses the explicit tensor pullback and its actual section `1 ⊗ s`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Sections with scalars restricted along the specified structure morphism.
Source: Stacks, Tag 02KH (blueprint: lem-sfb-norm-pencil-differential-polynomial). -/
noncomputable def pencilSections {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (M : X.Modules) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (f.specStructureMap ⊤).hom).obj (M.val.obj (op ⊤))

/-- The target sheaf `Ω¹ ⊗ M ⊗ M`, parenthesized as `Ω¹ ⊗ (M ⊗ M)`.
Source: Stacks, Tag 02G1 (blueprint: lem-sfb-norm-pencil-differential-polynomial). -/
noncomputable abbrev pencilTarget {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) :
    X.Modules :=
  f.relativeDifferentials ⊗ (M ⊗ M)

/-- The local formula is required in every frame, so it includes frame independence.
Source: the local cancellation argument in separating-pair-open, step 11
(blueprint: lem-sfb-norm-pencil-differential-polynomial). -/
def PencilLocalFormula {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (δ : pencilSections f M → pencilSections f M → pencilSections f (pencilTarget f M)) :
    Prop :=
  ∀ (U : X.Opens) (e : Γ(M, U)), IsFreeGenerator e →
    ∀ (a b : Γ(X, U)) (s t : pencilSections f M),
      M.presheaf.map (homOfLE le_top).op s = a • e →
      M.presheaf.map (homOfLE le_top).op t = b • e →
      (pencilTarget f M).presheaf.map (homOfLE le_top).op (δ s t) =
        tmulSection (M := f.relativeDifferentials) (N := M ⊗ M) (U := U)
          (b • f.relativeDifferentialsDerivation.d (X := op U) a -
            a • f.relativeDifferentialsDerivation.d (X := op U) b)
          (tmulSection (M := M) (N := M) (U := U) e e)

/-- The curve after scalar extension to an arbitrary algebra, including nonreduced algebras.
Source: Stacks, Tag 02KH (blueprint: lem-sfb-norm-pencil-differential-polynomial). -/
noncomputable abbrev pencilCurve {F R : Type u} [CommRing F] [CommRing R] [Algebra F R]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of F)) : Scheme.{u} :=
  Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap F R)))

/-- The projection to the original curve.
Source: Stacks, Tag 02KH (blueprint: lem-sfb-norm-pencil-differential-polynomial). -/
noncomputable abbrev pencilProjection {F R : Type u} [CommRing F] [CommRing R] [Algebra F R]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of F)) : pencilCurve (R := R) f ⟶ C :=
  pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F R)))

/-- The structure map of the scalar-extended curve.
Source: Stacks, Tag 02KH (blueprint: lem-sfb-norm-pencil-differential-polynomial). -/
noncomputable abbrev pencilStructure {F R : Type u} [CommRing F] [CommRing R] [Algebra F R]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of F)) : pencilCurve (R := R) f ⟶ Spec (.of R) :=
  pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F R)))

/-- The line bundle pulled back by the explicit tensor construction.
Source: Stacks, Tag 0095 (blueprint: lem-sfb-norm-pencil-differential-polynomial). -/
noncomputable abbrev pencilModule {F R : Type u} [CommRing F] [CommRing R] [Algebra F R]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of F)) (M : C.Modules) :
    (pencilCurve (R := R) f).Modules :=
  (tensorPullback (pencilProjection (R := R) f)).obj M

/-- All scalar-extension comparisons, normalized on actual sections and differentials.
The differential on the base change is characterized by the same local formula.
Source: Stacks, Tags 00RV, 02KH; separating-pair-open, steps 11--12
(blueprint: lem-sfb-norm-pencil-differential-polynomial). -/
structure PencilDifferentialBaseChange {F : Type u} [Field F] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of F)) (M : C.Modules)
    (δ : pencilSections f M →ₗ[F] pencilSections f M →ₗ[F]
      pencilSections f (pencilTarget f M))
    (R : Type u) [CommRing R] [Algebra F R] where
  /-- The canonical differential-sheaf comparison. -/
  omegaIso : (tensorPullback (pencilProjection (R := R) f)).obj f.relativeDifferentials ≅
    (pencilStructure (R := R) f).relativeDifferentials
  /-- Its normalization `1 ⊗ da ↦ d(1 ⊗ a)` on every open. -/
  omega_d : ∀ (U : C.Opens) (a : Γ(C, U)),
    omegaIso.hom.app (pencilProjection (R := R) f ⁻¹ᵁ U)
      (tensorPullbackSection (pencilProjection (R := R) f) f.relativeDifferentials U
        (f.relativeDifferentialsDerivation.d (X := op U) a)) =
      (pencilStructure (R := R) f).relativeDifferentialsDerivation.d
        (X := op (pencilProjection (R := R) f ⁻¹ᵁ U))
        ((pencilProjection (R := R) f).app U a)
  /-- Pullback of the whole target, using the preceding differential comparison. -/
  targetIso : (tensorPullback (pencilProjection (R := R) f)).obj (pencilTarget f M) ≅
    pencilTarget (pencilStructure (R := R) f) (pencilModule (R := R) f M)
  /-- Pure tensors fix the target comparison, rather than an arbitrary isomorphism. -/
  target_tmul : ∀ (U : C.Opens) (η : Γ(f.relativeDifferentials, U)) (s t : Γ(M, U)),
    targetIso.hom.app (pencilProjection (R := R) f ⁻¹ᵁ U)
      (tensorPullbackSection (pencilProjection (R := R) f) (pencilTarget f M) U
        (tmulSection η (tmulSection s t))) =
      tmulSection (omegaIso.hom.app (pencilProjection (R := R) f ⁻¹ᵁ U)
        (tensorPullbackSection (pencilProjection (R := R) f) f.relativeDifferentials U η))
        (tmulSection (tensorPullbackSection (pencilProjection (R := R) f) M U s)
          (tensorPullbackSection (pencilProjection (R := R) f) M U t))
  /-- The canonical comparison for the sections of `M`. -/
  sectionsM : R ⊗[F] pencilSections f M ≃ₗ[R]
    pencilSections (pencilStructure (R := R) f) (pencilModule (R := R) f M)
  /-- The canonical comparison for the sections of the differential target. -/
  sectionsQ : R ⊗[F] pencilSections f (pencilTarget f M) ≃ₗ[R]
    pencilSections (pencilStructure (R := R) f)
      (pencilTarget (pencilStructure (R := R) f) (pencilModule (R := R) f M))
  /-- Normalization of the first global-section comparison. -/
  sectionsM_tmul : ∀ (r : R) (s : pencilSections f M),
    sectionsM (r ⊗ₜ[F] s) = r •
      (@id (pencilSections (pencilStructure (R := R) f) (pencilModule (R := R) f M))
        (tensorPullbackSection (pencilProjection (R := R) f) M ⊤ s))
  /-- Normalization of the second global-section comparison. -/
  sectionsQ_tmul : ∀ (r : R) (s : pencilSections f (pencilTarget f M)),
    sectionsQ (r ⊗ₜ[F] s) = (pencilStructure (R := R) f).specStructureMap ⊤ r •
      targetIso.hom.app ⊤
      (tensorPullbackSection (pencilProjection (R := R) f) (pencilTarget f M) ⊤ s)
  /-- The relative alternating bilinear differential. -/
  differential : pencilSections (pencilStructure (R := R) f) (pencilModule (R := R) f M) →ₗ[R]
    pencilSections (pencilStructure (R := R) f) (pencilModule (R := R) f M) →ₗ[R]
      pencilSections (pencilStructure (R := R) f)
        (pencilTarget (pencilStructure (R := R) f) (pencilModule (R := R) f M))
  /-- Alternatingness includes characteristic two. -/
  alternating : ∀ s, differential s s = 0
  /-- Every frame on the base change gives the same formula. -/
  local_formula : PencilLocalFormula (pencilStructure (R := R) f)
    (pencilModule (R := R) f M) (fun s t ↦ differential s t)
  /-- The relative formula is the scalar extension of the original bilinear map. -/
  differential_tmul : ∀ (r r' : R) (s t : pencilSections f M),
    differential (sectionsM (r ⊗ₜ[F] s)) (sectionsM (r' ⊗ₜ[F] t)) =
      sectionsQ ((r * r') ⊗ₜ[F] δ s t)

/-- Coordinate polynomials of the differential for two polynomial families of sections.
Source: separating-pair-open, step 12
(blueprint: lem-sfb-norm-pencil-differential-polynomial). -/
noncomputable def pencilCoordinatePolynomials {F J Q : Type u} [Field F]
    [AddCommGroup J] [Module F J] [AddCommGroup Q] [Module F Q]
    (δ : J →ₗ[F] J →ₗ[F] Q) {N r m : ℕ} (bJ : Module.Basis (Fin N) F J)
    (bQ : Module.Basis (ULift.{u} (Fin r)) F Q)
    (a b : Fin N → MvPolynomial (ULift.{u} (Fin m)) F) :
    ULift.{u} (Fin r) → MvPolynomial (ULift.{u} (Fin m)) F :=
  fun k ↦ ∑ i, ∑ j, MvPolynomial.C (bQ.repr (δ (bJ i) (bJ j)) k) * a i * b j

/-- Polynomial specialization and the closed zero locus for every choice of bases.
Inputs `a,b` encode all sections on the polynomial parameter space by `sectionsM`.
Source: separating-pair-open, steps 12--13
(blueprint: lem-sfb-norm-pencil-differential-polynomial). -/
def PencilPolynomialLaw {F : Type u} [Field F] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of F)) (M : C.Modules)
    (δ : pencilSections f M →ₗ[F] pencilSections f M →ₗ[F]
      pencilSections f (pencilTarget f M))
    (bc : ∀ (R : Type u) [CommRing R] [Algebra F R],
      PencilDifferentialBaseChange f M δ R) : Prop :=
  ∀ (N r m : ℕ) (bJ : Module.Basis (Fin N) F (pencilSections f M))
    (bQ : Module.Basis (ULift.{u} (Fin r)) F (pencilSections f (pencilTarget f M)))
    (a b : Fin N → MvPolynomial (ULift.{u} (Fin m)) F),
    ∃ (h : ULift.{u} (Fin r) → MvPolynomial (ULift.{u} (Fin m)) F)
      (Δ : AffineSpace (ULift.{u} (Fin m)) (Spec (.of F)) ⟶
        AffineSpace (ULift.{u} (Fin r)) (Spec (.of F))),
      h = pencilCoordinatePolynomials δ bJ bQ a b ∧
      (AffineSpace.SpecIso _ (.of F)).inv ≫ Δ ≫
          (AffineSpace.SpecIso _ (.of F)).hom =
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval h).toRingHom) ∧
      IsClosed (PrimeSpectrum.zeroLocus (Set.range h)) ∧
      IsOpen (PrimeSpectrum.zeroLocus (Set.range h))ᶜ ∧
      (∀ (R : Type u) [CommRing R] [Algebra F R] (v : ULift.{u} (Fin m) → R),
        (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom) ≫
          (AffineSpace.SpecIso _ (.of F)).inv ≫ Δ =
          Spec.map (CommRingCat.ofHom
            (MvPolynomial.aeval (fun k ↦ MvPolynomial.aeval v (h k))).toRingHom) ≫
              (AffineSpace.SpecIso _ (.of F)).inv) ∧
        (bc R).differential
          ((bc R).sectionsM (∑ i, (MvPolynomial.aeval v (a i)) ⊗ₜ[F] bJ i))
          ((bc R).sectionsM (∑ i, (MvPolynomial.aeval v (b i)) ⊗ₜ[F] bJ i)) =
        (bc R).sectionsQ (∑ k, (MvPolynomial.aeval v (h k)) ⊗ₜ[F] bQ k)) ∧
      (∀ (E : Type u) [Field E] [Algebra F E] (v : ULift.{u} (Fin m) → E),
        PrimeSpectrum.comap (MvPolynomial.aeval v).toRingHom
          (⊥ : PrimeSpectrum E) ∈ (PrimeSpectrum.zeroLocus (Set.range h))ᶜ ↔
        (bc E).differential
          ((bc E).sectionsM (∑ i, (MvPolynomial.aeval v (a i)) ⊗ₜ[F] bJ i))
          ((bc E).sectionsM (∑ i, (MvPolynomial.aeval v (b i)) ⊗ₜ[F] bJ i)) ≠ 0)

/-- The local differential of a pencil is alternating, commutes with arbitrary algebra
extension, and gives a polynomial map with the stated open nonzero locus.

Source: Stacks Project, Tags 00RV, 02G1, 02KH; separating-pair-open, steps 11--13
(blueprint: lem-sfb-norm-pencil-differential-polynomial).

Proof: (1) Projectivity gives properness (lem-kun-projective-implies-proper), and finite
 type over the field gives Noetherianity (lem-weil-pbc-finite-type-over-noetherian).
(2) The integral smooth curve has relative dimension one; smooth differentials are locally
free of rank one (lem-sc-smooth-omega-finite-locally-free). Invertibility and tensor products
make M and the target coherent (pqf-lem-coherent-ft-locnoeth); proper coherent cohomology
in degree zero is finite-dimensional (lem-pc-coherent-hi).
(3) In a frame e use (b da - a db) tensor e tensor e. Replacing e by ue replaces a,b by
u⁻¹a,u⁻¹b; the two terms involving du cancel. The remaining factor u⁻² cancels u² from
the two frames. Restriction compatibility and sheaf gluing give a unique global section.
(4) Additivity and d(c)=0 for c in F give bilinearity, and identical terms cancel on the
diagonal in every characteristic.
(5) Differential base change (lem-trf-relative-differential-sheaf-base-change and
lem-weil-pbc-kahler-differentials-base-change) sends 1 tensor da to d(1 tensor a).
Tensor pullback sends the three tensor factors to their pulled-back sections, so it
carries the local formula to the same relative formula.
(6) Every F-algebra is F-flat. Properness gives quasi-compactness and quasi-separatedness
(lem-pc-separated-quasi-separated). Canonical flat base change in degree zero
(lem-pc-flat-base-change-cohom, lem-sc-flat-base-change-coherent) gives sectionsM and
sectionsQ with the pure-tensor normalizations. Bilinearity extends the pure-tensor
compatibility to arbitrary sums, and the normalized maps commute with specialization.
(7) Expand in bases of J and Q: h_k = sum c_kij a_i b_j. The polynomial ring map sending
the k-th variable to h_k defines Delta. Applying any algebra-valued point to these
finite sums gives exactly the relative differential, including the generic point with
values in F[P]. Changing bases describes the same scalar-extended Q-valued element.
(8) The simultaneous zero locus of the finitely many h_k is closed. Over every field
extension its open complement consists exactly of points with nonzero relative
differential. Empty bases give the zero ideal and empty complement; m=0 gives F itself. -/
theorem norm_pencil_differential_polynomial {F : Type u} [Field F] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of F)) [Smooth f] [IsHProjective f] [GeometricallyIntegral f]
    [IsIntegral C] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hdim : topologicalKrullDim C = 1) (M : C.Modules) [M.IsInvertible] :
    f.relativeDifferentials.IsInvertible ∧
    FiniteDimensional F (pencilSections f M) ∧
    FiniteDimensional F (pencilSections f (pencilTarget f M)) ∧
    ∃ δ : pencilSections f M →ₗ[F] pencilSections f M →ₗ[F]
        pencilSections f (pencilTarget f M),
      (∀ s, δ s s = 0) ∧ PencilLocalFormula f M (fun s t ↦ δ s t) ∧
      ∃ bc : ∀ (R : Type u) [CommRing R] [Algebra F R],
          PencilDifferentialBaseChange f M δ R,
        PencilPolynomialLaw f M δ bc := by
  sorry

end AlgebraicGeometry.Scheme.Modules
