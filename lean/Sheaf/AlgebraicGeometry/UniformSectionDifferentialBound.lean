module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Module.Torsion.Basic
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.AlgebraicGeometry.StrictHenselizationDVR
import Sheaf.RingTheory.FiniteProjectiveOfStandardCover
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Uniform bounds for section differential defects

Source: Bosch--Lutkebohmert--Raynaud, Neron Models, Section 3.3, Proposition 3,
printed pages 66--67 (blueprint: lem-sfb-uniform-section-differential-bound).

The section module is constructed from the relative differential sheaf and tensor pullback.
The theorem bounds the length of its torsion uniformly over all strict henselian sections.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual A-module of global sections of the pullback of relative differentials
along `a : Spec A → X`. Scalars are restricted through the canonical isomorphism
`A → Γ(Spec A, O)`, so the torsion and length below are taken over A itself.
Source: BLR, Neron Models, Section 3.3, definition preceding Lemma 1, printed page 65
(blueprint: lem-sfb-uniform-section-differential-bound). -/
noncomputable def sectionDifferentialModule {R A : Type u} [CommRing R] [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (a : Spec (.of A) ⟶ X) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).obj
    (ModuleCat.of _ Γ((Scheme.Modules.tensorPullback a).obj f.relativeDifferentials, ⊤))

/-- The torsion lengths of relative differentials at all strict henselian sections
of a flat, finite-type, generically smooth model over a DVR have a common finite bound.
No constant generic dimension or nonempty set of sections is required.

Source: BLR, Neron Models, Section 3.3, Proposition 3, printed pages 66--67
(blueprint: lem-sfb-uniform-section-differential-bound).

Proof (the node's module-theoretic argument):
1. A DVR R is a Noetherian PID (lem-weil-pbc-pid-noetherian-normal). Identify the
   algebraic strict henselization A with the geometric strict local ring by
   lem-exc-affine-strict-local-ring-comparison. By lem-sc-strict-henselization-dvr,
   A is a DVR and R → A is injective. The image t of a uniformizer pi is nonzero;
   R[1/pi] is the fraction field K. We do not require t to be a uniformizer of A.
2. Finite type gives a finite affine cover (def-weil-finite-type-morphism).
   Every section factors through a chart containing the image of the closed point:
   every point of a local spectrum generalizes its closed point.
3. On a chart Spec B, M = Omega(B/R) is finite by
   lem-trf-relative-differential-sheaf-base-change. B is Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian, so M is finitely presented by
   lem-sc-noetherian-finite-module-finite-presentation. Choose a surjection q : B^m → M.
4. Put C = B[1/pi], P = M[1/pi]. Differential base change and
   lem-weil-pbc-localization-tensor identify P with Omega(C/K). Smoothness and
   lem-ag-smooth-relative-differentials-finite-locally-free give finite free principal
   charts for P. Take a finite principal cover using
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact; by
   lem-sc-affine-standard-cover-finite-projective, P is projective, even with varying rank.
5. Split the localized q by projectivity (def-weil-pbc-projective-module).
   Localization is flat (lem-weil-pbc-localization-flat), so
   lem-weil-pbc-flat-base-change-hom-finitely-presented and
   lem-weil-pbc-localization-tensor express the splitting as h_pi/pi^b for
   h : M → B^m. Fractions combine over a common power, without finiteness of Hom.
   Thus (qh - pi^b id)_pi = 0.
6. Clear the remaining denominators on the finite chosen generators of M using
   def-weil-pbc-module-localization-away. For some d, u = pi^d h and N = b+d satisfy
   qu = pi^N id_M. These choices precede the choice of section.
7. Pulling back a section yields V_a = A tensor_B M by
   lem-weil-pbc-module-pullback-affine-sections. Base-changing q and u gives
   q_A u_A = t^N id (def-weil-module-base-change). The free module A^m is torsion-free,
   so u_A kills torsion and hence t^N kills the torsion submodule T_a of V_a.
8. Apply lem-sfb-pid-submodule-smith-bases to ker(q_A) inside A^m. The coordinate
   quotient decomposes V_a into a free part and at most m cyclic torsion summands.
   Thus T_a has at most m generators, including m = 0 and unit Smith coefficients.
9. A is Noetherian of dimension one (lem-weil-pbc-pid-noetherian-normal and
   lem-sc-dvr-dimension-one). Since t^N is a nonzerodivisor,
   lem-weil-pbc-dim-le-one-principal-quotient-finite-length gives finite length L
   for A/(t^N). There is a surjection (A/(t^N))^r → T_a with r ≤ m.
   By lem-weil-pbc-length-additive-short-exact, length(T_a) ≤ r L ≤ m L.
   If N = 0 both A/(t^N) and T_a vanish.
10. Take the maximum of these finitely many chart bounds and zero. Each section
    factors through a chart and its pullback is unchanged there. The empty scheme
    and an empty set of sections are covered by c = 0. -/
theorem exists_uniform_section_differential_bound
    (R K ksep A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field ksep] [Algebra (IsLocalRing.ResidueField R) ksep]
    [IsSepClosure (IsLocalRing.ResidueField R) ksep]
    [Algebra R ksep] [IsScalarTower R (IsLocalRing.ResidueField R) ksep]
    [CommRing A] [Algebra R A]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} R ksep A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    ∃ c : ℕ, ∀ (a : Spec (.of A) ⟶ X),
      a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      Module.length A (Submodule.torsion A (f.sectionDifferentialModule a)) ≤ (c : ℕ∞) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
