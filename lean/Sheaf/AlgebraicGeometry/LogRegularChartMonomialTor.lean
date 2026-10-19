/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.GroupTheory.Torsion
import Sheaf.TraceFormula.KatoTorIndependenceChart
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.RingTheory.Flat.TorsionFree
import Sheaf.RingTheory.MonomialModuleTorDevissage

/-!
# Monomial quotient Tor vanishing over a log regular chart

Source: ILO, Travaux de Gabber, Exposé X 1.3(vii), printed p.140, and the proof
of Lemma 1.5, printed pp.141--142 (blueprint: lem-per-log-regular-chart-monomial-tor).

The multiplicative notation for the fs monoids is Mathlib's convention: the monomial
`single p 1` is the paper's z^p. The helper below expands the two Tor expressions
with their prescribed scalar maps. Its tensor product is literally A tensor_C R,
with the R-action induced by the canonical right inclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The two Tor vanishings for C → A, C → R and the quotient R/I: over C, and over R
with first argument A tensor_C R. All scalar structures are induced by the displayed
ring maps, and the R-action on the tensor product is the canonical right inclusion.
This is an expansion of the conclusion, not an additional geometric hypothesis.
Source: ILO X 1.3(vii) and Lemma 1.5, pp.140--142
(blueprint: lem-per-log-regular-chart-monomial-tor). -/
noncomputable def chartQuotientTorVanishes
    {C A R : Type u} [CommRing C] [CommRing A] [CommRing R]
    (a : C →+* A) (r : C →+* R) (I : Ideal R) (i : ℕ) : Prop :=
  letI : Algebra C A := a.toAlgebra
  letI : Algebra C R := r.toAlgebra
  IsZero (((Tor' (ModuleCat.{u} C) i).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of A A))).obj
      ((ModuleCat.restrictScalars r).obj (ModuleCat.of R (R ⧸ I)))) ∧
  IsZero (((Tor' (ModuleCat.{u} R) i).obj
    ((ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight : R →ₐ[C] A ⊗[C] R).toRingHom).obj
        (ModuleCat.of (A ⊗[C] R) (A ⊗[C] R)))).obj (ModuleCat.of R (R ⧸ I)))

/-- Every monomial quotient in a sharp log regular chart has vanishing positive Tor,
both over the base chart ring and after its prescribed base change. The assertion
also includes polynomial variables and killing any subset of them.
Source: ILO X 1.3(vii), p.140, and proof of Lemma 1.5, pp.141--142
(blueprint: lem-per-log-regular-chart-monomial-tor).

Proof (the four steps of the node):
1. Put D = Z[Q]. Identify the geometric stalk A with the affine-neighbourhood
strict henselization by lemma-weil-pbc-affine-neighbourhood-cofinal and
lem-weil-pbc-colimit-initial-full-subcategory. The comparison commutes with ring
and log germs. Apply lem-trf-kato-tor-independence-chart to every monoid ideal of Q;
lem-weil-pbc-tor-symmetry gives Tor^D_1(A,D/Z[I]) = 0. Ordinary flatness is not used.
2. For the first assertion put E = P and H = J. For the polynomial assertion put
E = P times N^s and let H consist of the monomials with P-coordinate in J or a
positive coordinate in one of the killed variables. The map Q → E^gp is injective.
Apply lem-per-monomial-module-tor-devissage to T = E, U = H, M = A, using step 1.
It gives Tor^D_i(A,Z[E]/Z[H]) = 0 for i > 0. Use U empty also to obtain the same
vanishing for Z[E]. The cases H empty and H = E are included.
3. The localized cyclotomic coefficient ring is Z-torsion-free, hence Z-flat by
lem-weil-pbc-pid-torsion-free-module-flat. Extend a D-free resolution of Z[E]/Z[H]
by tensoring with Lambda; lem-weil-pbc-flat-tensor-exact preserves exactness and
its terms become C-free. The termwise identification
A tensor_C (Lambda tensor_Z F_n) = A tensor_D F_n, and Tor symmetry, yield the
positive Tor^C vanishings for Lambda[E]/(H) and Lambda[E].
4. Tensor a C-free resolution G of A with Lambda[E]. Its positive homology vanishes
by step 3, so it resolves B_E = A tensor_C Lambda[E] by Lambda[E]-free modules.
Tensoring it with V = Lambda[E]/(H) gives the complex G tensor_C V by associativity;
step 3 gives zero positive homology. For E = P times N^s, the basis bijection
z^(p,e) → z^p y^e identifies the ring with R' and the ideal with (J,y_j : j in L).
This proves both polynomial vanishings, including s = 0 and empty or full L.
-/
theorem FineSaturatedLogScheme.monomialQuotient_tor_vanishes
    (S : FineSaturatedLogScheme.{u}) (_hS : S.IsLogRegular)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S.scheme)
    (Q : Type u) [CommMonoid Q] (_hQ : IsFineSaturatedMonoid Q)
    (_hsharp : ∀ q : Q, IsUnit q → q = 1)
    (W : S.scheme.Etale) (w : (Scheme.pointSmallEtale x).fiber.obj W)
    (c : Q →* S.logStructure.monoidSheaf.obj.obj (op W))
    (_hc : S.logStructure.IsChart W c)
    (e : Q ≃* S.logStructure.characteristic x)
    (_he : ∀ q : Q, e q = Associates.mk
      (S.logStructure.toEtalePrelogStructure.germ x W w (c q)))
    (N : ℕ) (_hN : 0 < N)
    (Λ : Type u) [CommRing Λ] [Algebra (CyclotomicRing N ℤ ℚ) Λ]
    (M : Submonoid (CyclotomicRing N ℤ ℚ)) [_hΛ : IsLocalization M Λ]
    (_hNΛ : IsUnit (N : Λ)) [Algebra Λ (strictLocalRing S.scheme x)]
    (_hNA : IsUnit (N : strictLocalRing S.scheme x))
    (ζ : CyclotomicRing N ℤ ℚ) (_hζ : IsPrimitiveRoot ζ N)
    (_hζA : IsPrimitiveRoot
      (algebraMap Λ (strictLocalRing S.scheme x)
        (algebraMap (CyclotomicRing N ℤ ℚ) Λ ζ)) N)
    (P : Type u) [CommMonoid P] (_hP : IsFineSaturatedMonoid P) (γ : Q →* P)
    (_hγ : Function.Injective
      (Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := P)).comp γ)))
    (_hfinite : Finite (CommGroup.torsion
      (Algebra.GrothendieckGroup P ⧸
        (Algebra.GrothendieckGroup.lift
          ((Algebra.GrothendieckGroup.of (M := P)).comp γ)).range)))
    (_horder : IsUnit (Nat.card (CommGroup.torsion
      (Algebra.GrothendieckGroup P ⧸
        (Algebra.GrothendieckGroup.lift
          ((Algebra.GrothendieckGroup.of (M := P)).comp γ)).range)) :
            strictLocalRing S.scheme x)) :
    (∀ (J : Set P), (∀ j ∈ J, ∀ p : P, j * p ∈ J) → ∀ i : ℕ, 0 < i →
      chartQuotientTorVanishes
        (MonoidAlgebra.lift Λ (strictLocalRing S.scheme x) Q
          ((S.logStructure.toEtalePrelogStructure.stalkAlpha x).comp
            ((S.logStructure.toEtalePrelogStructure.germ x W w).hom.comp c))).toRingHom
        (MonoidAlgebra.mapDomainRingHom Λ γ)
        (Ideal.span ((fun p : P ↦ MonoidAlgebra.single p (1 : Λ)) '' J)) i) ∧
    (∀ (s : ℕ) (J : Set P), (∀ j ∈ J, ∀ p : P, j * p ∈ J) →
      ∀ (L : Set (Fin s)) (i : ℕ), 0 < i →
      chartQuotientTorVanishes
        (MonoidAlgebra.lift Λ (strictLocalRing S.scheme x) Q
          ((S.logStructure.toEtalePrelogStructure.stalkAlpha x).comp
            ((S.logStructure.toEtalePrelogStructure.germ x W w).hom.comp c))).toRingHom
        ((MvPolynomial.C : MonoidAlgebra Λ P →+* MvPolynomial (Fin s) (MonoidAlgebra Λ P)).comp
          (MonoidAlgebra.mapDomainRingHom Λ γ))
        (Ideal.map MvPolynomial.C
          (Ideal.span ((fun p : P ↦ MonoidAlgebra.single p (1 : Λ)) '' J)) ⊔
            Ideal.span (MvPolynomial.X '' L)) i) := by
  sorry

end AlgebraicGeometry
