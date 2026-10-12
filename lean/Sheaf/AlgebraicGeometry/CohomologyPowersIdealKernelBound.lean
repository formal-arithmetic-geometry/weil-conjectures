module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.CohomologyPowersIdealReesFinite
import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry

/-- Kernel estimate for the transition maps, for every sufficiently large choice of c.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OA, proof of (3).
(blueprint: lem-weil-pbc-cohomology-powers-ideal-application-kernel)

Proof: Set M_r = H^q(X, J^r F), B = Rees(I), and K_r = ker(M_r -> M_0).
Rees finiteness makes M = direct sum M_r a finite B-module. Cancellation of the monic
inclusions into F identifies the assumed i with the canonical transition maps and proves
composition and compatibility with homogeneous multiplication. Apply cohomology to get
these identities on M. Compatibility implies K = direct sum K_r is a B-submodule:
for a in I^k and y in K_r, the image of a*y in M_0 factors through a*(image of y in M_0),
which is zero. As B is Noetherian, K is finite. Replace its finite generators by their
nonzero homogeneous components y_j in K_(d_j) and let c0 bound all d_j, taking zero for
the empty set. Degree n components express every x in K_n as a sum b_j*y_j with
b_j in I^(n-d_j). For c >= c0 and n >= c, transition from n to n-d_j sends this term
to b_j*(image of y_j in M_0) = 0. Because d_j <= c, it therefore also vanishes after
transition to n-c. This proves K_n is contained in ker(M_n -> M_(n-c)).
The reverse inclusion follows from composition of M_n -> M_(n-c) -> M_0.
All c >= c0 work; if K = 0 the empty generating set proves the same assertion, and
at n = c the two maps have the same target and coincide. -/
theorem cohomology_powers_ideal_kernel_bound
    (A : Type v) [CommRing A] [IsNoetherianRing A] {X : Scheme.{v}}
    (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (q : ℕ)
    (i : ∀ (k n : ℕ), n ≤ k →
      (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι k).2 F ⟶
        Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))
    (hi : ∀ (k n : ℕ) (h : n ≤ k),
      i k n h ≫ Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F =
        Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι k).2 F) :
    ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c →
(∀ n : ℕ, c ≤ n →
          LinearMap.ker ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map (i n 0 (Nat.zero_le n)))).hom =
          LinearMap.ker ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map
              (i n (n - c) (Nat.sub_le n c)))).hom) := by
  sorry

end AlgebraicGeometry
