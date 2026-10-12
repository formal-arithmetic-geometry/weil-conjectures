module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.CohomologyPowersIdealReesFinite
import Sheaf.Paper.PQFCohomology

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry

/-- Image estimate for the transition maps, for every sufficiently large choice of c.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OA, proof of (1) and (2).
(blueprint: lem-weil-pbc-cohomology-powers-ideal-application-image)

Proof: Write M_r = H^q(X, J^r F) with the A-module structure in the statement.
The Rees finiteness theorem gives M = direct sum M_r finite over B = Rees(I), with
multiplication induced by scalar multiplication on the sheaves. The inclusions into F
are monic. Hence the assumed factorization identifies i with the canonical inclusions,
and cancellation of these monomorphisms proves that transition maps compose, commute
with the homogeneous products, and send the product by a in I^k to scalar multiplication
by a after transition from degree r+k to r. Applying cohomology preserves these identities.
Replace a finite generating set of M by all its nonzero homogeneous components and let
c0 bound their degrees (take c0 = 0 when M = 0). For c >= c0 and r >= c, comparing degree
r components of an expression in the generators, and factoring
I^(r-d) = I^(r-c) I^(c-d), shows M_r = B_(r-c) M_c.
Fix n,m with n+m >= c. If n >= c, this equality and the same factorization give
M_(n+m) = B_m M_n; transition takes each such product into I^m M_n.
If n < c, write k = n+m-c = m-(c-n). Generate M_(n+m) as B_k M_c and commute
transition with multiplication through M_c -> M_n. The resulting image lies in I^k M_n.
Additivity handles each finite sum. These two cases give the asserted exponent.
The argument works for every c >= c0, including m = 0, n = 0, and c = 0. -/
theorem cohomology_powers_ideal_image_bound
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
        (∀ (n m : ℕ), c ≤ n + m →
          LinearMap.range ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map
              (i (n + m) n (Nat.le_add_right n m)))).hom ≤
            I ^ (m - (c - n)) • (⊤ : Submodule A ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
                ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
                  (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))))) := by
  sorry

end AlgebraicGeometry
