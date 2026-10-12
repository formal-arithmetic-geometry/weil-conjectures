/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.RingTheory.Ideal.Operations
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.CohomologyPowersIdealApplication
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor

/-! # Mittag-Leffler and Artin-Rees bounds for cohomology of ideal-power quotients

Source: Stacks Project, Cohomology of Schemes, Lemma 02OB, parts (1) and (3)
(blueprint: lem-weil-pbc-ml-cohomology-powers-ideal).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For a proper scheme over a Noetherian ring, the kernel of cohomology reduction
is bounded by an ideal power and the images of reductions stabilize to the image
of the original cohomology. The last clause is the Mittag-Leffler consequence.
All objects and maps are the established module cohomology and canonical quotients.
The extended ideal is obtained by comap from the ideal sheaf on Spec A.

The kernel bound uses restriction of scalars along A ≅ Γ(Spec A) → Γ(X, O_X),
so its submodules and the ideal power act over the specified ring A.
The index op n of formalCompletionSystem denotes the positive level n + 1.

Source: Stacks Project, Cohomology of Schemes, Lemma 02OB, parts (1) and (3)
(blueprint: lem-weil-pbc-ml-cohomology-powers-ideal).

Proof:
1. Form 0 → I^n F → F → F/I^n F → 0 and the morphisms between them for k ≥ n,
   using def-weil-pbc-coherent-formal-module. The category has enough injectives
   (lem-weil-pbc-scheme-modules-enough-injectives). By pqf-def-cohomology and
   lem-weil-pbc-horseshoe-delta-functor, their long exact sequences are natural:
   H^p(I^n F) → H → M_n → H^(p+1)(I^n F) → H^(p+1)(F).
   Write iota_n, rho_n, delta_n, beta_n for these maps, and alpha_(k,n) for the
   inclusion-induced maps in degree p+1. Then delta_n tau_(k,n) = alpha_(k,n) delta_k,
   beta_k = beta_n alpha_(k,n), and the alpha maps compose.
2. Apply lem-weil-pbc-cohomology-powers-ideal-application in degrees p and p+1,
   obtaining c_p and c_(p+1), and take c = max(c_p, c_(p+1)).
3. Exactness identifies ker rho_n with im iota_n. Part (a) of that lemma with
   its n = 0 bounds this image by I^(n-c_p)H, contained in I^(n-c)H for n ≥ c.
4. Compatibility tau_(k,n) rho_k = rho_n gives im rho_n ⊆ im tau_(k,n).
5. For x ∈ M_k, exactness gives delta_k(x) ∈ ker beta_k. Part (b) of the same
   lemma in degree p+1 identifies this kernel with ker alpha_(k,k-c_(p+1)).
   If k ≥ n+c, this alpha factors through alpha_(k,n), so alpha_(k,n) delta_k(x) = 0.
   Naturality and exactness give tau_(k,n)(x) ∈ ker delta_n = im rho_n.
   This proves the reverse inclusion. Stacks' citation of 02OA(4) here uses 02OA(3).
6. For each positive n, all images with k ≥ n+c equal im rho_n, independently
   of k. This is def-weil-pbc-mittag-leffler-system, i.e. Functor.IsMittagLeffler
   of the underlying-set system. -/
theorem ml_cohomology_powers_ideal
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (I : Ideal A) (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (p : ℕ) :
    ∃ c : ℕ,
      (∀ n : ℕ, 1 ≤ n → c ≤ n →
        LinearMap.ker (((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map
          (formalModuleQuotientπ
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f) n F))).hom) ≤
          I ^ (n - c) • (⊤ : Submodule A
            ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
              ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)))) ∧
      (∀ (n k : ℕ), 1 ≤ n → ∀ h : n + c ≤ k,
        Set.range (((RingedSpace.moduleCohomology X.toRingedSpace p).map
          (formalModuleQuotientMap
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f)
            (𝟙 F) (Nat.le_trans (Nat.le_add_right n c) h))).hom) =
        Set.range (((RingedSpace.moduleCohomology X.toRingedSpace p).map
          (formalModuleQuotientπ
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f) n F)).hom)) ∧
      (formalCompletionSystem
        ((Scheme.IdealSheafData.ofIdealTop
          (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f) F ⋙
        RingedSpace.moduleCohomology X.toRingedSpace p ⋙
        forget (ModuleCat ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))).IsMittagLeffler := by
  sorry

end AlgebraicGeometry
