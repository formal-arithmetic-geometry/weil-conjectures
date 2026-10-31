/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.LocalRing.Module

import WeilConjectures.RingTheory.LocalTrivializationResidueRank
import WeilConjectures.RingTheory.SimultaneousResidueBases
import WeilConjectures.RingTheory.BasisOfMaximalResidueBases

/-!
# A generating submodule contains a basis over a semilocal algebra

Source: Stacks Project, Algebra, Tags 03C1 and 02M9
(blueprint: lem-a1-semilocal-submodule-basis).
-/

@[expose] public section

universe u v w

namespace Module

/-- A generating `D`-submodule contains an `E`-basis of a constant-rank finite locally
free module over a semilocal `D`-algebra. The local ring `D` has infinite residue field,
and its maximal ideal extends into the Jacobson radical of `E`.

Source: Stacks Project, Algebra, Tags 03C1 and 02M9.
(blueprint: lem-a1-semilocal-submodule-basis)

Proof:
1. Enumerate the maximal ideals `qᵢ` of `E`. The radical hypothesis gives embeddings
   `k = D/m → E/qᵢ = kᵢ`, so the images of `N` in `Fᵢ = P/qᵢP` are `k`-linear.
2. Choose a principal trivializing open containing each `qᵢ`. Localize its rank-`r`
   basis further to get `P_qᵢ ≃ E_qᵢ^r`. On fractions the comparison sends
   `(p/f^a)/s` to `p/(f^a s)`, with inverse `p/s ↦ (p/1)/s`.
3. Reduction identifies `P_qᵢ/qᵢP_qᵢ` with `Fᵢ` by `[p/s] ↦ s̄⁻¹[p]`, with inverse
   `[p] ↦ [p/1]`. Thus `Fᵢ` has dimension `r` over `kᵢ`.
4. Lift coordinate bases of the finitely many `Fᵢ` and express the lifts using `N`.
   Collect the finitely many elements of `N` used into `x₁,...,x_L`. The maps
   `Tᵢ : k^L → Fᵢ`, `c ↦ ∑ cⱼ[xⱼ]`, have `kᵢ`-spanning images.
5. Inductively choose `n₁,...,n_r` in `N` with independent images in every `Fᵢ`.
   Before step `t+1`, the inverse images under `Tᵢ` of the spans of the first `t`
   images are proper `k`-subspaces. Avoid their finite union by
   `lem-pc-finite-linear-avoidance`, lift the chosen coefficients to `D`, and take
   the corresponding combination of the `xⱼ`. At `t=r` every residue family is a basis.
6. The map `φ : E^r → P` defined by these vectors is surjective at each maximal
   localization by `lem-weil-pbc-nakayama-local-generators`.
7. Compose `φ_qᵢ` with the rank-`r` trivialization. The resulting surjective finite
   endomorphism is bijective by `lem-weil-pbc-finite-module-surjective-endomorphism-bijective`.
8. Apply `lem-weil-pbc-linear-map-bijective-at-maximal-localizations` to `φ`.
   Its inverse gives the desired basis, all of whose vectors were chosen in `N`.
   If `E` is the zero ring, the maximal spectrum and the avoidance family are empty;
   `P=0` and the same conclusion holds. -/
theorem exists_basis_mem_submodule_of_semilocal
    {D : Type u} [CommRing D] [IsLocalRing D]
    [Infinite (IsLocalRing.ResidueField D)]
    {E : Type v} [CommRing E] [Algebra D E] [Finite (MaximalSpectrum E)]
    (hjac : Ideal.map (algebraMap D E) (IsLocalRing.maximalIdeal D) ≤
      Ideal.jacobson (⊥ : Ideal E))
    {P : Type w} [AddCommGroup P] [Module E P] [Module D P] [IsScalarTower D E P]
    (r : ℕ) (hr : 1 ≤ r)
    (hfree : ∃ s : Finset E,
      (∀ p : PrimeSpectrum E, ∃ f ∈ s, f ∉ p.asIdeal) ∧
      ∀ f ∈ s, Nonempty (Module.Basis (Fin r) (Localization.Away f)
        (LocalizedModule.Away f P)))
    (N : Submodule D P) (hspan : Submodule.span E (N : Set P) = ⊤) :
    ∃ b : Module.Basis (Fin r) E P, ∀ i : Fin r, b i ∈ N := by
  classical
  have _ := hr
  obtain ⟨s, hcover, htriv⟩ := hfree
  have hlocal (q : Ideal E) [q.IsMaximal] :
      Nonempty (Basis (Fin r) (Localization.AtPrime q)
        (LocalizedModule q.primeCompl P)) ∧
      Module.Finite (E ⧸ q) (P ⧸ q • (⊤ : Submodule E P)) ∧
      finrank (E ⧸ q) (P ⧸ q • (⊤ : Submodule E P)) = r := by
    obtain ⟨f, hf, hfq⟩ := hcover ⟨q, inferInstance⟩
    obtain ⟨hb, _, _, hfin, hdim⟩ :=
      local_trivialization_residue_rank P q f hfq r (htriv f hf)
    exact ⟨hb, hfin, hdim⟩
  let K (q : MaximalSpectrum E) := E ⧸ q.asIdeal
  let F (q : MaximalSpectrum E) := P ⧸ q.asIdeal • (⊤ : Submodule E P)
  let (q : MaximalSpectrum E) : Field (K q) := Ideal.Quotient.field q.asIdeal
  let (q : MaximalSpectrum E) : AddCommGroup (F q) := inferInstance
  let (q : MaximalSpectrum E) : Module (K q) (F q) := inferInstance
  let (q : MaximalSpectrum E) : Module.Finite (K q) (F q) :=
    (hlocal q.asIdeal).2.1
  have hdim (q : MaximalSpectrum E) : finrank (K q) (F q) = r :=
    (hlocal q.asIdeal).2.2
  have hkill (q : MaximalSpectrum E) (a : D)
      (ha : a ∈ IsLocalRing.maximalIdeal D) :
      Ideal.Quotient.mk q.asIdeal (algebraMap D E a) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hle : Ideal.jacobson (⊥ : Ideal E) ≤ q.asIdeal :=
      sInf_le ⟨bot_le, q.isMaximal⟩
    exact hle (hjac (Ideal.mem_map_of_mem _ ha))
  let ι (q : MaximalSpectrum E) : IsLocalRing.ResidueField D →+* K q :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal D)
      ((Ideal.Quotient.mk q.asIdeal).comp (algebraMap D E)) (hkill q)
  let ρ (q : MaximalSpectrum E) :
      N →ₛₗ[(ι q).comp (IsLocalRing.residue D)] F q :=
    { toFun := fun n ↦ (q.asIdeal • (⊤ : Submodule E P)).mkQ n
      map_add' := fun x y ↦ map_add _ _ _
      map_smul' := fun a n ↦ by
        change Submodule.Quotient.mk (a • (n : P)) =
          Ideal.Quotient.mk q.asIdeal (algebraMap D E a) •
            Submodule.Quotient.mk (n : P)
        rw [Module.Quotient.mk_smul_mk, IsScalarTower.algebraMap_smul] }
  have hresSpan (q : MaximalSpectrum E) :
      Submodule.span (K q) (Set.range (ρ q)) = ⊤ := by
    let U := Submodule.span (K q) (Set.range (ρ q))
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨p, rfl⟩ := (q.asIdeal • (⊤ : Submodule E P)).mkQ_surjective x
    have hp : p ∈ Submodule.span E (N : Set P) := by rw [hspan]; trivial
    induction hp using Submodule.span_induction with
    | mem p hp => exact Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩
    | zero => exact U.zero_mem
    | add p p' hp hp' ih ih' => exact U.add_mem ih ih'
    | smul a p hp ih =>
      change Submodule.Quotient.mk (a • p) ∈ U
      rw [← Module.Quotient.mk_smul_mk]
      exact U.smul_mem _ ih
  obtain ⟨n, hn⟩ := IsLocalRing.exists_simultaneous_residue_bases
    D N (MaximalSpectrum E) r K ι F hdim ρ hresSpan
  have hbij : Function.Bijective (Fintype.linearCombination E fun i ↦ (n i : P)) := by
    apply bijective_linearCombination_of_maximal_residue_bases r
    · intro q hq
      exact (hlocal q).1
    · intro q hq
      exact hn ⟨q, hq⟩
  let e := LinearEquiv.ofBijective (Fintype.linearCombination E fun i ↦ (n i : P)) hbij
  refine ⟨Basis.ofEquivFun e.symm, fun i ↦ ?_⟩
  simp [Basis.coe_ofEquivFun, e]

end Module
