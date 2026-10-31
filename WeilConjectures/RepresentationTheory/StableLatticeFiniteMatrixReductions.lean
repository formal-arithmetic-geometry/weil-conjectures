/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
import WeilConjectures.RepresentationTheory.ProfiniteStableLattice
import Mathlib.Algebra.Module.Lattice
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Stable lattice coordinates and finite matrix reductions

Source: Stanford Weil II seminar, lecture 19, Proposition 1.1.9, second and third bullets,
printed p. 3 (blueprint: lem-sfb-stable-lattice-finite-matrix-reductions).
-/

@[expose] public section

universe u v w

namespace Padic

private theorem continuous_adic_coordinate
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) (f : M →ₗ[R] R) :
    @Continuous M (R ⧸ I ^ n) (I.adicModuleTopology M) ⊥
      (fun x ↦ Ideal.Quotient.mk (I ^ n) (f x)) := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace (R ⧸ I ^ n) := ⊥
  have : DiscreteTopology (R ⧸ I ^ n) := ⟨rfl⟩
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  have : IsTopologicalAddGroup M := B.toAddGroupFilterBasis.isTopologicalAddGroup
  let SB := I.ringFilterBasis.submodulesBasisIsBasis (I.adic_module_basis M)
  let q : M →+ R ⧸ I ^ n :=
    (Ideal.Quotient.mk (I ^ n)).toAddMonoidHom.comp f.toAddMonoidHom
  have hker : (I ^ n • (⊤ : Submodule R M)).toAddSubgroup ≤ q.ker := by
    intro x hx
    change Ideal.Quotient.mk (I ^ n) (f x) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      simpa only [map_smul, smul_eq_mul] using (I ^ n).mul_mem_right (f m) hr
    · intro x y hx hy
      simpa only [map_add] using (I ^ n).add_mem hx hy
  have hopen : IsOpen (q.ker : Set M) :=
    AddSubgroup.isOpen_mono hker (SB.openAddSubgroup n).isOpen
  apply continuous_of_continuousAt_zero q
  rw [ContinuousAt, map_zero, nhds_discrete (R ⧸ I ^ n), Filter.tendsto_pure]
  exact hopen.mem_nhds q.ker.zero_mem

set_option backward.isDefEq.respectTransparency false in
/-- A continuous compact-group representation admits integral lattice coordinates whose
reductions at every positive level are continuous finite matrix representations.

Source: Stanford Weil II seminar, lecture 19, Proposition 1.1.9, second and third bullets,
printed p. 3 (blueprint: lem-sfb-stable-lattice-finite-matrix-reductions).

Proof: The spectral norm is complete by `lem-weil-l-adic-extension-complete`.
By `lem-weil-pbc-finite-dimensional-linear-homeomorphism`, coordinates identify the norm
and module topologies. Apply `lem-pod-profinite-stable-lattice` to obtain a stable full
free lattice with its adic topology equal to the subspace topology and continuous action.
The chosen uniformizer generates the maximal ideal, so its adic topology agrees too.
Choose an integral basis. Clearing common denominators in the fraction field, using
`lem-weil-l-adic-extension-integers-dvr`, proves that it is also a field basis.
Expand the action on basis vectors to define the integral matrices. Composition gives
matrix multiplication, the identity gives the identity matrix, and the action of the
inverse gives both inverse identities. Thus these matrices define the homomorphism A.
For every positive n, `lem-weil-valued-dvr-finite-quotients` makes the coefficient quotient
finite. Apply its quotient map entrywise to A: multiplication and both inverse identities
are preserved. Finite matrices over a finite ring form a finite set, so the image is finite.
For a fixed reduced matrix, lift its entries. Its fiber consists of those g for which each
basis vector is carried into the coset of the lifted column modulo the nth lattice power.
These cosets are open and the orbit maps are continuous. The fiber is a finite intersection
of open sets; arbitrary inverse images are unions of fibers. The reduction is therefore
continuous into the discrete matrix group. Its range restriction has the same fibers and
is surjective by definition. In rank zero the bases are empty, the matrix groups and images
are singletons, and the empty intersection is all of G, so the same argument applies.
-/
theorem exists_stable_lattice_finite_matrix_reductions
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (V : Type w) [AddCommGroup V] [Module E V] [FiniteDimensional E V] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    letI : TopologicalSpace V := moduleTopology E V
    letI : Module (coefficientExtensionIntegers l E) V :=
      Module.compHom V (coefficientExtensionIntegers l E).subtype
    ∀ (ρ : G →* (V ≃ₗ[E] V)), Continuous (fun p : G × V ↦ ρ p.1 p.2) →
      ∃ Λ : Submodule (coefficientExtensionIntegers l E) V,
      ∃ b : Module.Basis (Fin (Module.finrank E V)) (coefficientExtensionIntegers l E) Λ,
      ∃ e : Module.Basis (Fin (Module.finrank E V)) E V,
      ∃ A : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank E V))
          (coefficientExtensionIntegers l E),
        Submodule.span E (Λ : Set V) = ⊤ ∧
        (∀ g : G, (ρ g) '' (Λ : Set V) = (Λ : Set V)) ∧
        (∀ j, (b j : V) = e j) ∧
        (∀ (g : G) (j : Fin (Module.finrank E V)),
          ρ g (e j) = ∑ i, ((A g i j : coefficientExtensionIntegers l E) : E) • e i) ∧
        (Ideal.span ({coefficientExtensionUniformizer l E} :
          Set (coefficientExtensionIntegers l E))).adicModuleTopology Λ =
            TopologicalSpace.induced (fun x : Λ ↦ (x : V)) inferInstance ∧
        (∃ a : G × Λ → Λ, Continuous a ∧
          ∀ p : G × Λ, (a p : V) = ρ p.1 (p.2 : V)) ∧
        ∀ (n : ℕ), 1 ≤ n →
          ∃ Aₙ : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank E V))
              (coefficientExtensionRing l E n),
            Aₙ = (Matrix.GeneralLinearGroup.map
              (Ideal.Quotient.mk (coefficientExtensionIdeal l E n))).comp A ∧
            Finite (coefficientExtensionRing l E n) ∧ Finite Aₙ.range ∧
            @Continuous G _ inferInstance ⊥ Aₙ ∧
            @Continuous G Aₙ.range inferInstance ⊥ Aₙ.rangeRestrict ∧
            Function.Surjective Aₙ.rangeRestrict := by
  classical
  intro ρ hρ
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : TopologicalSpace V := moduleTopology E V
  let : Module (coefficientExtensionIntegers l E) V :=
    Module.compHom V (coefficientExtensionIntegers l E).subtype
  let O := coefficientExtensionIntegers l E
  have hdvr := (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsFractionRing O E := hdvr.2.2.2.2.2.2.1
  have hgen : Ideal.span ({coefficientExtensionUniformizer l E} : Set O) =
      coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  obtain ⟨Λ, hfg, hspan, hfree, hrank, hstable, htop, hact⟩ :=
    exists_stable_lattice l E G V ρ hρ
  have := hfree
  have : Module.Finite O Λ := Module.Finite.of_fg hfg
  have : Submodule.IsLattice E Λ := ⟨hfg, hspan⟩
  let b : Module.Basis (Fin (Module.finrank E V)) O Λ :=
    (Module.finBasis O Λ).reindex (finCongr hrank)
  let e := b.extendOfIsLattice E
  have he (j) : (b j : V) = e j := (b.extendOfIsLattice_apply E j).symm
  have hmap (g : G) : Λ.map ((ρ g).restrictScalars O).toLinearMap = Λ := by
    apply SetLike.coe_injective
    exact hstable g
  let τ : G →* (Λ ≃ₗ[O] Λ) :=
    { toFun g := ((ρ g).restrictScalars O).ofSubmodules Λ Λ (hmap g)
      map_one' := by
        apply LinearEquiv.ext
        intro v
        apply Subtype.ext
        change ρ 1 (v : V) = v
        simp
      map_mul' g h := by
        apply LinearEquiv.ext
        intro v
        apply Subtype.ext
        change ρ (g * h) (v : V) = ρ g (ρ h v)
        rw [map_mul]
        rfl }
  let A : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank E V)) O :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv O Λ).symm.toMonoidHom.comp τ)
  have hA (g : G) (i j) : A g i j = b.repr (τ g (b j)) i := by
    exact LinearMap.toMatrixAlgEquiv_apply b (τ g).toLinearMap i j
  have hcoord (g : G) (j) :
      ρ g (e j) = ∑ i, ((A g i j : O) : E) • e i := by
    rw [← he]
    have hh := congrArg (fun x : Λ ↦ (x : V)) (b.sum_repr (τ g (b j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hh
    change (∑ i, (b.repr (τ g (b j)) i) • (b i : V)) = ρ g (b j : V) at hh
    calc
      ρ g (b j : V) = ∑ i, (b.repr (τ g (b j)) i) • (b i : V) := hh.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hA, ← he]
        exact (IsScalarTower.algebraMap_smul E _ _).symm
  refine ⟨Λ, b, e, A, hspan, hstable, he, hcoord, ?_, ?_, ?_⟩
  · rw [hgen]
    exact htop
  · rw [htop] at hact
    exact hact
  · intro n hn
    let Aₙ := (Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk (coefficientExtensionIdeal l E n))).comp A
    have : Finite (coefficientExtensionRing l E n) := finite_coefficientExtensionRing l E n hn
    let : TopologicalSpace (coefficientExtensionRing l E n) := ⊥
    have : DiscreteTopology (coefficientExtensionRing l E n) := ⟨rfl⟩
    let : TopologicalSpace
        (Matrix.GeneralLinearGroup (Fin (Module.finrank E V))
          (coefficientExtensionRing l E n)) := ⊥
    have : DiscreteTopology
        (Matrix.GeneralLinearGroup (Fin (Module.finrank E V))
          (coefficientExtensionRing l E n)) := ⟨rfl⟩
    let I : Ideal O := Ideal.span ({coefficientExtensionUniformizer l E} : Set O)
    let : TopologicalSpace (O ⧸ I ^ n) := ⊥
    let : TopologicalSpace Λ := I.adicModuleTopology Λ
    have hact' : ∃ a : G × Λ → Λ, Continuous a ∧
        ∀ p : G × Λ, (a p : V) = ρ p.1 (p.2 : V) := by
      change ∃ a, @Continuous (G × Λ) Λ
        (@instTopologicalSpaceProd G Λ _ (I.adicModuleTopology Λ))
        (I.adicModuleTopology Λ) a ∧ _
      change ∃ a, @Continuous (G × Λ) Λ
        (@instTopologicalSpaceProd G Λ _
          ((Ideal.span ({coefficientExtensionUniformizer l E} : Set O)).adicModuleTopology Λ))
        ((Ideal.span ({coefficientExtensionUniformizer l E} : Set O)).adicModuleTopology Λ) a ∧ _
      rw [hgen]
      exact hact
    obtain ⟨a, ha, haρ⟩ := hact'
    have haτ (p : G × Λ) : a p = τ p.1 p.2 := Subtype.ext (haρ p)
    have hentry (i j : Fin (Module.finrank E V)) :
        Continuous (fun g ↦ Aₙ g i j) := by
      have hp : Continuous (fun g : G ↦ (g, b j)) :=
        continuous_id.prodMk continuous_const
      have horbit : Continuous (fun g : G ↦ a (g, b j)) := ha.comp hp
      have hq := continuous_adic_coordinate I n (b.coord i)
      have hh := hq.comp horbit
      change @Continuous G (O ⧸ I ^ n) _ ⊥ (fun g ↦
        Ideal.Quotient.mk (I ^ n) (A g i j))
      apply hh.congr
      intro g
      exact congrArg (Ideal.Quotient.mk (I ^ n)) (by
        change b.repr (a (g, b j)) i = A g i j
        rw [haτ, hA])
    have hc : Continuous Aₙ := by
      apply continuous_discrete_rng.mpr
      intro B
      have hf : Aₙ ⁻¹' {B} = ⋂ i, ⋂ j, {g : G | Aₙ g i j = B i j} := by
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
        exact Matrix.GeneralLinearGroup.ext_iff _ _
      rw [hf]
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro j
      exact (isOpen_discrete {B i j}).preimage (hentry i j)
    refine ⟨Aₙ, rfl, inferInstance, inferInstance, hc, ?_, Aₙ.rangeRestrict_surjective⟩
    let : TopologicalSpace Aₙ.range := ⊥
    have : DiscreteTopology Aₙ.range := ⟨rfl⟩
    apply continuous_discrete_rng.mpr
    intro B
    have hf : Aₙ.rangeRestrict ⁻¹' {B} = Aₙ ⁻¹' {B.val} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact Subtype.ext_iff
    rw [hf]
    exact (isOpen_discrete {B.val}).preimage hc

end Padic
