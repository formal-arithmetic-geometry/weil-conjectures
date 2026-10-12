module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ValuationClosedFibreDivisibility
import Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator
import Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

@[expose] public section

open scoped AlgebraicGeometry

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

/-!
# Generic-fibre triviality over a valuation ring

Source: More on Morphisms, Lemma 0EX8 (blueprint: lem-sc-picard-locus-closed-valuation-triviality).
-/

/-- Let `A` be a valuation ring with fraction field `K`, and let `f : X ⟶ Spec A` be
proper, flat, and of finite presentation (properness supplies quasi-compactness and
quasi-separatedness, so `LocallyOfFinitePresentation f` is finite presentation here).
`hX₀` says that the closed fibre `X₀ = X ×_A Spec (A ⧸ 𝔪)` is integral. `hglobal` says
`H⁰(X_K, O_{X_K}) = K`: the canonical map `K = Γ(Spec K, ⊤) → Γ(X_K, ⊤)` induced by the
projection `X_K ⟶ Spec K` is an isomorphism. `htriv` says that the pullback of `L` along
`X_K ⟶ X` is trivial. Then `L` is trivial on `X`.

Proof (Stacks 0EX8): `H⁰(X, L)` is a finitely presented, torsion-free, hence finite free
`A`-module; flat base change gives `H⁰(X, L) ⊗_A K = H⁰(X_K, L_K) = K`, so it is free of
rank one with a generator `s`. If `A` is a field there is nothing more to prove. Otherwise
`s` restricted to the integral closed fibre is nonzero (else `s` would be divisible by a
nonzero `π ∈ 𝔪`), so the zero scheme `Z(s)` is a relative effective Cartier divisor, flat
over `A`. As `s` trivializes `L` on `X_K`, `Z(s)_K` is empty; generizations lift along the
flat `Z(s) → Spec A`, so `Z(s)` is empty and `s` trivializes `L`.

Source: More on Morphisms, Lemma 0EX8
(blueprint: lem-sc-picard-locus-closed-valuation-triviality). -/
theorem generic_fibre_triviality_over_valuation_ring
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (hX₀ : IsIntegral (pullback f (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))))
    (hglobal : IsIso (pullback.snd f (Spec.map
      (CommRingCat.ofHom (algebraMap A K)))).appTop)
    (htriv : Nonempty ((Scheme.Modules.tensorPullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj L ≅
      SheafOfModules.unit _)) :
    Nonempty (L ≅ SheafOfModules.unit _) := by
  classical
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨s, hs, hsK⟩ := Scheme.Modules.exists_generic_trivializing_generator
    A K X f L hglobal htriv
  obtain ⟨hclosed, hdiv⟩ := Scheme.Modules.closed_fibre_vanishing_is_divisible
    A X f L hX₀ s
  have hs₀ : ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
      (f.fiberι (IsLocalRing.closedPoint A)))).unit.app L).val.app
      (Opposite.op ⊤) s ≠ 0 := by
    intro hz
    obtain ⟨π, hπ, t, ht⟩ := hdiv hz
    obtain ⟨a, ha⟩ := hs.surjective t
    rw [← ha] at ht
    have hscalar : π * a = 1 := hs.injective (by
      simpa only [map_mul, mul_smul, map_one, one_smul] using ht)
    have hone : (1 : A) ∈ IsLocalRing.maximalIdeal A :=
      hscalar ▸ (IsLocalRing.maximalIdeal A).mul_mem_right a hπ
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem
      (IsLocalRing.maximalIdeal A) hone isUnit_one)
  let : IsIntegral (f.fiber (IsLocalRing.closedPoint A)) := hclosed
  have hcartier := Scheme.Modules.valuation_zero_section_relative_cartier
    A X f (IsLocalRing.closedPoint A)
    (IsLocalRing.isClosed_singleton_closedPoint A) L s hs₀
  let J := Scheme.Modules.Hom.zeroLocus (Scheme.Modules.homOfGlobalSection L s)
  have : Flat (J.subschemeι ≫ f) := hcartier.2
  let g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let η := g (IsLocalRing.closedPoint K)
  have hη : IsGenericPoint η Set.univ := by
    change closure {η} = Set.univ
    rw [PrimeSpectrum.closure_singleton]
    have hbot : η.asIdeal = ⊥ := by
      change Ideal.comap (algebraMap A K) (IsLocalRing.maximalIdeal K) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A K)
    rw [hbot, PrimeSpectrum.zeroLocus_bot]
  have hJ : J.support = ⊥ := by
    apply TopologicalSpace.Closeds.ext
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨z, rfl⟩ := (J.range_subschemeι ▸ hx : x ∈ Set.range J.subschemeι)
    obtain ⟨z', _, hz'⟩ := Flat.generalizingMap (J.subschemeι ≫ f)
      (hη.specializes (Set.mem_univ ((J.subschemeι ≫ f) z)))
    obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := g) (J.subschemeι z') (IsLocalRing.closedPoint K) hz'
    have hwJ : (pullback.fst f g) w ∈ J.support := by
      rw [hw]
      change J.subschemeι z' ∈ (J.support : Set X)
      rw [← J.range_subschemeι]
      exact Set.mem_range_self z'
    have hwK : w ∈ (J.comap (pullback.fst f g)).support := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hwJ
    rw [hsK, Scheme.IdealSheafData.support_top] at hwK
    exact hwK
  have htop : (⊤ : X.Opens) ≤ J.support.compl := by
    rw [hJ]
    intro x _
    exact Set.notMem_empty x
  have hgen := Scheme.Modules.isFreeGenerator_app_one_of_le
    (Scheme.Modules.homOfGlobalSection L s) htop
  have hsgen : Scheme.Modules.IsFreeGenerator s := by
    change Scheme.Modules.IsFreeGenerator
      ((Scheme.Modules.homOfGlobalSection L s).app ⊤ (1 : Γ(X, ⊤))) at hgen
    simpa only [Scheme.Modules.homOfGlobalSection_app_one,
      Scheme.Modules.presheaf_map_id_apply] using hgen
  have := Scheme.Modules.isIso_homOfGlobalSection hsgen
  exact ⟨(asIso (Scheme.Modules.homOfGlobalSection L s)).symm⟩

