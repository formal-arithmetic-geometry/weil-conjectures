/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleTopologicalInvariance.WStrictlyLocal
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale

/-!
# Weakly étale algebras over a universal homeomorphism are covered by base changes

Let `A → B` be a ring map such that `Spec B ⟶ Spec A` is a universal homeomorphism, and let `S`
be a weakly étale `B`-algebra. We show that there is a weakly étale `A`-algebra `T` and a
`B`-algebra map `S → T ⊗[A] B` which is surjective on spectra. Geometrically: every scheme
weakly étale over `Spec B` is covered, in the pro-étale topology, by the base change of a scheme
weakly étale over `Spec A`. This is the cover-density in the topological invariance of the small
pro-étale site.

## Proof

We run the proof of Stacks 097Z over `B`, but with the w-strictly local cover
`C_B = C ⊗[A] B` of `B`, the base change of the w-strict localization `C` of `A`; it is
w-strictly local by
`AlgebraicGeometry.Algebra.IsUniversalHomeomorphism.isWStrictlyLocalRing_tensorProduct`. This
yields a faithfully flat map `S → D` where `D` is bijective on stalks over `C_B` and w-local, so
that `D` is the modification `PullbackProfinite C_B T i` of the connected components of
`Spec C_B` along `T = π₀(Spec D)` (Stacks 097F). Since `Spec C_B ≃ Spec C`, this modification
is the base change of the modification `T' = PullbackProfinite C T i'` of `Spec C`, which is
ind-Zariski over `C` and hence ind-étale over `A`. The comparison map `D → T' ⊗[A] B` is
produced from a continuous map of spectra by Stacks 096L.

## Main statements

- `AlgebraicGeometry.Algebra.IsUniversalHomeomorphism.exists_weaklyEtale_comap_surjective`:
  the cover-density statement above.
-/

@[expose] public section

universe u

open PrimeSpectrum TensorProduct CategoryTheory WContractification

namespace AlgebraicGeometry.Algebra.IsUniversalHomeomorphism

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [_root_.Algebra.IsUniversalHomeomorphism A B]

/-- The map on connected components of spectra induced by a universal homeomorphism of rings is
injective. -/
lemma connectedComponentsMap_comap_injective :
    Function.Injective (PrimeSpectrum.continuous_comap (algebraMap A B)).connectedComponentsMap := by
  let h := (isHomeomorph_comap A B).homeomorph
  intro x y hxy
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
  have := congrArg h.symm.continuous.connectedComponentsMap hxy
  simp only [Continuous.connectedComponentsMap_mk] at this
  change ConnectedComponents.mk (h.symm (h x)) = ConnectedComponents.mk (h.symm (h y)) at this
  simpa using this

attribute [local instance] _root_.Algebra.TensorProduct.rightAlgebra

/-- **Cover-density for weakly étale algebras along a universal homeomorphism**: if
`Spec B ⟶ Spec A` is a universal homeomorphism and `S` is a weakly étale `B`-algebra, there is a
weakly étale `A`-algebra `T` and a ring map `S → T ⊗[A] B` over `B` which is surjective on
spectra. -/
theorem exists_weaklyEtale_comap_surjective (S : Type u) [CommRing S] [Algebra B S]
    [_root_.Algebra.WeaklyEtale B S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T), _root_.Algebra.WeaklyEtale A T ∧
      ∃ φ : S →+* T ⊗[A] B,
        φ.comp (algebraMap B S) = _root_.Algebra.TensorProduct.includeRight.toRingHom ∧
          Function.Surjective (PrimeSpectrum.comap φ) := by
  classical
  -- the w-strict localization `C` of `A` and its base change `CB` to `B`
  set C := WStrictLocalization A with hC
  set J : Ideal C := (WStrictLocalization.closedIdeal A).map
    (algebraMap (WLocalization A) C) with hJdef
  have hJ : zeroLocus (J : Set C) = closedPoints (PrimeSpectrum C) :=
    WStrictLocalization.zeroLocus_map_eq_closedPoints A
  set CB := C ⊗[A] B with hCB
  have hhomeo := isHomeomorph_comap C CB
  set JB : Ideal CB := J.map (algebraMap C CB) with hJBdef
  have hJB : zeroLocus (JB : Set CB) = closedPoints (PrimeSpectrum CB) := by
    rw [hJBdef, Ideal.map, zeroLocus_span, ← preimage_comap_zeroLocus, hJ,
      hhomeo.isEmbedding.closedPoints_eq_preimage]
    rw [hhomeo.surjective.range_eq]
    exact stableUnderSpecialization_univ
  have hCB' : ∀ p : PrimeSpectrum B, ∃ x ∈ zeroLocus (JB : Set CB),
      PrimeSpectrum.comap (algebraMap B CB) x = p := by
    intro p
    obtain ⟨x, hx, hxp⟩ := WStrictLocalization.exists_mem_zeroLocus_comap_eq A
      (PrimeSpectrum.comap (algebraMap A B) p)
    obtain ⟨y, rfl⟩ := hhomeo.surjective x
    refine ⟨y, ?_, ?_⟩
    · rw [hJBdef, Ideal.map, zeroLocus_span, ← preimage_comap_zeroLocus]
      exact hx
    · apply comap_injective A B
      rw [← hxp, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 1
      ext a
      change (1 : C) ⊗ₜ[A] algebraMap A B a = algebraMap A C a ⊗ₜ[A] (1 : B)
      rw [_root_.Algebra.algebraMap_eq_smul_one (A := B) a, _root_.Algebra.algebraMap_eq_smul_one (A := C) a,
        TensorProduct.smul_tmul]
  -- Stacks 097Z over `B`, with the w-strictly local cover `CB`
  set D' := CB ⊗[B] S with hD'
  set D := (JB.map (algebraMap CB D')).WLocalization with hD
  obtain ⟨hbos, hwloc⟩ :=
    _root_.Algebra.WeaklyEtale.bijectiveOnStalks_wLocalization (R := B) (S := S) JB hJB
  have hsurjD := _root_.Algebra.WeaklyEtale.comap_surjective_wLocalization (R := B) (S := S)
    JB hJB hCB'
  -- Stacks 097F: `D` is the modification of `Spec CB` along `T = π₀(Spec D)`
  set T := ConnectedComponents (PrimeSpectrum D) with hT
  let i : C(T, ConnectedComponents (PrimeSpectrum CB)) :=
    ⟨(PrimeSpectrum.continuous_comap (algebraMap CB D)).connectedComponentsMap,
      (PrimeSpectrum.continuous_comap (algebraMap CB D)).connectedComponentsMap_continuous⟩
  obtain ⟨e⟩ := _root_.Algebra.BijectiveOnStalks.nonempty_algEquiv_pullbackProfinite CB D hwloc
  -- the lift `T' = PullbackProfinite C T i'` of `D`
  let i' : C(T, ConnectedComponents (PrimeSpectrum C)) :=
    ⟨(PrimeSpectrum.continuous_comap (algebraMap C CB)).connectedComponentsMap ∘ i,
      (PrimeSpectrum.continuous_comap (algebraMap C CB)).connectedComponentsMap_continuous.comp
        i.continuous⟩
  set T' := PullbackProfinite C T i' with hT'
  let _ : Algebra A T' := Algebra.compHom T' (algebraMap A C)
  have : IsScalarTower A C T' := .of_algebraMap_eq' rfl
  have : _root_.Algebra.IndEtale A T' := _root_.Algebra.IndEtale.trans A (S := C) T'
  refine ⟨T', inferInstance, inferInstance, inferInstance, ?_⟩
  -- `E = T' ⊗[A] B` as a `CB`-algebra
  set E := T' ⊗[A] B with hE
  let ψ : CB →ₐ[A] E :=
    _root_.Algebra.TensorProduct.map (IsScalarTower.toAlgHom A C T') (AlgHom.id A B)
  let _ : Algebra CB E := ψ.toRingHom.toAlgebra
  have : IsScalarTower C CB E := .of_algebraMap_eq fun x ↦ by
    change algebraMap C T' x ⊗ₜ[A] (1 : B) = ψ (x ⊗ₜ[A] 1)
    exact (_root_.Algebra.TensorProduct.map_tmul (IsScalarTower.toAlgHom A C T')
      (AlgHom.id A B) x 1).symm
  have hpush : _root_.Algebra.IsPushout C T' CB E :=
    _root_.Algebra.IsPushout.tensorProduct_tensorProduct A B C T' (RingHom.ext fun x ↦ by
      change ψ (1 ⊗ₜ x) = 1 ⊗ₜ x
      rw [_root_.Algebra.TensorProduct.map_tmul, map_one]
      rfl)
  have hψ : (algebraMap CB E).IndZariski :=
    RingHom.IndZariski.isStableUnderBaseChange C T' CB E
      ((RingHom.IndZariski.algebraMap_iff C T').mpr inferInstance)
  have : _root_.Algebra.IndZariski CB E := (RingHom.IndZariski.algebraMap_iff _ _).mp hψ
  -- the continuous map `Spec E → Spec (PullbackProfinite CB T i)` over `Spec CB`
  have pb := PullbackProfinite.isPullback CB T i
  let a : TopCat.of (PrimeSpectrum E) ⟶ TopCat.of T :=
    TopCat.ofHom ((PullbackProfinite.projT C T i').comp
      ⟨PrimeSpectrum.comap (algebraMap T' E), PrimeSpectrum.continuous_comap _⟩)
  let b : TopCat.of (PrimeSpectrum E) ⟶ TopCat.of (PrimeSpectrum CB) :=
    TopCat.ofHom ⟨PrimeSpectrum.comap (algebraMap CB E), PrimeSpectrum.continuous_comap _⟩
  -- the structure maps of `Spec E` to `Spec C`
  have hCE : ∀ y : PrimeSpectrum E, PrimeSpectrum.comap (algebraMap C CB)
      (PrimeSpectrum.comap (algebraMap CB E) y) =
      PullbackProfinite.projSpec C T i' (PrimeSpectrum.comap (algebraMap T' E) y) := by
    intro y
    change PrimeSpectrum.comap (algebraMap C CB) (PrimeSpectrum.comap (algebraMap CB E) y) =
      PrimeSpectrum.comap (algebraMap C T') (PrimeSpectrum.comap (algebraMap T' E) y)
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq C T' E]
  -- the compatibility on `π₀` of a point of `PullbackProfinite C T i'`
  have hfib : ∀ y : PrimeSpectrum T', i' (PullbackProfinite.projT C T i' y) =
      ConnectedComponents.mk (PullbackProfinite.projSpec C T i' y) := by
    intro y
    have := (PullbackProfinite.fiberHomeo C T i' y).2
    rwa [PullbackProfinite.fst_fiberHomeo, PullbackProfinite.snd_fiberHomeo] at this
  have w : a ≫ TopCat.ofHom i =
      b ≫ TopCat.ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ := by
    ext y
    apply connectedComponentsMap_comap_injective C CB
    change i' (PullbackProfinite.projT C T i' (PrimeSpectrum.comap (algebraMap T' E) y)) =
      (PrimeSpectrum.continuous_comap (algebraMap C CB)).connectedComponentsMap
      (ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap CB E) y))
    rw [hfib, Continuous.connectedComponentsMap_mk, hCE]
  let φ := pb.lift a b w
  have hφT : ∀ y, PullbackProfinite.projT CB T i (φ y) = a y := fun y ↦
    ConcreteCategory.congr_hom (pb.lift_fst a b w) y
  have hφS : ∀ y, PullbackProfinite.projSpec CB T i (φ y) = b y := fun y ↦
    ConcreteCategory.congr_hom (pb.lift_snd a b w) y
  let Φ : _root_.Algebra.BijectiveOnStalks.HomOver CB (PullbackProfinite CB T i) E :=
    { toContinuousMap := φ.hom
      comp_comap_algebraMap := fun y ↦ hφS y }
  -- Stacks 096L: the induced `CB`-algebra map `D → E`
  let g₀ := _root_.Algebra.BijectiveOnStalks.algHom_of_continuousMap CB _ E Φ
  have hg₀ : ∀ y, PrimeSpectrum.comap g₀.toRingHom y = φ y := fun y ↦
    DFunLike.congr_fun
      (_root_.Algebra.BijectiveOnStalks.continuousMap_of_algHom_algHom_of_continuousMap CB _ E Φ) y
  let g : D →ₐ[CB] E := g₀.comp e.symm.toAlgHom
  refine ⟨g.toRingHom.comp ((algebraMap D' D).comp (algebraMap S D')), ?_, ?_⟩
  · -- compatibility with `B`
    ext x
    change g (algebraMap D' D (algebraMap S D' (algebraMap B S x))) = (1 : T') ⊗ₜ[A] x
    rw [← IsScalarTower.algebraMap_apply B S D']
    rw [show algebraMap B D' x = algebraMap CB D' (algebraMap B CB x) from rfl,
      ← IsScalarTower.algebraMap_apply CB D' D, AlgHom.commutes]
    change ψ ((1 : C) ⊗ₜ[A] x) = _
    rw [_root_.Algebra.TensorProduct.map_tmul, map_one]
    rfl
  · -- surjectivity on spectra
    suffices hg : Function.Surjective (PrimeSpectrum.comap g.toRingHom) by
      intro w
      obtain ⟨z, rfl⟩ := hsurjD w
      obtain ⟨y, rfl⟩ := hg z
      exact ⟨y, by rw [PrimeSpectrum.comap_comp_apply]⟩
    intro z
    -- the point `z' = e⁻¹ z` of the modification of `Spec CB`
    set z' : PrimeSpectrum (PullbackProfinite CB T i) :=
      PrimeSpectrum.comap e.toRingHom z with hz'
    set c := PrimeSpectrum.comap (algebraMap C CB) (PullbackProfinite.projSpec CB T i z')
    have hc : i' (PullbackProfinite.projT CB T i z') = ConnectedComponents.mk c := by
      have := (PullbackProfinite.fiberHomeo CB T i z').2
      rw [PullbackProfinite.fst_fiberHomeo, PullbackProfinite.snd_fiberHomeo] at this
      change (PrimeSpectrum.continuous_comap (algebraMap C CB)).connectedComponentsMap
        (i (PullbackProfinite.projT CB T i z')) = _
      rw [this, Continuous.connectedComponentsMap_mk]
    -- the point of `Spec T'` with coordinates `(projT z', c)`, and a point of `Spec E` over it
    set t := (PullbackProfinite.fiberHomeo C T i').symm
      ⟨(PullbackProfinite.projT CB T i z', c), hc⟩ with ht
    have ht₁ : PullbackProfinite.projT C T i' t = PullbackProfinite.projT CB T i z' := by
      rw [← PullbackProfinite.fst_fiberHomeo, ht, Homeomorph.apply_symm_apply]
    have ht₂ : PullbackProfinite.projSpec C T i' t = c := by
      rw [← PullbackProfinite.snd_fiberHomeo, ht, Homeomorph.apply_symm_apply]
    obtain ⟨y, hy⟩ := comap_surjective T' E t
    refine ⟨y, ?_⟩
    -- `φ y = z'`, by comparing coordinates
    have hφy : φ y = z' := by
      apply (PullbackProfinite.fiberHomeo CB T i).injective
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · rw [PullbackProfinite.fst_fiberHomeo, PullbackProfinite.fst_fiberHomeo, hφT]
        change PullbackProfinite.projT C T i' (PrimeSpectrum.comap (algebraMap T' E) y) = _
        rw [hy, ht₁]
      · rw [PullbackProfinite.snd_fiberHomeo, PullbackProfinite.snd_fiberHomeo, hφS]
        apply comap_injective C CB
        change PrimeSpectrum.comap (algebraMap C CB) (PrimeSpectrum.comap (algebraMap CB E) y) = c
        rw [hCE, hy, ht₂]
    change PrimeSpectrum.comap (g₀.toRingHom.comp e.symm.toAlgHom.toRingHom) y = z
    rw [PrimeSpectrum.comap_comp_apply, hg₀, hφy, hz', ← PrimeSpectrum.comap_comp_apply]
    have he : e.toRingHom.comp e.symm.toAlgHom.toRingHom = RingHom.id D := by
      ext x
      exact e.apply_symm_apply x
    rw [he, PrimeSpectrum.comap_id]

end AlgebraicGeometry.Algebra.IsUniversalHomeomorphism
