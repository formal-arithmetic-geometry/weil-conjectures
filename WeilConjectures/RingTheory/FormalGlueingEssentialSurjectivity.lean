/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.FormalGlueingInjectiveApproximation
import WeilConjectures.RingTheory.FormalGlueingExtensionTransport
import Mathlib.Algebra.Module.LocalizedModule.Exact
import WeilConjectures.AlgebraicGeometry.TorsionModuleFlatBaseChangeIso
import WeilConjectures.RingTheory.TorsionExtensionFlatDescent

/-!
# Algebraizing formal glueing data

If `R → S` is flat and induces an isomorphism modulo `I = (f₁, …, fₜ)`, every formal glueing
datum `X` is isomorphic to the canonical datum of an `R`-module.

## Implementation details

Let `H` be the module of compatible families of `X`. The chart projections extend to
isomorphisms `H_{fᵢ} ≃ X.M i`, and tensoring the prime projection gives a morphism
`Ψ : Can(H) → X`. The kernel and cokernel of `Ψ.prime` vanish after localizing at each `fᵢ`,
hence are `I`-power torsion; flat base change of torsion submodules shows that `Ψ.prime` is
injective. Descending the extension of the cokernel `Q` by `S ⊗ H` gives an extension
`H → E → Q` with `S ⊗ E ≃ X.M'`; as `H → E` is bijective after each localization, the maps
assemble to an isomorphism `Can(E) ≅ X`. The module `E` lives in the same universe, since the
construction only uses submodules, quotients and finite products.

## References

* [Stacks, Tag 05ER]
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

private theorem lm_comp {R : Type u} [CommRing R] (f : R)
    {M N P : ModuleCat.{w} R} (a : M →ₗ[R] N) (b : N →ₗ[R] P) :
    localMap f (b.comp a) = (localMap f b).comp (localMap f a) :=
  IsLocalizedModule.map_comp' _ _ _ _ a b

private theorem lm_id {R : Type u} [CommRing R] (f : R) (M : ModuleCat.{w} R) :
    localMap f (LinearMap.id : M →ₗ[R] M) = LinearMap.id :=
  IsLocalizedModule.map_id _ _

private theorem em_comp {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) {M N P : ModuleCat.{w} R} (a : M →ₗ[R] N) (b : N →ₗ[R] P) :
    extendMapR φ (b.comp a) = (extendMapR φ b).comp (extendMapR φ a) := by
  let : Algebra R S := φ.toAlgebra
  simp only [extendMapR, extendMap, LinearMap.baseChange_comp]
  rfl

private theorem em_id {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{w} R) :
    extendMapR φ (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  let : Algebra R S := φ.toAlgebra
  simp only [extendMapR, extendMap, LinearMap.baseChange_id]
  rfl

private theorem inverse_square {R : Type u} [CommRing R]
    {A B C D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B]
    [Module R C] [Module R D]
    (a : A →ₗ[R] B) (b : C →ₗ[R] D) (p : A →ₗ[R] C) (q : B →ₗ[R] D)
    (p' : C →ₗ[R] A) (q' : D →ₗ[R] B)
    (hpp' : p.comp p' = LinearMap.id) (hqq : q'.comp q = LinearMap.id)
    (h : b.comp p = q.comp a) : a.comp p' = q'.comp b := by
  calc
    a.comp p' = (q'.comp q).comp (a.comp p') := by rw [hqq, LinearMap.id_comp]
    _ = q'.comp ((q.comp a).comp p') := by simp only [LinearMap.comp_assoc]
    _ = q'.comp ((b.comp p).comp p') := by rw [← h]
    _ = q'.comp b := by rw [LinearMap.comp_assoc, hpp', LinearMap.comp_id]

private theorem glue_hom_ext {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {φ : R →+* S} {t : ℕ} {f : Fin t → R}
    {X Y : Data.{u, v, w} φ f} {F G : Hom X Y}
    (hp : F.prime = G.prime) (hc : F.chart = G.chart) : F = G := by
  cases F
  cases G
  cases hp
  cases hc
  rfl

private theorem iso_of_bijective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {φ : R →+* S} {t : ℕ} {f : Fin t → R}
    {X Y : Data.{u, v, w} φ f} (F : X ⟶ Y)
    (hp : Function.Bijective F.prime) (hc : ∀ i, Function.Bijective (F.chart i)) :
    Nonempty (X ≅ Y) := by
  classical
  let ep := LinearEquiv.ofBijective F.prime hp
  let ec := fun i ↦ LinearEquiv.ofBijective (F.chart i) (hc i)
  have pp : F.prime.comp ep.symm.toLinearMap = LinearMap.id := ep.comp_symm
  have pp' : ep.symm.toLinearMap.comp F.prime = LinearMap.id := ep.symm_comp
  have cc (i) : (F.chart i).comp (ec i).symm.toLinearMap = LinearMap.id :=
    (ec i).comp_symm
  have cc' (i) : (ec i).symm.toLinearMap.comp (F.chart i) = LinearMap.id :=
    (ec i).symm_comp
  let G : Y ⟶ X :=
    { prime := ep.symm.toLinearMap
      chart := fun i ↦ (ec i).symm.toLinearMap
      prime_compat := by
        intro i
        apply inverse_square _ _ _ _ _ _ _ _ (F.prime_compat i)
        · rw [← lm_comp]
          change localMap (f i) (restrictMap φ (F.prime.comp ep.symm.toLinearMap)) = _
          rw [pp]
          exact lm_id _ _
        · rw [← em_comp, cc', em_id]
      chart_compat := by
        intro i k
        apply inverse_square _ _ _ _ _ _ _ _ (F.chart_compat i k)
        · rw [← lm_comp, cc, lm_id]
        · rw [← lm_comp, cc', lm_id] }
  have hg : F ≫ G = 𝟙 X := by
    change compHom F G = idHom X
    have he : (fun i ↦ (G.chart i).comp (F.chart i)) = fun _ ↦ LinearMap.id :=
      funext cc'
    exact glue_hom_ext pp' he
  have hf : G ≫ F = 𝟙 Y := by
    change compHom G F = idHom Y
    have he : (fun i ↦ (F.chart i).comp (G.chart i)) = fun _ ↦ LinearMap.id :=
      funext cc
    exact glue_hom_ext pp he
  exact ⟨{ hom := F, inv := G, hom_inv_id := hg, inv_hom_id := hf }⟩

private theorem cast_comp_heq {S : Type v} [CommRing S]
    {A B C : ModuleCat.{w} S} (h : A = B) (g : A →ₗ[S] C) :
    HEq (g.comp (eqToIso h.symm).hom.hom) g := by
  cases h
  rfl

/-- If `R → S` is flat and induces an isomorphism modulo `I = (f₁, …, fₜ)`, then every formal
glueing datum is isomorphic to the canonical datum of some `R`-module. -/
theorem canonical_essentially_surjective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f)
    (hobj : (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))))
    (hflat : φ.Flat)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map))
    (X : Data.{u, v, max u v w} φ f) :
    ∃ M : ModuleCat.{max u v w} R, Nonempty (Can.obj M ≅ X) := by
  classical
  let : Algebra R S := φ.toAlgebra
  let I : Ideal R := Ideal.span (Set.range f)
  have hI : I.FG := Submodule.fg_span (Set.finite_range f)
  obtain ⟨H, ψ, hψp, hψc, hQ⟩ :=
    exists_injective_approximation φ t f Can hobj hflat hquot X
  let U := LinearMap.range ψ.prime
  let Q : ModuleCat.{max u v w} R := restrict φ (ModuleCat.of S (X.M' ⧸ U))
  let : Module S Q := inferInstanceAs (Module S (X.M' ⧸ U))
  let : IsScalarTower R S Q := ⟨fun r s x ↦ mul_smul (φ r) s x⟩
  let ρ : X.M' →ₗ[S] Q := U.mkQ
  let ι : TensorProduct R S H →ₗ[S] X.M' :=
    ψ.prime.comp (eqToIso ((hobj H).1).symm).hom.hom
  have hι : Function.Injective ι :=
    hψp.comp (eqToIso ((hobj H).1).symm).toLinearEquiv.injective
  have hιρ : Function.Exact ι ρ := by
    intro x
    change Submodule.Quotient.mk x = 0 ↔ ∃ y, ι y = x
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(eqToIso ((hobj H).1)).hom.hom y, ?_⟩
      change ψ.prime ((eqToIso ((hobj H).1)).toLinearEquiv.symm
        ((eqToIso ((hobj H).1)).toLinearEquiv y)) = ψ.prime y
      rw [LinearEquiv.symm_apply_apply]
    · rintro ⟨y, rfl⟩
      exact ⟨(eqToIso ((hobj H).1).symm).hom.hom y, rfl⟩
  have hiso : ∃ e : (R ⧸ I) ≃+* (S ⧸ I.map φ),
      ∀ r : R, e (Ideal.Quotient.mk I r) = Ideal.Quotient.mk (I.map φ) (φ r) := by
    refine ⟨RingEquiv.ofBijective
      (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) hquot, ?_⟩
    intro r
    change (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) (Ideal.Quotient.mk I r) = _
    exact Ideal.quotientMap_mk
  have ht := RingTheory.torsionModule_flat_baseChange_bijective
    (T := Q) φ hflat I hiso hQ
  have hmodule : Module.compHom S φ = (inferInstance : Module R S) := by
    ext r s
    exact (Algebra.smul_def r s).symm
  rw [hmodule] at ht
  have hη : Function.Bijective (fun x : Q ↦ TensorProduct.tmul R (1 : S) x) := by
    convert (TensorProduct.comm R Q S).bijective.comp ht using 1
    ext x
    simp
  let mult : S →ₗ[S] Q →ₗ[R] Q :=
    { toFun := fun s ↦
        { toFun := fun x ↦ s • x
          map_add' := smul_add s
          map_smul' := fun r x ↦ smul_comm s r x }
      map_add' := fun s t ↦ LinearMap.ext (add_smul s t)
      map_smul' := fun s t ↦ LinearMap.ext (mul_smul s t) }
  let μ : TensorProduct R S Q →ₗ[S] Q := TensorProduct.AlgebraTensorModule.lift mult
  have hμη (x : Q) : μ (TensorProduct.tmul R (1 : S) x) = x := by
    change (1 : S) • x = x
    exact one_smul S x
  have hμ : Function.Bijective μ := by
    constructor
    · intro z z' h
      obtain ⟨x, rfl⟩ := hη.2 z
      obtain ⟨y, rfl⟩ := hη.2 z'
      rw [hμη, hμη] at h
      rw [h]
    · intro x
      exact ⟨TensorProduct.tmul R (1 : S) x, hμη x⟩
  let eμ := LinearEquiv.ofBijective μ hμ
  let π : X.M' →ₗ[S] TensorProduct R S Q := eμ.symm.toLinearMap.comp ρ
  have hιπ : Function.Exact ι π := by
    intro x
    change eμ.symm (ρ x) = 0 ↔ ∃ y, ι y = x
    rw [← eμ.symm.map_zero, eμ.symm.injective.eq_iff]
    exact hιρ x
  have hπ : Function.Surjective π := eμ.symm.surjective.comp U.mkQ_surjective
  obtain ⟨E₀, _, _, j, q, hj, hjq, _, θ, hθj, _⟩ :=
    LinearMap.exists_torsion_extension_flat_descent hflat I hI hquot hQ ι π hι hιπ hπ
  let E : ModuleCat.{max u v w} R := ModuleCat.of R E₀
  have hjloc (i : Fin t) : Function.Bijective (localMap (f i) (M := H) (N := E) j) := by
    constructor
    · exact IsLocalizedModule.map_injective (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap _ H) (LocalizedModule.mkLinearMap _ E) j hj
    · intro z
      have hex := LocalizedModule.map_exact (Submonoid.powers (f i)) j q hjq
      apply (hex z).mp
      induction z using LocalizedModule.induction_on with
      | _ x d =>
        rw [IsLocalizedModule.map_LocalizedModules]
        obtain ⟨n, _, hn⟩ := hQ (q x)
        have hfi : f i ∈ I := Ideal.subset_span (Set.mem_range_self i)
        have hf : (f i) ^ n ∈ I ^ n := Ideal.pow_mem_pow hfi n
        rw [← LocalizedModule.zero_mk d, LocalizedModule.mk_eq]
        refine ⟨⟨(f i) ^ n, ⟨n, rfl⟩⟩, ?_⟩
        change (f i) ^ n • (d : R) • q x = (f i) ^ n • (d : R) • (0 : Q)
        rw [smul_comm, hn _ hf, smul_zero, smul_zero]
  have hθ : HEq (θ.toLinearMap.comp (extendMap φ (M := H) (N := E) j)) ψ.prime := by
    rw [show extendMap φ (M := H) (N := E) j = j.baseChange S from rfl]
    rw [hθj]
    exact cast_comp_heq (hobj H).1 ψ.prime
  obtain ⟨Φ, hΦp, hΦc⟩ :=
    exists_extension_transport φ t f Can hobj H E X ψ j θ hjloc hψc hθ
  exact ⟨E, iso_of_bijective Φ hΦp hΦc⟩

end FormalGlueing
