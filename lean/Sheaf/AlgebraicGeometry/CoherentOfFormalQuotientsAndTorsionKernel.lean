/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Finiteness from formal quotients and a bounded torsion kernel

Source: Stacks Project, Tag 0889(1), finiteness paragraph, and Tag 05EU.
(blueprint: lem-weil-pbc-coherent-of-formal-quotients-torsion-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open Scheme Scheme.Modules

private theorem exists_fg_lift {R P Q : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) (K : Submodule R Q) (hK : K.FG) (hle : K ≤ f.range) :
    ∃ L : Submodule R P, L.FG ∧ L.map f = K := by
  classical
  obtain ⟨n, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  have hmem (i : Fin n) : v i ∈ K := by
    rw [← hv]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose w hw using fun i ↦ hle (hmem i)
  refine ⟨Submodule.span R (Set.range w), Submodule.fg_span (Set.finite_range w), ?_⟩
  rw [Submodule.map_span]
  convert hv using 2
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (hw i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨w i, ⟨i, rfl⟩, hw i⟩

private theorem finite_of_quotient_and_torsion_kernel
    {R P H : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup H] [Module R H] [Module.Finite R H]
    (I : Ideal R) (a : P →ₗ[R] H)
    [Module.Finite R (P ⧸ (I • (⊤ : Submodule R P)))]
    (hk : ∀ r ∈ I, ∀ x : P, a x = 0 → r • x = 0) : Module.Finite R P := by
  classical
  let K := I • (⊤ : Submodule R P)
  obtain ⟨L₁, hL₁, hmap₁⟩ := exists_fg_lift a a.range (IsNoetherian.noetherian _) le_rfl
  obtain ⟨L₂, hL₂, hmap₂⟩ := exists_fg_lift K.mkQ ⊤ Module.Finite.fg_top
    (by rw [Submodule.range_mkQ])
  let L := L₁ ⊔ L₂
  have hIL : K ≤ L := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ (fun x y hx hy ↦ L.add_mem hx hy)
    intro r hr x _
    have hx : a x ∈ L₁.map a := by rw [hmap₁]; exact ⟨x, rfl⟩
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
    have hxy : a (x - y) = 0 := by simp [map_sub, heq]
    have hz := hk r hr (x - y) hxy
    have he : r • x = r • y := by simpa only [smul_sub, sub_eq_zero] using hz
    rw [he]
    exact (show L₁ ≤ L from le_sup_left) (L₁.smul_mem r hy)
  have htop : L = ⊤ := by
    have h := (Submodule.map_mkQ_eq_top K L₂).mp hmap₂
    apply top_unique
    rw [← h]
    exact sup_le hIL le_sup_right
  apply Module.Finite.of_fg_top
  rw [← htop]
  exact hL₁.sup hL₂

set_option linter.style.haveILetI false in
/-- Sections on an affine open are finite under the coherent formal quotient and
annihilated-kernel hypotheses.

Source: Stacks Project, Tag 0889(1), finiteness paragraph.
(blueprint: new-stage3-coherent-formal-quotients-affine-sections).

Proof: identify the formal quotient's affine sections with P/I^s P by exactness
of affine sections and the ideal-product comparison. Coherence makes this quotient
and the sections of H finite. The affine kernel comparison transfers the hypothesis
that I^s kills the kernel. The existing finite-generator lemma then proves that P
is finite, by lifting generators of the quotient and the image in H. -/
theorem finite_sections_of_formalQuotient_and_torsionKernel
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (H : CoherentModules X) (a : F ⟶ H.obj)
    (s : ℕ) (hs : 1 ≤ s)
    (hquot : RingedSpace.IsCoherent X.toRingedSpace
      (((formalCompletionFunctor J).obj F).obj (op (s - 1))))
    (hker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
      (kernel a))) (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(F, U.1) := by
  classical
  let Q := formalModuleQuotient J s F
  have hQcoh : RingedSpace.IsCoherent X.toRingedSpace Q := by
    simpa [formalCompletionFunctor, formalCompletionSystem, Nat.sub_add_cancel hs] using hquot
  have hFq : F.IsQuasicoherent := inferInstance
  letI : H.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X H.obj).mp H.property).1
  letI : (kernel a).IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel a
  have hpow : (Scheme.idealSheafPower J.toModulesι s).1.IsQuasicoherent :=
    (Scheme.Modules.ideal_times_quasiCoherent_affine_sections J F).2.2.1 s hs
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have hprod :
      (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2 F).IsQuasicoherent := by
    let b := MonoidalCategory.whiskerRight
      (Scheme.idealSheafPower J.toModulesι s).2 F ≫ (MonoidalCategory.leftUnitor F).hom
    have := Scheme.Modules.quasiCoherent_tensor_product_affine_sections
      (Scheme.idealSheafPower J.toModulesι s).1 F |>.1
    have := Scheme.Modules.isQuasicoherent_cokernel b
    have := Scheme.Modules.isQuasicoherent_kernel (cokernel.π b)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage b) inferInstance
  have hQq : Q.IsQuasicoherent := by
    change (cokernel (Scheme.idealModuleProductι
      (Scheme.idealSheafPower J.toModulesι s).2 F)).IsQuasicoherent
    exact Scheme.Modules.isQuasicoherent_cokernel _
  have hQfin : Module.Finite Γ(X, U.1) Γ(Q, U.1) :=
    Scheme.Modules.coherent_affine_sections_finite X Q hQcoh U.1 U.2
  letI : Module.Finite Γ(X, U.1) Γ(Q, U.1) := hQfin
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let v : Γ(F, U.1) →ₗ[Γ(X, U.1)] Γ(Q, U.1) :=
    (E.map (formalModuleQuotientπ J s F)).hom
  have hqc := Scheme.Modules.quasiCoherent_cokernel_image
    (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι s).2 F)
  have hv : Function.Surjective v := hqc.2.2.2.2.2.2.2.2 U |>.2.1
  have hk : LinearMap.ker v = J.ideal U ^ s • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) := by
    change LinearMap.ker ((cokernel.π
      (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι s).2 F)).val.app
      (op U.1)).hom = _
    rw [hqc.2.2.2.2.2.2.2.2 U |>.2.2.1]
    let i := (Scheme.idealSheafPower J.toModulesι s).2
    have hp : (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) = J.ideal U ^ s := by
      simpa [i] using Scheme.Modules.powers_range J U s hs
    have hr := Scheme.Modules.multiplication_range i F U
    dsimp only at hr
    rw [hp] at hr
    exact SetLike.coe_injective hr
  let e := v.quotKerEquivOfSurjective hv
  letI : Module.Finite Γ(X, U.1)
      (Γ(F, U.1) ⧸ LinearMap.ker v) := Module.Finite.equiv e.symm
  letI : Module.Finite Γ(X, U.1)
      (Γ(F, U.1) ⧸ (J.ideal U ^ s • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)))) := hk ▸ inferInstance
  have hHfin : Module.Finite Γ(X, U.1) Γ(H.obj, U.1) :=
    Scheme.Modules.coherent_affine_sections_finite X H.obj H.property U.1 U.2
  letI : Module.Finite Γ(X, U.1) (E.obj H.obj) := by
    change Module.Finite Γ(X, U.1) Γ(H.obj, U.1)
    exact hHfin
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hcover : ∀ x : X, ∃ V ∈ (Set.univ : Set X.affineOpens), x ∈ V.1 := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) from trivial)
        (⊤ : X.Opens).2
    exact ⟨⟨V, hV⟩, Set.mem_univ _, hx⟩
  have hz := (Scheme.idealPowerProduct_isZero_iff_affine_cover X (kernel a)
    J Set.univ hcover s).mp hker U (Set.mem_univ _)
  have ha : ∀ r ∈ J.ideal U ^ s, ∀ x : Γ(F, U.1),
      (E.map a).hom x = 0 → r • x = 0 := by
    intro r hr x hx
    obtain ⟨y, hy⟩ := (Set.ext_iff.mp (Scheme.Modules.range_map_kernelι U.1 a)
      x).mpr (LinearMap.mem_ker.mp hx)
    rw [← hy]
    exact ((E.map (kernel.ι a)).hom.map_smul r y).symm.trans
      (by rw [Module.mem_annihilator.mp (hz hr) y, map_zero])
  exact finite_of_quotient_and_torsion_kernel (J.ideal U ^ s)
    (E.map a).hom ha


set_option backward.isDefEq.respectTransparency false in
/-- A fixed quasi-coherent candidate is coherent if its quotient by a positive ideal
power is coherent and that same power annihilates the kernel of a map to a coherent module.

Source: Stacks Project, Tag 0889(1), finiteness paragraph, and Tag 05EU.
(blueprint: lem-weil-pbc-coherent-of-formal-quotients-torsion-kernel).

Proof: on X = Spec A let P and M be the sections of F and H, and let I be the
sections of J. Exactness of affine sections identifies the kernel of a with
ker(P -> M), killed by I^s. The formal quotient at level s has finite sections,
namely P/I^s P. The image in the finite module M is finite since A is Noetherian.
Choose a finite submodule L of P containing lifts of generators of both this image
and P/I^s P. Surjectivity onto the image gives P = L + ker a, so I^s P is contained
in L because I^s ker a = 0. Surjectivity onto the quotient gives P = L + I^s P.
Thus P=L is finite. The affine finite-type criterion and the Noetherian coherence
criterion give coherence. This works also for I=0, I=A, and the empty spectrum. -/
theorem coherent_of_formalQuotients_and_torsionKernel
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (H : CoherentModules X) (a : F ⟶ H.obj)
    (s : ℕ) (hs : 1 ≤ s)
    (hquot : RingedSpace.IsCoherent X.toRingedSpace
      (((formalCompletionFunctor J).obj F).obj (op (s - 1))))
    (hker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
      (kernel a))) :
    RingedSpace.IsCoherent X.toRingedSpace F := by
  let hq : F.IsQuasicoherent := inferInstance
  have hfin : ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U) := by
    intro U hU
    exact finite_sections_of_formalQuotient_and_torsionKernel J F H a s hs hquot hker ⟨U, hU⟩
  have hpair := (Scheme.Modules.quasicoherent_finite_type_affine X).2 F hq |>.2.1
      Unit (fun _ ↦ (⊤ : X.Opens)) (by simp) (fun _ ↦ isAffineOpen_top X)
      (fun _ ↦ hfin ⊤ (isAffineOpen_top X))
  have hft : F.IsFiniteType := hpair.1
  exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mpr ⟨hq, hft⟩

end AlgebraicGeometry
