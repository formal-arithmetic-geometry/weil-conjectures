/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.CoherentAffineSectionsFinite
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import all Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

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
  sorry

end AlgebraicGeometry
