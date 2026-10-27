/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Fpqc descent of finite type for quasi-coherent modules

Source: Stacks Project, Descent, Tag 05AZ, lemma-finite-type-descends
(blueprint: lem-sfb-fpqc-finite-type-module-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

private theorem finite_pi_tensor {R : Type u} [CommRing R]
    {J : Type v} [Finite J] (A : J → Type u) [∀ j, CommRing (A j)]
    [∀ j, Algebra R (A j)] (M : Type u) [AddCommGroup M] [Module R M]
    [∀ j, Module.Finite (A j) (A j ⊗[R] M)] :
    Module.Finite (∀ j, A j) ((∀ j, A j) ⊗[R] M) := by
  classical
  let := Fintype.ofFinite J
  let B := ∀ j, A j
  let N := fun j ↦ A j ⊗[R] M
  let : ∀ j, Module B (N j) := fun j ↦ Module.compHom _ (Pi.evalRingHom A j)
  have hfin (j : J) : Module.Finite B (N j) := by
    let q : N j →ₛₗ[Pi.evalRingHom A j] N j :=
      { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    exact (LinearMap.finite_iff_of_bijective q Function.bijective_id).mpr inferInstance
  let e := TensorProduct.piLeft R M A
  have he (a : B) (m : M) (j : J) : e (a ⊗ₜ[R] m) j = a j ⊗ₜ[R] m := rfl
  let eB : B ⊗[R] M ≃ₗ[B] ∀ j, N j :=
    { e.toAddEquiv with
      map_smul' := by
        intro b t
        change e (b • t) = b • e t
        induction t using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | tmul a m =>
          rw [TensorProduct.smul_tmul']
          ext j
          change e ((b * a) ⊗ₜ[R] m) j = b j • e (a ⊗ₜ[R] m) j
          rw [he, he]
          exact (TensorProduct.smul_tmul' (b j) (a j) m).symm
        | add t t' ht ht' => simp only [smul_add, map_add, ht, ht'] }
  exact Module.Finite.equiv eB.symm

private theorem finite_affine_tensor {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) (hF : F.IsQuasicoherent)
    (hfinite : ((tensorPullback f).obj F).IsFiniteType)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    Module.Finite Γ(Y, V.1) (Γ(Y, V.1) ⊗[Γ(X, U.1)] Γ(F, U.1)) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : ∀ G : X.Modules, Module Γ(X, U.1) Γ((tensorPullback f).obj G, V.1) :=
    fun G ↦ Module.compHom _ (f.appLE U.1 V.1 hVU).hom
  obtain ⟨c, hc, hsmul, _, _⟩ := exists_tensorPullback_affine_sections f U V hVU
  let e : (Γ(Y, V.1) ⊗[Γ(X, U.1)] Γ(F, U.1)) ≃ₗ[Γ(Y, V.1)]
      Γ((tensorPullback f).obj F, V.1) :=
    LinearEquiv.ofBijective
      { toFun := fun t ↦ c F hF (TensorProduct.comm _ _ _ t)
        map_add' := by intros; simp
        map_smul' := by
          intro b t
          simpa only [TensorProduct.comm_comm, TensorProduct.comm_symm, RingHom.id_apply] using
            hsmul F hF b (TensorProduct.comm _ _ _ t) }
      ((hc F hF).comp (TensorProduct.comm _ _ _).bijective)
  have : F.IsQuasicoherent := hF
  have : ((tensorPullback f).obj F).IsFiniteType := hfinite
  have : Module.Finite Γ(Y, V.1) Γ((tensorPullback f).obj F, V.1) :=
    finite_sections_of_finiteType _ V.2
  exact Module.Finite.equiv e.symm

private theorem module_finite_sections_of_fpqc_tensorPullback
    {X : Scheme.{u}} (F : X.Modules)
    (hF : F.IsQuasicoherent) {I : Type v} (Y : I → Scheme.{u})
    (f : ∀ i, Y i ⟶ X) (hf : Presieve.ofArrows Y f ∈ fpqcPrecoverage X)
    (hfinite : ∀ i, ((tensorPullback (f i)).obj F).IsFiniteType)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(F, U) := by
  classical
  let E : PreZeroHypercover X := ⟨I, Y, f⟩
  have : QuasiCompactCover E := presieve₀_mem_qcPrecoverage_iff.mp hf.1
  have hflat : ∀ i, Flat (f i) := ((ofArrows_mem_precoverage_iff @Flat).mp hf.2).2
  obtain ⟨n, a, V, hV, hcover⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact E hU.isCompact
  have hVU (j : Fin n) : V j ≤ f (a j) ⁻¹ᵁ U := by
    intro x hx
    have : f (a j) x ∈ ⋃ j, f (a j) '' (V j) :=
      Set.mem_iUnion.mpr ⟨j, ⟨x, hx, rfl⟩⟩
    rwa [hcover] at this
  let R := Γ(X, U)
  let A (j : Fin n) := Γ(Y (a j), V j)
  let g (j : Fin n) : R →+* A j := (f (a j) |>.appLE U (V j) (hVU j)).hom
  have hg (j : Fin n) : (g j).Flat := by
    have : Flat (f (a j)) := hflat _
    exact (f (a j)).flat_appLE hU (hV j) (hVU j)
  let : ∀ j, Algebra R (A j) := fun j ↦ (g j).toAlgebra
  have : ∀ j, Module.Flat R (A j) := hg
  have hpi : (RingHom.pi g).Flat := by
    change Module.Flat R (∀ j, A j)
    exact Module.Flat.of_linearEquiv
      (DirectSum.linearEquivFunOnFintype R (Fin n) (fun j ↦ ↥(A j))).symm
  have hff : (RingHom.pi g).FaithfullyFlat := by
    apply RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
    refine ⟨hpi, ?_⟩
    intro p
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso hU.isoSpec.hom.base).surjective p
    have hxc : x.1 ∈ ⋃ j, f (a j) '' (V j) := by rw [hcover]; exact x.2
    obtain ⟨j, y, hy, hyx⟩ := Set.mem_iUnion.mp hxc
    let q := (hV j).primeIdealOf ⟨y, hy⟩
    have hq : PrimeSpectrum.comap (g j) q = p := by
      rw [IsAffineOpen.comap_primeIdealOf_appLE U hU (V j) (hV j) (hVU j) hy]
      have hxy : (⟨f (a j) y, hVU j hy⟩ : U) = x := Subtype.ext hyx
      change hU.isoSpec.hom ⟨f (a j) y, hVU j hy⟩ = p
      rw [hxy]
      exact hx
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j ↦ ↥(A j)) j) q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]
    exact hq
  have : Module.FaithfullyFlat R (∀ j, A j) := hff
  have hfin (j : Fin n) : Module.Finite (A j) (A j ⊗[R] Γ(F, U)) :=
    finite_affine_tensor (f (a j)) F hF (hfinite (a j)) ⟨U, hU⟩ ⟨V j, hV j⟩ (hVU j)
  have : Module.Finite (∀ j, A j) ((∀ j, A j) ⊗[R] Γ(F, U)) :=
    finite_pi_tensor (R := ↥R) (fun j ↦ ↥(A j)) Γ(F, U)
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (∀ j, A j)



/-- A quasi-coherent module is of finite type if its tensor pullbacks along an fpqc
covering are of finite type. The covering index type is arbitrary, including empty.
Source: Stacks Project, Descent, Tag 05AZ, lemma-finite-type-descends
(blueprint: lem-sfb-fpqc-finite-type-module-descent).

Proof:
1. Fix an affine open U of X, with coordinate ring R and module M = F(U). Restrict
   the fpqc covering to U. Flatness is unchanged on the corresponding local rings;
   finite affine refinements of affine opens of U are supplied by the original
   fpqc covering (def-weil-pbc-fpqc-covering, def-weil-flat-morphism).
2. Apply lem-weil-pbc-fpqc-affine-standard-refinement over U. This gives finitely
   many affine opens V_j in covering members, with coordinate rings A_j, such that
   R maps faithfully flatly to B = product_j A_j.
3. By lem-weil-pbc-module-pullback-quasi-coherent, each pullback is quasi-coherent.
   Its finite-type hypothesis and lem-weil-pbc-quasi-coherent-finite-type-affine (a)
   make its sections on V_j finite over A_j. The canonical isomorphism of
   lem-weil-pbc-module-pullback-affine-sections identifies these with M tensor_R A_j;
   tensor symmetry therefore makes A_j tensor_R M finite over A_j.
4. Identify B tensor_R M with product_j (A_j tensor_R M) by coordinate projection.
   Its inverse sums the tensor maps induced by the R-linear coordinate insertions.
   Projection after insertion is the identity in the matching coordinate and zero
   elsewhere; the sum of the inserted coordinates is the original element of B.
   These maps are B-linear, since b times insertion_j(a) is insertion_j(b_j a).
   Insert finite generators in each coordinate; their finite union generates the
   product over B. For an empty finite refinement both tensor and product are zero.
5. Apply lem-weil-pbc-faithfully-flat-descent-finite-module, namely
   Module.Finite.of_finite_tensorProduct_of_faithfullyFlat, to deduce M is finite over R.
6. On an affine open covering of X, all sections are now finite. Clause (c) of
   lem-weil-pbc-quasi-coherent-finite-type-affine gives finite type of F. No finite
   cover of X is required. On an empty X, the finite-type condition is vacuous,
   including when the original fpqc covering is empty (pqf-def-coherent). -/
theorem isFiniteType_of_fpqc_tensorPullback {X : Scheme.{u}} (F : X.Modules)
    (hF : F.IsQuasicoherent) {I : Type v} (Y : I → Scheme.{u})
    (f : ∀ i, Y i ⟶ X) (hf : Presieve.ofArrows Y f ∈ fpqcPrecoverage X)
    (hfinite : ∀ i, ((tensorPullback (f i)).obj F).IsFiniteType) : F.IsFiniteType := by
  let hcriterion := quasicoherent_finite_type_affine X
  have hsections : ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U) :=
    fun U hU ↦ module_finite_sections_of_fpqc_tensorPullback F hF Y f hf hfinite hU
  let A := X.affineCover
  let U : A.I₀ → X.Opens := fun i ↦ (A.f i).opensRange
  have htop : (⨆ i, U i) = ⊤ := by
    change (⨆ i, (A.f i).opensRange) = ⊤
    exact A.iSup_opensRange
  have hfiniteType : ∀ i, Module.Finite Γ(X, U i) Γ(F, U i) :=
    fun i ↦ hsections (U i) (isAffineOpen_opensRange (A.f i))
  exact hcriterion.2 F hF |>.2.1 A.I₀ U htop
    (fun i ↦ isAffineOpen_opensRange (A.f i)) hfiniteType |>.1

end AlgebraicGeometry.Scheme.Modules
