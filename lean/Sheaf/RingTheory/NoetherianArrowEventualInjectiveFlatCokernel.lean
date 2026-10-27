/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.RingTheory.ColimitEventuallyFlat
import WeilConjectures.RingTheory.FlatOfLocalCriterionBaseChange
import WeilConjectures.RingTheory.FlatModInjective
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.RingTheory.FlatSemilinearEquiv

/-!
# Eventual injectivity and flat cokernels at Noetherian local stages

Source: Stacks Project, Algebra, Tag 046Y, first and final proof paragraphs;
Tags 00R6, 00MO and 00ME.
(blueprint: lem-trf-noetherian-arrow-eventual-injective-flat-cokernel)

Closed fibres are written as residue-field tensor products, canonically the quotients
by maximal-ideal multiples. Scalar extension is written with the scalar ring first.
In particular `k ⊗[Rᵢ] Mᵢ` is canonically `k ⊗[kᵢ] (Mᵢ / mᵢ Mᵢ)`.
The comparison in `h_source` is uniquely specified on pure tensors; its quantified
presentation imposes no choice of an arbitrary map. Scalar tower instances encode
restriction along the displayed ring maps and impose no additional mathematical condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

set_option linter.unusedVariables false in
/-- Eventual flatness of the target, closed-fibre injectivity, injectivity of the arrow,
and flatness of its cokernel. Source: Stacks Project, Algebra, Tag 046Y, first and final
proof paragraphs; Tags 00R6, 00MO and 00ME.
(blueprint: lem-trf-noetherian-arrow-eventual-injective-flat-cokernel)

Proof:
1. Bundle the target module diagram, and use its representatives and eventual
   equalities to identify its group colimit with `N`. Identify the categorical ring
   colimits with the supplied cocones. Transport the scalar actions and flatness via
   `Module.Flat.semilinearEquiv_iff`, and apply `RingTheory.exists_flat_stage`.
   Mathlib supplies preservation of filtered ring colimits by the forgetful functor.
2. Propagate the resulting flat stage `a` to all later stages with
   `lem-weil-pbc-flat-another-variant-local-criterion`, taking its ideal to be zero.
   That ideal is proper since the stage ring is local; its tensor multiplication
   kernel is zero. Transport through `hbaseN`. Choose an upper bound `i₂` of `a` and `i₁`.
3. For each `j ≥ i₂`, locality induces the field embedding `kⱼ → k`.
   Mathlib's `Module.Flat.tensorProduct_mk_injective` makes the map from the stage
   source fibre to its scalar extension injective, including for the zero vector
   space. Tensor cancellation identifies its codomain with `k ⊗[Rⱼ] Mⱼ`.
   Compose with `h_source` to embed that fibre into the limit source fibre.
4. Arrow/cocone compatibility gives the commuting closed-fibre square. If a stage
   fibre element maps to zero, its image in the limit source fibre maps to zero
   under the injective limit fibre arrow `h_fibre`. Step 3 kills the original element.
   No injectivity of the target fibre cocone is used.
5. Apply `lem-weil-pbc-flat-mod-injective` to `ui j`, with finite source `Mi j`,
   flat target `Ni j` and the stage local ring map. It gives injectivity and flatness
   of the quotient by the range. Together with steps 2 and 4 these are all four claims.
-/
theorem eventually_injective_flat_cokernel_of_noetherian_local_stages
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Ri Si : I ⥤ CommRingCat.{u})
    (cR : Cocone Ri) (cS : Cocone Si)
    (hcR : IsColimit cR) (hcS : IsColimit cS)
    [IsLocalRing cR.pt] [IsLocalRing cS.pt]
    [∀ i : I, IsLocalRing (Ri.obj i)] [∀ i : I, IsLocalRing (Si.obj i)]
    [∀ i : I, IsNoetherianRing (Ri.obj i)]
    [∀ i : I, IsNoetherianRing (Si.obj i)]
    [Algebra cR.pt cS.pt] [IsLocalHom (algebraMap cR.pt cS.pt)]
    [∀ i : I, Algebra (Ri.obj i) (Si.obj i)]
    [∀ i : I, Algebra (Ri.obj i) cR.pt]
    [∀ i : I, Algebra (Si.obj i) cS.pt]
    [∀ i : I, Algebra (Ri.obj i) cS.pt]
    [∀ i : I, IsScalarTower (Ri.obj i) (Si.obj i) cS.pt]
    [∀ i : I, IsScalarTower (Ri.obj i) cR.pt cS.pt]
    [∀ i : I, IsLocalHom (algebraMap (Ri.obj i) (Si.obj i))]
    [∀ i : I, IsLocalHom (algebraMap (Ri.obj i) cR.pt)]
    [∀ i : I, IsLocalHom (algebraMap (Si.obj i) cS.pt)]
    (hR_local : ∀ (i j : I) (h : i ≤ j), IsLocalHom (Ri.map (homOfLE h)).hom)
    (hS_local : ∀ (i j : I) (h : i ≤ j), IsLocalHom (Si.map (homOfLE h)).hom)
    (hR : ∀ (i : I), algebraMap (Ri.obj i) cR.pt = (cR.ι.app i).hom)
    (hS : ∀ (i : I), algebraMap (Si.obj i) cS.pt = (cS.ι.app i).hom)
    (h_ring_arrow : ∀ (i j : I) (h : i ≤ j) (r : Ri.obj i),
      (Si.map (homOfLE h)).hom (algebraMap (Ri.obj i) (Si.obj i) r) =
        algebraMap (Ri.obj j) (Si.obj j) ((Ri.map (homOfLE h)).hom r))
    (hR_represent : ∀ r : cR.pt, ∃ (i : I) (a : Ri.obj i), (cR.ι.app i).hom a = r)
    (hS_represent : ∀ s : cS.pt, ∃ (i : I) (a : Si.obj i), (cS.ι.app i).hom a = s)
    (hR_equal : ∀ (i j : I) (a : Ri.obj i) (b : Ri.obj j),
      (cR.ι.app i).hom a = (cR.ι.app j).hom b →
        ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
          (Ri.map (homOfLE hik)).hom a = (Ri.map (homOfLE hjk)).hom b)
    (hS_equal : ∀ (i j : I) (a : Si.obj i) (b : Si.obj j),
      (cS.ι.app i).hom a = (cS.ι.app j).hom b →
        ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
          (Si.map (homOfLE hik)).hom a = (Si.map (homOfLE hjk)).hom b)
    (Mi Ni : I → Type u)
    [∀ i : I, AddCommGroup (Mi i)] [∀ i : I, AddCommGroup (Ni i)]
    [∀ i : I, Module (Si.obj i) (Mi i)] [∀ i : I, Module (Si.obj i) (Ni i)]
    [∀ i : I, Module.Finite (Si.obj i) (Mi i)]
    [∀ i : I, Module.Finite (Si.obj i) (Ni i)]
    [∀ i : I, Module (Ri.obj i) (Mi i)]
    [∀ i : I, IsScalarTower (Ri.obj i) (Si.obj i) (Mi i)]
    [∀ i : I, Module (Ri.obj i) (Ni i)]
    [∀ i : I, IsScalarTower (Ri.obj i) (Si.obj i) (Ni i)]
    (ui : ∀ i : I, Mi i →ₗ[Si.obj i] Ni i)
    (m : ∀ (i j : I), i ≤ j → Mi i →+ Mi j)
    (n : ∀ (i j : I), i ≤ j → Ni i →+ Ni j)
    (hm_smul : ∀ (i j : I) (h : i ≤ j) (s : Si.obj i) (x : Mi i),
      m i j h (s • x) = (Si.map (homOfLE h)).hom s • m i j h x)
    (hn_smul : ∀ (i j : I) (h : i ≤ j) (s : Si.obj i) (y : Ni i),
      n i j h (s • y) = (Si.map (homOfLE h)).hom s • n i j h y)
    (hm_id : ∀ (i : I) (x : Mi i), m i i le_rfl x = x)
    (hn_id : ∀ (i : I) (y : Ni i), n i i le_rfl y = y)
    (hm_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : Mi i),
      m j k hjk (m i j hij x) = m i k (hij.trans hjk) x)
    (hn_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (y : Ni i),
      n j k hjk (n i j hij y) = n i k (hij.trans hjk) y)
    (h_stage_arrow : ∀ (i j : I) (h : i ≤ j) (x : Mi i),
      n i j h (ui i x) = ui j (m i j h x))
    (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [Module cS.pt M] [Module cS.pt N]
    [Module cR.pt M] [IsScalarTower cR.pt cS.pt M]
    [Module cR.pt N] [IsScalarTower cR.pt cS.pt N]
    (mu : ∀ i : I, Mi i →+ M) (nu : ∀ i : I, Ni i →+ N)
    (hmu_smul : ∀ (i : I) (s : Si.obj i) (x : Mi i),
      mu i (s • x) = algebraMap (Si.obj i) cS.pt s • mu i x)
    (hnu_smul : ∀ (i : I) (s : Si.obj i) (y : Ni i),
      nu i (s • y) = algebraMap (Si.obj i) cS.pt s • nu i y)
    (hmu_comp : ∀ (i j : I) (h : i ≤ j) (x : Mi i), mu j (m i j h x) = mu i x)
    (hnu_comp : ∀ (i j : I) (h : i ≤ j) (y : Ni i), nu j (n i j h y) = nu i y)
    (u : M →ₗ[cS.pt] N)
    (h_limit_arrow : ∀ (i : I) (x : Mi i), nu i (ui i x) = u (mu i x))
    (hM_represent : ∀ x : M, ∃ (i : I) (xi : Mi i), mu i xi = x)
    (hN_represent : ∀ y : N, ∃ (i : I) (yi : Ni i), nu i yi = y)
    (hM_equal : ∀ (i j : I) (x : Mi i) (y : Mi j),
      mu i x = mu j y → ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        m i k hik x = m j k hjk y)
    (hN_equal : ∀ (i j : I) (x : Ni i) (y : Ni j),
      nu i x = nu j y → ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        n i k hik x = n j k hjk y)
    (hloc : ∀ (i j : I) (h : i ≤ j),
      letI := (Ri.map (homOfLE h)).hom.toAlgebra
      ∃ (q : Si.obj i ⊗[Ri.obj i] Ri.obj j →+* Si.obj j)
        (W : Submonoid (Si.obj i ⊗[Ri.obj i] Ri.obj j)),
        (∀ (s : Si.obj i) (r : Ri.obj j), q (s ⊗ₜ[Ri.obj i] r) =
          (Si.map (homOfLE h)).hom s * algebraMap (Ri.obj j) (Si.obj j) r) ∧
        (letI := q.toAlgebra; IsLocalization W (Si.obj j)))
    (hbaseM : ∀ (i j : I) (h : i ≤ j),
      letI := (Si.map (homOfLE h)).hom.toAlgebra
      ∃ e : (Si.obj j ⊗[Si.obj i] Mi i) ≃ₗ[Si.obj j] Mi j,
        ∀ (s : Si.obj j) (x : Mi i), e (s ⊗ₜ[Si.obj i] x) = s • m i j h x)
    (hbaseN : ∀ (i j : I) (h : i ≤ j),
      letI := (Si.map (homOfLE h)).hom.toAlgebra
      ∃ e : (Si.obj j ⊗[Si.obj i] Ni i) ≃ₗ[Si.obj j] Ni j,
        ∀ (s : Si.obj j) (x : Ni i), e (s ⊗ₜ[Si.obj i] x) = s • n i j h x)
    [Module.Flat cR.pt N]
    (h_fibre : Function.Injective
      ((u.restrictScalars cR.pt).lTensor (IsLocalRing.ResidueField cR.pt)))
    (i₁ : I)
    (h_source : ∀ j : I, i₁ ≤ j →
      letI := ((algebraMap cR.pt (IsLocalRing.ResidueField cR.pt)).comp
        (algebraMap (Ri.obj j) cR.pt)).toAlgebra
      ∃ Ψ : (IsLocalRing.ResidueField cR.pt ⊗[Ri.obj j] Mi j) →ₗ[
          IsLocalRing.ResidueField cR.pt] (IsLocalRing.ResidueField cR.pt ⊗[cR.pt] M),
        (∀ (c : IsLocalRing.ResidueField cR.pt) (x : Mi j),
          Ψ (c ⊗ₜ[Ri.obj j] x) = c ⊗ₜ[cR.pt] mu j x) ∧ Function.Injective Ψ) :
    ∃ i₂ : I, i₁ ≤ i₂ ∧ ∀ j : I, i₂ ≤ j →
      Module.Flat (Ri.obj j) (Ni j) ∧
        Function.Injective
          (((ui j).restrictScalars (Ri.obj j)).lTensor
            (IsLocalRing.ResidueField (Ri.obj j))) ∧
        Function.Injective (ui j) ∧
        Module.Flat (Ri.obj j) (Ni j ⧸ LinearMap.range ((ui j).restrictScalars (Ri.obj j))) := by
  classical
  let D : I ⥤ AddCommGrpCat.{u} :=
    { obj := fun i ↦ AddCommGrpCat.of (Ni i)
      map := fun f ↦ AddCommGrpCat.ofHom (n _ _ (leOfHom f))
      map_id := fun i ↦ by ext x; exact hn_id i x
      map_comp := fun f g ↦ by ext x; exact (hn_comp _ _ _ _ _ x).symm }
  let cD : Cocone D :=
    { pt := AddCommGrpCat.of N
      ι :=
        { app := fun i ↦ AddCommGrpCat.ofHom (nu i)
          naturality := fun i j f ↦ by ext x; exact hnu_comp i j (leOfHom f) x } }
  let : HasColimit D := HasColimit.mk
    ⟨_, AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit D⟩
  let : PreservesColimit D (forget AddCommGrpCat) :=
    preservesColimit_of_preserves_colimit_cocone
      (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit D)
      (Types.TypeMax.colimitCoconeIsColimit (D ⋙ forget AddCommGrpCat))
  have hcD : IsColimit cD := by
    let : ReflectsColimit D (forget AddCommGrpCat) :=
      reflectsColimit_of_reflectsIsomorphisms D (forget AddCommGrpCat)
    apply isColimitOfReflects (forget AddCommGrpCat)
    apply Types.FilteredColimit.isColimitOf
    · intro x
      obtain ⟨i, y, hy⟩ := hN_represent x
      exact ⟨i, y, hy.symm⟩
    · intro i j x y h
      obtain ⟨k, hik, hjk, hxy⟩ := hN_equal i j x y h
      exact ⟨k, homOfLE hik, homOfLE hjk, hxy⟩
  let eR := (colimit.isoColimitCocone ⟨cR, hcR⟩).commRingCatIsoToRingEquiv
  let eS := (colimit.isoColimitCocone ⟨cS, hcS⟩).commRingCatIsoToRingEquiv
  let eN := (colimit.isoColimitCocone ⟨cD, hcD⟩).addCommGroupIsoToAddEquiv
  have heR (i : I) (r : Ri.obj i) :
      eR ((colimit.ι Ri i).hom r) = algebraMap (Ri.obj i) cR.pt r := by
    rw [hR]
    exact ConcreteCategory.congr_hom (colimit.isoColimitCocone_ι_hom ⟨cR, hcR⟩ i) r
  have heS (i : I) (s : Si.obj i) :
      eS ((colimit.ι Si i).hom s) = algebraMap (Si.obj i) cS.pt s := by
    rw [hS]
    exact ConcreteCategory.congr_hom (colimit.isoColimitCocone_ι_hom ⟨cS, hcS⟩ i) s
  have heN (i : I) (x : Ni i) : eN ((colimit.ι D i).hom x) = nu i x :=
    ConcreteCategory.congr_hom (colimit.isoColimitCocone_ι_hom ⟨cD, hcD⟩ i) x
  let ψ := eS.symm.toRingHom.comp ((algebraMap cR.pt cS.pt).comp eR.toRingHom)
  let : Module (colimit Si : CommRingCat) N := Module.compHom N eS.toRingHom
  let : Module (colimit Si : CommRingCat) (colimit D : AddCommGrpCat) :=
    eN.module (colimit Si : CommRingCat)
  have hψ (i : I) : ψ.comp (colimit.ι Ri i).hom =
      (colimit.ι Si i).hom.comp (algebraMap (Ri.obj i) (Si.obj i)) := by
    ext r
    apply eS.injective
    change eS (eS.symm (algebraMap cR.pt cS.pt (eR ((colimit.ι Ri i).hom r)))) = _
    simp only [RingHom.comp_apply]
    rw [eS.apply_symm_apply, heR, heS]
    exact (IsScalarTower.algebraMap_apply (Ri.obj i) cR.pt cS.pt r).symm.trans
      (IsScalarTower.algebraMap_apply (Ri.obj i) (Si.obj i) cS.pt r)
  have hlimitScalar (i : I) (b : Si.obj i) (x : Ni i) :
      (colimit.ι D i).hom (b • x) =
        (colimit.ι Si i).hom b • (colimit.ι D i).hom x := by
    apply eN.injective
    change eN ((colimit.ι D i).hom (b • x)) =
      eN (eN.symm (eS ((colimit.ι Si i).hom b) • eN ((colimit.ι D i).hom x)))
    rw [eN.apply_symm_apply, heN, heN, heS]
    exact hnu_smul i b x
  have hflat : letI := Module.compHom (colimit D : AddCommGrpCat) ψ
      Module.Flat (colimit Ri : CommRingCat) (colimit D : AddCommGrpCat) := by
    let : Module (colimit Ri : CommRingCat) (colimit D : AddCommGrpCat) :=
      Module.compHom (colimit D : AddCommGrpCat) ψ
    exact (Module.Flat.semilinearEquiv_iff eR eN (fun r x ↦ by
      change eN (eN.symm (eS (ψ r) • eN x)) = eR r • eN x
      rw [eN.apply_symm_apply]
      change eS (eS.symm (algebraMap cR.pt cS.pt (eR r))) • eN x = _
      rw [eS.apply_symm_apply, algebraMap_smul])).mpr inferInstance
  have hloc' : ∀ (i j : I) (f : i ⟶ j),
      letI := (algebraMap (Ri.obj i) (Si.obj i)).toAlgebra
      letI := (Ri.map f).hom.toAlgebra
      ∃ (q : Si.obj i ⊗[Ri.obj i] Ri.obj j →+* Si.obj j)
        (W : Submonoid (Si.obj i ⊗[Ri.obj i] Ri.obj j)),
        (∀ s r, q (s ⊗ₜ[Ri.obj i] r) =
          (Si.map f).hom s * algebraMap (Ri.obj j) (Si.obj j) r) ∧
        (letI := q.toAlgebra; IsLocalization W (Si.obj j)) := by
    intro i j f
    rw [toAlgebra_algebraMap]
    exact hloc i j (leOfHom f)
  obtain ⟨a, ha⟩ := RingTheory.exists_flat_stage Ri Si D
    (fun i ↦ algebraMap (Ri.obj i) (Si.obj i)) (fun _ ↦ inferInstance)
    (fun i j f ↦ hR_local i j (leOfHom f))
    (fun i j f ↦ hS_local i j (leOfHom f))
    (fun i j f ↦ RingHom.ext (h_ring_arrow i j (leOfHom f)))
    (fun i j f ↦ hn_smul i j (leOfHom f)) ψ hψ hlimitScalar hloc'
    (fun i j f ↦ hbaseN i j (leOfHom f)) hflat
  have hcomp (i : I) : Module.compHom (Ni i) (algebraMap (Ri.obj i) (Si.obj i)) =
      (inferInstance : Module (Ri.obj i) (Ni i)) := by
    ext r x
    exact algebraMap_smul (Si.obj i) r x
  rw [hcomp a] at ha
  have htail (j : I) (haj : a ≤ j) : Module.Flat (Ri.obj j) (Ni j) := by
    let : Algebra (Ri.obj a) (Ri.obj j) := (Ri.map (homOfLE haj)).hom.toAlgebra
    let : Algebra (Si.obj a) (Si.obj j) := (Si.map (homOfLE haj)).hom.toAlgebra
    let : Algebra (Ri.obj a) (Si.obj j) :=
      ((Si.map (homOfLE haj)).hom.comp (algebraMap (Ri.obj a) (Si.obj a))).toAlgebra
    have : IsScalarTower (Ri.obj a) (Si.obj a) (Si.obj j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower (Ri.obj a) (Ri.obj j) (Si.obj j) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext (h_ring_arrow a j haj))
    have : IsLocalHom (algebraMap (Ri.obj a) (Ri.obj j)) := hR_local a j haj
    have : IsLocalHom (algebraMap (Si.obj a) (Si.obj j)) := hS_local a j haj
    have : Module.Flat (Ri.obj a) (Ni a) := ha
    have hf := Module.flat_of_local_criterion_baseChange (R := Ri.obj a)
      (S := Si.obj a) (R' := Ri.obj j) (S' := Si.obj j)
      ⊥ bot_ne_top (Ni a) (hloc a j haj) (by infer_instance) 0
      (fun b x ↦ by
        have hb : b = 0 := Subsingleton.elim _ _
        have hb' : (⟨algebraMap (Ri.obj a) (Ri.obj j) b,
            Ideal.mem_map_of_mem (algebraMap (Ri.obj a) (Ri.obj j)) b.property⟩ :
            (⊥ : Ideal (Ri.obj a)).map (algebraMap (Ri.obj a) (Ri.obj j))) = 0 := by
          apply Subtype.ext
          simp [hb]
        simp only [hb', TensorProduct.zero_tmul, AddMonoidHom.zero_apply]) (fun _ _ ↦ rfl)
    obtain ⟨e, _⟩ := hbaseN a j haj
    exact (Module.Flat.equiv_iff (e.restrictScalars (Ri.obj j))).mp hf
  obtain ⟨i₂, h₁, ha₂⟩ := exists_ge_ge i₁ a
  refine ⟨i₂, h₁, fun j hj ↦ ?_⟩
  have := htail j (ha₂.trans hj)
  refine ⟨inferInstance, ?_⟩
  let K := IsLocalRing.ResidueField cR.pt
  let k := IsLocalRing.ResidueField (Ri.obj j)
  obtain ⟨Ψ, hΨ, hinjΨ⟩ := h_source j (h₁.trans hj)
  let t : k ⊗[Ri.obj j] Mi j →ₗ[Ri.obj j] K ⊗[Ri.obj j] Mi j :=
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange
      (Ri.obj j) k k K (Mi j)).toLinearMap.comp
      (TensorProduct.mk k K (k ⊗[Ri.obj j] Mi j) 1)).restrictScalars (Ri.obj j)
  have ht : Function.Injective t :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (Ri.obj j) k k K (Mi j)).injective.comp
        (Module.Flat.tensorProduct_mk_injective k _ K)
  have ht_tmul (c : k) (x : Mi j) :
      t (c ⊗ₜ[Ri.obj j] x) = algebraMap k K c ⊗ₜ[Ri.obj j] x := by
    simp [t, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      Algebra.smul_def]
  let ν : Ni j →ₛₗ[algebraMap (Ri.obj j) cR.pt] N :=
    { toAddHom := nu j
      map_smul' := by
        intro r x
        change nu j (r • x) = algebraMap (Ri.obj j) cR.pt r • nu j x
        rw [← algebraMap_smul (Si.obj j) r x, hnu_smul,
          ← IsScalarTower.algebraMap_apply (Ri.obj j) (Si.obj j) cS.pt,
          IsScalarTower.algebraMap_apply (Ri.obj j) cR.pt cS.pt, algebraMap_smul] }
  let κ : k →ₛₗ[algebraMap (Ri.obj j) cR.pt] K :=
    { toFun := algebraMap k K
      map_add' := map_add _
      map_smul' := by
        intro r c
        change algebraMap k K (r • c) = algebraMap (Ri.obj j) cR.pt r •
          algebraMap k K c
        change algebraMap k K (algebraMap (Ri.obj j) k r * c) =
          algebraMap cR.pt K (algebraMap (Ri.obj j) cR.pt r) * algebraMap k K c
        simp only [map_mul, ← IsScalarTower.algebraMap_apply] }
  let β := TensorProduct.map κ ν
  have hsquare (z : k ⊗[Ri.obj j] Mi j) :
      (u.restrictScalars cR.pt).lTensor K (Ψ (t z)) =
        β (((ui j).restrictScalars (Ri.obj j)).lTensor k z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul c x =>
      rw [ht_tmul, hΨ, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.map_tmul]
      change _ = algebraMap k K c ⊗ₜ[cR.pt] nu j (ui j x)
      rw [h_limit_arrow]
      rfl
  have hfibre : Function.Injective (((ui j).restrictScalars (Ri.obj j)).lTensor k) := by
    intro x y hxy
    apply ht
    apply hinjΨ
    apply h_fibre
    rw [hsquare, hsquare, hxy]
  refine ⟨hfibre, ?_⟩
  let J := IsLocalRing.maximalIdeal (Ri.obj j)
  let v := (ui j).restrictScalars (Ri.obj j)
  let P := J • (⊤ : Submodule (Ri.obj j) (Mi j))
  let Q := J • (⊤ : Submodule (Ri.obj j) (Ni j))
  let bar := P.mapQ Q v (Submodule.smul_top_le_comap_smul_top J v)
  let eM := TensorProduct.quotTensorEquivQuotSMul (Mi j) J
  let eN := TensorProduct.quotTensorEquivQuotSMul (Ni j) J
  have hnat : eN.symm.toLinearMap.comp bar =
      (v.lTensor k).comp eM.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  have hbar : Function.Injective bar := by
    intro x y hxy
    apply eM.symm.injective
    apply hfibre
    change ((v.lTensor k).comp eM.symm.toLinearMap) x =
      ((v.lTensor k).comp eM.symm.toLinearMap) y
    rw [← hnat]
    exact congrArg eN.symm hxy
  have hc : Module.compHom (Mi j) (algebraMap (Ri.obj j) (Si.obj j)) =
      (inferInstance : Module (Ri.obj j) (Mi j)) := by
    ext r x
    exact algebraMap_smul (Si.obj j) r x
  have hcrit := flat_mod_injective (N := Mi j) (M := Ni j)
    (algebraMap (Ri.obj j) (Si.obj j))
    (fun r hr ↦ map_nonunit (algebraMap (Ri.obj j) (Si.obj j)) r hr)
  rw [hc] at hcrit
  exact hcrit v hbar

end Module
