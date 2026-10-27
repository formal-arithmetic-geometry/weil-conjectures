/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.Separable

import Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Unramified.Locus
import WeilConjectures.AlgebraicGeometry.Morphisms.FormallyUnramifiedStalkNeighbourhood

/-!
# Fibrewise unramified locus and base change

Source: Stacks Project, Morphisms, Tags 0475 and 02GF
(blueprint: lem-trf-unramified-locus-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem support_baseChange_iff {A B M : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (q : PrimeSpectrum B) :
    q ∈ Module.support B (TensorProduct A B M) ↔
      q.comap (algebraMap A B) ∈ Module.support A M := by
  let p := q.comap (algebraMap A B)
  let : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) rfl).toAlgebra
  have : IsScalarTower A p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    .of_algebraMap_eq fun a ↦ (Ideal.ResidueField.map_algebraMap _ _ _ rfl a).symm
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A B q.asIdeal.ResidueField
    q.asIdeal.ResidueField M
  rw [e.toEquiv.nontrivial_congr]
  let e' := TensorProduct.AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField
    q.asIdeal.ResidueField q.asIdeal.ResidueField M
  rw [← e'.toEquiv.nontrivial_congr]
  have : Module.Free p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    Module.Free.of_divisionRing _ _
  have : Module.FaithfullyFlat p.asIdeal.ResidueField q.asIdeal.ResidueField := by
    refine { toFlat := Module.Flat.of_free, submodule_ne_top := ?_ }
    intro m hm
    have hm0 : m = ⊥ := (Ideal.eq_bot_or_top m).resolve_right hm.ne_top
    simpa only [hm0, Submodule.bot_smul] using
      (bot_ne_top : (⊥ : Submodule p.asIdeal.ResidueField q.asIdeal.ResidueField) ≠ ⊤)
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right _ _

private theorem unramifiedAt_baseChange_iff
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.IsPushout R B A C]
    [Algebra.EssFiniteType R A] (q : PrimeSpectrum C) :
    Algebra.IsUnramifiedAt B q.asIdeal ↔
      Algebra.IsUnramifiedAt R (q.comap (algebraMap A C)).asIdeal := by
  change q ∈ Algebra.unramifiedLocus B C ↔
    q.comap (algebraMap A C) ∈ Algebra.unramifiedLocus R A
  rw [Algebra.unramifiedLocus_eq_compl_support,
    Algebra.unramifiedLocus_eq_compl_support]
  simp only [Set.mem_compl_iff]
  rw [← (KaehlerDifferential.tensorKaehlerEquiv R B A C).support_eq]
  exact not_congr (support_baseChange_iff q)

private theorem formallyUnramified_stalkMap_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    let := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyUnramified ↔
      Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  dsimp only
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyUnramified_algebraMap]
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · constructor
    · intro h
      have := h
      have : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime p) :=
        .of_isLocalization p.primeCompl
      exact Algebra.FormallyUnramified.comp _ (Localization.AtPrime p) _
    · intro h
      have := h
      exact Algebra.FormallyUnramified.of_restrictScalars Γ(Y, U) _ _

private theorem formallyUnramified_stalkMap_baseChange_iff
    {P X Y S : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback a b f g) [LocallyOfFiniteType f] (x : P) :
    (b.stalkMap x).hom.FormallyUnramified ↔
      (f.stalkMap (a x)).hom.FormallyUnramified := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (a x))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  have hyU : g (b x) ∈ U := by
    rwa [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (g ⁻¹ᵁ U).isOpen
  let T := a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ W
  have hT : IsAffineOpen T := by
    have : IsAffine (Scheme.Opens.toScheme U) := hU
    have : IsAffine (Scheme.Opens.toScheme V) := hV
    have : IsAffine (Scheme.Opens.toScheme W) := hW
    exact IsAffine.of_isPullback (Scheme.Hom.isPullback_resLE sq hWU hVU rfl)
  have hxT : x ∈ T := ⟨hxV, hxW⟩
  let ra := f.appLE U V hVU
  let rb := g.appLE U W hWU
  let ac := a.appLE V T inf_le_left
  let bc := b.appLE W T inf_le_right
  let : Algebra Γ(S, U) Γ(X, V) := ra.hom.toAlgebra
  let : Algebra Γ(S, U) Γ(Y, W) := rb.hom.toAlgebra
  let : Algebra Γ(X, V) Γ(P, T) := ac.hom.toAlgebra
  let : Algebra Γ(Y, W) Γ(P, T) := bc.hom.toAlgebra
  let : Algebra Γ(S, U) Γ(P, T) := (ac.hom.comp ra.hom).toAlgebra
  have heq : ac.hom.comp ra.hom = bc.hom.comp rb.hom := by
    change (ra ≫ ac).hom = (rb ≫ bc).hom
    congr 1
    simp only [ra, rb, ac, bc, Scheme.Hom.appLE_comp_appLE, sq.w]
  have : IsScalarTower Γ(S, U) Γ(X, V) Γ(P, T) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(S, U) Γ(Y, W) Γ(P, T) :=
    .of_algebraMap_eq fun r ↦ RingHom.congr_fun heq r
  have : Algebra.IsPushout Γ(S, U) Γ(Y, W) Γ(X, V) Γ(P, T) := by
    apply CommRingCat.isPushout_iff_isPushout.mp
    exact (isIso_pushoutSection_iff sq hWU hVU rfl).mp
      (isIso_pushoutSection_of_isAffineOpen sq hWU hVU rfl hU hW hV) |>.flip
  have : Algebra.EssFiniteType Γ(S, U) Γ(X, V) := (f.finiteType_appLE hU hV hVU).essFiniteType
  have hb := formallyUnramified_stalkMap_iff b x W hW T hT inf_le_right hxT
  have hf := formallyUnramified_stalkMap_iff f (a x) U hU V hV hVU hxV
  dsimp only at hb hf
  rw [hb, hf]
  have hp := IsAffineOpen.comap_primeIdealOf_appLE V hV T hT
    (f := a) inf_le_left hxT
  have hr := unramifiedAt_baseChange_iff Γ(S, U) Γ(X, V) Γ(Y, W)
    Γ(P, T) (hT.primeIdealOf ⟨x, hxT⟩)
  change Algebra.IsUnramifiedAt Γ(Y, W) (hT.primeIdealOf ⟨x, hxT⟩).asIdeal ↔
    Algebra.IsUnramifiedAt Γ(S, U)
      ((hT.primeIdealOf ⟨x, hxT⟩).comap ac.hom).asIdeal at hr
  rw [hp] at hr
  exact hr

private theorem isIso_fiber_residue_iff {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsIso ((f.fiber (f x)).residue (f.asFiber x)) ↔
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let q := f.fiberStalkMap x
  obtain ⟨hs, hk, -⟩ := f.fiberStalkMap_surjective_ker_quotientEquiv x
  have : IsLocalHom q.hom := IsLocalHom.of_surjective q.hom hs
  have hc := IsLocalRing.maximalIdeal_comap q.hom
  have he : IsLocalRing.maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) = ⊥ ↔
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [← Ideal.comap_injective_of_surjective q.hom hs |>.eq_iff]
    rw [hc, ← RingHom.ker_eq_comap_bot, hk]
    exact eq_comm
  rw [← he, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (IsLocalRing.residue _) ↔ _
  rw [Function.Bijective, and_iff_left IsLocalRing.residue_surjective,
    RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue]

/-- The union of source opens on which the morphism is unramified.
Source: Stacks Project, Morphisms, Tag 0475
(blueprint: lem-trf-unramified-locus-base-change). -/
def unramifiedLocus {Z S : Scheme.{u}} (h : Z ⟶ S) : Set Z :=
  {z | ∃ O : Z.Opens, z ∈ O ∧ IsUnramified (O.ι ≫ h)}

private theorem mem_unramifiedLocus_iff_stalk
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    x ∈ unramifiedLocus f ↔ (f.stalkMap x).hom.FormallyUnramified := by
  constructor
  · rintro ⟨U, hxU, hft, hd⟩
    have := hft
    have := hd
    have h := FormallyUnramified.stalkMap (U.ι ≫ f) ⟨x, hxU⟩
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.FormallyUnramified.respectsIso.cancel_right_isIso] at h
    exact h
  · intro h
    obtain ⟨U, hxU, hu⟩ := FormallyUnramified.exists_neighbourhood_of_stalkMap f x h
    have := hu
    exact ⟨U, hxU, inferInstance, inferInstance⟩

/-- The unramified locus is open, is characterized by unramified fibre neighbourhoods and
by the fibre residue map with finite separable residue extension, and commutes with base change.
Source: Stacks Project, Morphisms, Tag 0475 and Tag 02GF, (1), (2), (6)
(blueprint: lem-trf-unramified-locus-base-change).

Proof plan: (1) The union defining the locus is the set of points with an unramified source
neighbourhood. Tag 0475 identifies it with the fibrewise locus, proves openness, and proves
arbitrary-base-change compatibility. The forward inclusion also follows by base-changing each
unramified open using `lem-weil-pbc-unramified-base-change-open`.
(2) The fibre morphism is locally of finite type by `lem-weil-pbc-lft-base-change`. Apply
`lem-trf-unramified-maximal-ideal-residue-criterion` to that morphism. Its base is a field,
so the maximal-ideal condition says that the fibre residue map is an isomorphism. The
residue field at `h.asFiber z` is canonically the residue field at `z`; the remaining condition
is finiteness and separability of the residue extension induced by `h`. -/
theorem unramifiedLocus_baseChange
    {Z S : Scheme.{u}} (h : Z ⟶ S) [LocallyOfFiniteType h] :
    IsOpen (unramifiedLocus h) ∧
      (∀ z : Z, z ∈ unramifiedLocus h ↔
        h.asFiber z ∈ unramifiedLocus (h.fiberToSpecResidueField (h z))) ∧
      (∀ z : Z, z ∈ unramifiedLocus h ↔
        IsIso ((h.fiber (h z)).residue (h.asFiber z)) ∧
          (h.residueFieldMap z).hom.Finite ∧
          @Algebra.IsSeparable (S.residueField (h z)) (Z.residueField z) _ _
            (h.residueFieldMap z).hom.toAlgebra) ∧
      (∀ {S' : Scheme.{u}} (k : S' ⟶ S),
        unramifiedLocus (pullback.snd h k) =
          (pullback.fst h k) ⁻¹' unramifiedLocus h) := by
  have hbase {S' : Scheme.{u}} (k : S' ⟶ S) :
      unramifiedLocus (pullback.snd h k) =
        (pullback.fst h k) ⁻¹' unramifiedLocus h := by
    have : LocallyOfFiniteType (pullback.snd h k) := inferInstance
    ext x
    exact (mem_unramifiedLocus_iff_stalk _ _).trans
      ((formallyUnramified_stalkMap_baseChange_iff (.of_hasPullback h k) x).trans
        (mem_unramifiedLocus_iff_stalk _ _).symm)
  refine ⟨?_, ?_, ?_, hbase⟩
  · rw [isOpen_iff_mem_nhds]
    rintro z ⟨O, hzO, hO⟩
    exact Filter.mem_of_superset (O.isOpen.mem_nhds hzO) (fun y hy ↦ ⟨O, hy, hO⟩)
  · intro z
    have he := Set.ext_iff.mp (hbase (S.fromSpecResidueField (h z))) (h.asFiber z)
    change _ ↔ h.fiberι (h z) (h.asFiber z) ∈ unramifiedLocus h at he
    simpa only [Scheme.Hom.fiberι_asFiber, Scheme.Hom.fiberToSpecResidueField] using he.symm
  · intro z
    exact (unramified_neighbourhood_iff_maximalIdeal_residue h z).trans
      (and_congr_left fun _ ↦ (isIso_fiber_residue_iff h z).symm)

end AlgebraicGeometry
