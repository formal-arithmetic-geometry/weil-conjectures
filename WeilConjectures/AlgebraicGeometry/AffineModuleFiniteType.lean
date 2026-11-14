/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence
import WeilConjectures.AlgebraicGeometry.AffinePushforwardFreeEvaluation
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Finite type under the affine module correspondence

## References

* Stacks Project, Tags 0897, 01SB and 01PB
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

section SiteHelpers

universe v w

open SheafOfModules CategoryTheory.Limits

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  {R₀ : Sheaf J RingCat.{u}}
  [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

private theorem finiteType_of_data {M : SheafOfModules.{u} R₀}
    (q : M.LocalGeneratorsData) [hq : q.IsFiniteType] : M.IsFiniteType := by
  have : q.shrink.IsFiniteType := by
    constructor
    intro i
    exact hq.isFiniteType i.2.choose
  constructor
  exact ⟨q.shrink, this⟩

private theorem finiteType_of_generators {M : SheafOfModules.{u} R₀}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasBinaryProducts C] (g : M.GeneratingSections) [g.IsFiniteType] :
    M.IsFiniteType := by
  have : g.localGeneratorsData.IsFiniteType := by
    constructor
    intro x
    dsimp [SheafOfModules.GeneratingSections.localGeneratorsData]
    infer_instance
  exact finiteType_of_data g.localGeneratorsData

private theorem finiteType_of_iso {M N : SheafOfModules.{u} R₀} (e : M ≅ N)
    [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have : q'.IsFiniteType := by
    constructor
    intro i
    have := hq.isFiniteType i
    exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType
  exact finiteType_of_data q'

end SiteHelpers

private theorem affine_generators_cover {X : Scheme.{u}}
    {S : X.toTopCat.Sheaf RingCat.{u}} (M : SheafOfModules.{u} S) [M.IsFiniteType] :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} M, q.IsFiniteType ∧ ∀ i, IsAffineOpen (q.X i) := by
  classical
  obtain ⟨p, hp⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let q : M.LocalGeneratorsData :=
    { I := Σ i : p.I, { V : X.affineOpens // V.1 ≤ p.X i }
      X i := i.2.1.1
      coversTop := by
        apply (Opens.coversTop_iff _ _).mpr
        apply eq_top_iff.mpr
        intro x _
        have hx : x ∈ ⨆ i, p.X i := by
          rw [(Opens.coversTop_iff _ _).mp p.coversTop]
          trivial
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
        obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset hi
        exact Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨V, hV⟩, hle⟩⟩, hxV⟩
      generators i :=
        ((p.generators i.1).map (SheafOfModules.overMap S (homOfLE i.2.2))
          (SheafOfModules.overMapUnitIso (R := S) (homOfLE i.2.2)).symm).ofEpi
            ((SheafOfModules.overFunctorMap S (homOfLE i.2.2)).app M).hom }
  refine ⟨q, ?_, fun i ↦ i.2.1.2⟩
  constructor
  intro i
  have := hp.isFiniteType i.1
  dsimp [q]
  infer_instance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "AR" => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj A
set_option hygiene false in
local notation "PUSH" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := AR) (R := U.ringCatSheaf) (𝟙 AR)

set_option maxHeartbeats 400000 in
-- The explicit finite-free section calculation needs extra elaboration heartbeats.
/-- On one affine open, finite global generators of the direct image over its
sectionwise algebra are equivalent to finite generation of the inverse-image sections
(Stacks, Tags 01SB, 01PB, 0897). -/
private theorem affine_pushforward_finite_generators [IsAffineHom f]
    (F : U.Modules) (hF : F.IsQuasicoherent) (V : X.Opens) (hV : IsAffineOpen V) :
    (∃ σ : ((PUSH).obj F |>.over V).GeneratingSections, Finite σ.I) ↔
      Module.Finite Γ(U, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V)  := by
  classical
  let N := ((PUSH).obj F).over V
  let T : Over V := Over.mk (𝟙 V)
  constructor
  · rintro ⟨σ, hσ⟩
    let : Fintype σ.I := Fintype.ofFinite σ.I
    have hf : Module.Finite (((AR).over V).obj.obj (.op T))
        ((SheafOfModules.free (R := (AR).over V) σ.I).val.obj (.op T)) :=
      Module.Finite.equiv
        (SheafOfModules.freeSectionsLinearEquiv (R := (AR).over V) σ.I (.op T)).symm
    have hsurj := (affine_pushforward_free_evaluation f F hF V hV σ.I σ.s).mp σ.epi
    exact Module.Finite.of_surjective (σ.π.val.app (.op T)).hom hsurj
  · intro h
    have : Module.Finite (((AR).over V).obj.obj (.op T)) (N.val.obj (.op T)) := h
    obtain ⟨k, t, ht⟩ := Module.Finite.exists_fin
      (R := ((AR).over V).obj.obj (.op T)) (M := N.val.obj (.op T))
    let τ (W : (Over V)ᵒᵖ) : W.unop ⟶ T :=
      Over.homMk W.unop.hom (by simp [T])
    let s : ULift.{u} (Fin k) → N.sections := fun i ↦
      PresheafOfModules.sectionsMk
        (fun W ↦ N.val.map (τ W).op (t i.down))
        (fun W Z g ↦ by
          change N.val.presheaf.map g (N.val.presheaf.map (τ W).op (t i.down)) =
            N.val.presheaf.map (τ Z).op (t i.down)
          rw [← Functor.map_comp_apply]
          have hcomp : (τ W).op ≫ g = (τ Z).op := by
            apply Quiver.Hom.unop_inj
            exact CategoryTheory.Over.mkIdTerminal.hom_ext _ _
          rw [hcomp])
    let φ := N.freeHomEquiv.symm s
    have hsurj : Function.Surjective (φ.val.app (.op T)) := by
      let L := (φ.val.app (.op T)).hom
      apply LinearMap.range_eq_top.mp
      apply top_unique
      rw [← ht]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      refine ⟨(SheafOfModules.freeSection (R := (AR).over V)
        (ULift.up i : ULift.{u} (Fin k))).1 (.op T), ?_⟩
      have he := congrArg (fun a : N.sections ↦ a.1 (.op T))
        (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s (ULift.up i))
      have hτ : τ (.op T) = 𝟙 T := by
        exact CategoryTheory.Over.mkIdTerminal.hom_ext _ _
      change (φ.val.app (.op T))
        ((SheafOfModules.freeSection (R := (AR).over V)
          (ULift.up i : ULift.{u} (Fin k))).1 (.op T)) =
            N.val.presheaf.map (τ (.op T)).op (t i) at he
      rw [hτ] at he
      simpa only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using he
    have hφ : Epi φ :=
      (affine_pushforward_free_evaluation f F hF V hV (ULift.{u} (Fin k)) s).mpr hsurj
    exact ⟨{ I := ULift.{u} (Fin k), s := s, epi := hφ }, inferInstance⟩


set_option hygiene false in
local notation "R" => PUSH

/-- Finite type is preserved in both directions by the affine module correspondence, where
the direct image carries its sectionwise action by `A = f_* O_U` (Stacks, Tags 0897, 01SB,
01PB). -/
theorem affine_module_finite_type [IsAffineHom f]
    (M : SheafOfModules.{u} AR) (hM : M.IsQuasicoherent)
    (F : U.Modules) (hF : F.IsQuasicoherent) (e : (R).obj F ≅ M) :
    M.IsFiniteType ↔ F.IsFiniteType := by
  classical
  have _ : M.IsQuasicoherent := hM
  let N := (R).obj F
  have hcriterion := (quasicoherent_finite_type_affine.{u, u} U).2 F hF
  constructor
  · intro h
    have : N.IsFiniteType := finiteType_of_iso (R₀ := AR) e.symm
    obtain ⟨q, hq, hqa⟩ := affine_generators_cover N
    have hcover : (⨆ i, f ⁻¹ᵁ q.X i) = ⊤ := by
      apply eq_top_iff.mpr
      intro y _
      have hy : f.base y ∈ ⨆ i, q.X i := by
        rw [(Opens.coversTop_iff _ _).mp q.coversTop]
        trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
      exact Opens.mem_iSup.mpr ⟨i, hi⟩
    exact (hcriterion.2.1 q.I
      (fun i ↦ f ⁻¹ᵁ q.X i) hcover (fun i ↦ (hqa i).preimage f)
      (fun i ↦ (affine_pushforward_finite_generators f F hF (q.X i) (hqa i)).mp
        ⟨q.generators i, (hq.isFiniteType i).finite⟩)).1
  · intro h
    obtain ⟨q, hq, hqa⟩ := affine_generators_cover F
    have hsections :=
      (hcriterion.2.1 q.I q.X
        ((Opens.coversTop_iff _ _).mp q.coversTop) hqa (fun i ↦ by
          have := hq.isFiniteType i
          exact (hcriterion.1
            (q.X i) (hqa i)).1.mp
              (finiteType_of_generators (R₀ := U.ringCatSheaf.over (q.X i)) (q.generators i)))).2
    have hgen (V : X.affineOpens) :
        ∃ σ : (N.over V.1).GeneratingSections, Finite σ.I :=
      (affine_pushforward_finite_generators f F hF V.1 V.2).mpr
        (hsections (f ⁻¹ᵁ V.1) (V.2.preimage f))
    choose σ hσ using hgen
    let p : N.LocalGeneratorsData :=
      { I := X.affineOpens
        X V := V.1
        coversTop := by
          apply (Opens.coversTop_iff _ _).mpr
          apply eq_top_iff.mpr
          intro x _
          obtain ⟨V, hV, hxV, -⟩ :=
            exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
          exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩
        generators V := σ V }
    have : p.IsFiniteType := by
      constructor
      intro V
      exact ⟨hσ V⟩
    have : N.IsFiniteType := finiteType_of_data (R₀ := AR) p
    exact finiteType_of_iso (R₀ := AR) e

end
end AlgebraicGeometry.Scheme.Modules
