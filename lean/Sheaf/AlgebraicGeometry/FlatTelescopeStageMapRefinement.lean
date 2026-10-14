/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap

import Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagram
import Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison

/-! # Refining a homotopy map to maps of flat towers

Source: the common-replacement argument in step 3 of the normalized telescope
comparison plan, Stacks Project Tags 06YS, 06YJ and 04VC.
(blueprint: lem-sc-flat-telescope-stage-map-refinement).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem telescope_shift_presentation (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (k : ℤ) :
    ∃ P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      isFlatTelescope Y P' ∧ Nonempty
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P' ≅
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)⟦k⟧) := by
  obtain ⟨E, t, hb, hf, rfl⟩ := hP
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let S := shiftFunctor (CochainComplex A ℤ) k
  let E' := fun n ↦ S.obj (E n)
  let t' := fun n ↦ S.map (t n)
  let φ := flatTelescopeDifferential E t
  let φ' := flatTelescopeDifferential E' t'
  let σ : (∐ E') ⟶ S.obj (∐ E) := Limits.sigmaComparison S E
  have hb' : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → Limits.IsZero ((E' n).X i) := by
    intro n
    obtain ⟨b, hb⟩ := hb n
    refine ⟨b - k, fun i hi ↦ ?_⟩
    change Limits.IsZero ((E n).X (i + k))
    exact hb (i + k) (by omega)
  have hf' : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E' n).X i) :=
    fun n i ↦ hf n (i + k)
  have hc : φ' ≫ σ = σ ≫ S.map φ := by
    dsimp [φ', φ, flatTelescopeDifferential]
    rw [Functor.map_sub, CategoryTheory.Functor.map_id, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.id_comp, Category.comp_id]
    congr 1
    apply Limits.Sigma.hom_ext
    intro n
    rw [Limits.Sigma.ι_desc_assoc]
    change S.map (t n) ≫ Limits.Sigma.ι (fun n ↦ S.obj (E n)) (n + 1) ≫
        Limits.sigmaComparison S E = Limits.Sigma.ι (fun n ↦ S.obj (E n)) n ≫
        Limits.sigmaComparison S E ≫
          S.map (Limits.Sigma.desc (fun n ↦ t n ≫ Limits.Sigma.ι E (n + 1)))
    rw [Limits.ι_comp_sigmaComparison, Limits.ι_comp_sigmaComparison_assoc, ← S.map_comp,
      ← S.map_comp, Limits.Sigma.ι_desc]
  let m := CochainComplex.mappingCone.map φ' (S.map φ) σ σ hc
  have hσ : IsIso σ := by
    dsimp [σ]
    infer_instance
  have hm : IsIso (Q.map m) := by
    exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
      (Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap φ' (S.map φ) σ σ hc))
      (HomotopyCategory.mappingCone_triangleh_distinguished φ')
      (HomotopyCategory.mappingCone_triangleh_distinguished (S.map φ))
      (by exact inferInstanceAs (IsIso (Q.map σ)))
      (by exact inferInstanceAs (IsIso (Q.map σ)))
  refine ⟨CochainComplex.mappingCone φ', ⟨E', t', hb', hf', rfl⟩, ⟨?_⟩⟩
  exact asIso (Q.map m) ≪≫ (Q.mapIso (CochainComplex.mappingCone.shiftIso φ k)).symm ≪≫
    (Q.commShiftIso k).app _

private theorem telescope_presentation (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
    (hX : flatTelescopeShiftRepresentative Y X) :
    ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      isFlatTelescope Y P ∧
        Nonempty ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P ≅ X) := by
  obtain ⟨P, hP, h | h⟩ := hX
  · exact ⟨P, hP, ⟨eqToIso h⟩⟩
  · obtain ⟨P', hP', ⟨e⟩⟩ := telescope_shift_presentation Y P hP 1
    exact ⟨P', hP', ⟨e ≪≫ eqToIso h⟩⟩

private theorem stage_map_of_tower_map (Y : Scheme.{u})
    (E E' : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1)) (t' : ∀ n : ℕ, E' n ⟶ E' (n + 1))
    (a : ∀ n : ℕ, E n ⟶ E' n)
    (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → Limits.IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i))
    (hb' : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → Limits.IsZero ((E' n).X i))
    (hf' : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E' n).X i))
    (comm : flatTelescopeDifferential E t ≫ Limits.Sigma.map a =
      Limits.Sigma.map a ≫ flatTelescopeDifferential E' t')
    {X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)}
    (e : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone (flatTelescopeDifferential E' t')) ≅ X) :
    flatTelescopeStageMap Y
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (CochainComplex.mappingCone.map (flatTelescopeDifferential E t)
          (flatTelescopeDifferential E' t') (Limits.Sigma.map a)
          (Limits.Sigma.map a) comm) ≫ e.hom) := by
  let H := HomotopyCategory
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
  refine ⟨E, E', t, t', a, hb, hf, hb', hf', comm, 0,
    (shiftFunctorZero H ℤ).app _, (shiftFunctorZero H ℤ).app _ ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Iso.app_hom, Iso.app_inv]
  rw [(shiftFunctorZero H ℤ).hom.naturality_assoc]
  simp

/-- A homotopy map between telescope representatives admits a common source
on which it is induced by maps of bounded-flat towers. This assertion contains
no pullback, tensorator, or normalized comparison.

Source: Stacks Project, Tags 06YS and 06YJ, common flat replacement, and Tag 04VC,
right fractions; this explicit tower refinement is the expansion of parent
step 3 rather than a literal assertion of those tags.

Proof. Choose flat-tower presentations of the two objects, with their given
possible one-fold translates. Lift the homotopy morphism to a cochain map.
Resolve the resulting arrow diagram by bounded-above flat truncation towers,
retaining the maps to both original diagrams. At a given truncation level use
a common flat resolution for the source and the pullback of the target
resolution along the arrow; the projections then give a commuting square.
Construct the next level resolving this square together with the previous
level, so the transition squares commute. Taking sums and their transition
cones gives a third flat telescope R and two model maps a and b. The source
augmentation is a quasi-isomorphism by the flat truncation telescope comparison.
Their composites represent the given arrow after localization. Apply the right
fraction equality criterion and refine the source once more to turn that
localized equality into equality in the homotopy category. Compose the two
source refinements; their quasi-isomorphisms compose, and the composite tower
maps are again tower maps. Shift the diagrams and transport by their original
homotopy isomorphisms to cover the translated presentations. Thus a;s=b in the
homotopy category, with a a quasi-isomorphism. For the zero map use the zero
arrow diagram; for the identity use its identical presentations. Empty schemes
have the unique zero diagrams, so no nonzero-object assumption is needed.
(blueprint: lem-sc-flat-telescope-stage-map-refinement). -/
theorem exists_flat_telescope_stage_map_refinement (Y : Scheme.{u})
    {X X' : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)}
    (hX : flatTelescopeShiftRepresentative Y X)
    (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X') :
    ∃ (R : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (a : R ⟶ X) (b : R ⟶ X'),
      flatTelescopeShiftRepresentative Y R ∧
        HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) a ∧
        flatTelescopeStageMap Y a ∧ flatTelescopeStageMap Y b ∧ a ≫ s = b := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  obtain ⟨P, hP, ⟨e⟩⟩ := telescope_presentation Y X hX
  obtain ⟨P', hP', ⟨e'⟩⟩ := telescope_presentation Y X' hX'
  obtain ⟨f, hf⟩ := Q.map_surjective (e.hom ≫ s ≫ e'.inv)
  obtain ⟨E₀, E₁, E₂, t₀, t₁, t₂, c, d, hb₀, hf₀, hb₁, hf₁, hb₂, hf₂,
    comm₁, comm₂, e₁, e₂, g, q, hq, hcompat, hinr, hinl, hgc, hgd⟩ :=
      exists_flat_telescope_arrow_diagram Y P P' hP hP' f
  let φ₀ := flatTelescopeDifferential E₀ t₀
  let φ₂ := flatTelescopeDifferential E₂ t₂
  let m₂ := CochainComplex.mappingCone.map φ₀ φ₂ (Limits.Sigma.map d) (Limits.Sigma.map d) comm₂
  have hg : QuasiIso g :=
    CochainComplex.quasiIso_flat_truncation_telescope P E₀ t₀ q hq hcompat g hinr hinl
  have hQg : W (Q.map g) := (HomotopyCategory.quotient_map_mem_quasiIso_iff g).2 hg
  refine ⟨Q.obj (CochainComplex.mappingCone φ₀), Q.map g ≫ e.hom,
    Q.map m₂ ≫ (e₂ ≪≫ e').hom, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨CochainComplex.mappingCone φ₀, ⟨E₀, t₀, hb₀, hf₀, rfl⟩, Or.inl rfl⟩
  · exact W.comp_mem _ _ hQg (W.of_isIso e.hom)
  · rw [hgc, Category.assoc]
    exact stage_map_of_tower_map Y E₀ E₁ t₀ t₁ c hb₀ hf₀ hb₁ hf₁ comm₁ (e₁ ≪≫ e)
  · exact stage_map_of_tower_map Y E₀ E₂ t₀ t₂ d hb₀ hf₀ hb₂ hf₂ comm₂ (e₂ ≪≫ e')
  · have hgd' : Q.map g ≫ Q.map f = Q.map m₂ ≫ e₂.hom := hgd
    rw [hf] at hgd'
    simpa only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      using congrArg (fun k ↦ k ≫ e'.hom) hgd'

end AlgebraicGeometry
