/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.AlgebraicGeometry.FlatTelescopeModelShiftGauge
import Sheaf.AlgebraicGeometry.FlatTelescopeStageMapRefinement
import Sheaf.CategoryTheory.NatTransFromResolvingClass
import Sheaf.Algebra.Homology.FlatTruncationTower
import Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison

/-! # Shift gauge on flat telescope models

Source: the supplied-tensorator calculation in steps 1–2 of
lem-sc-normalized-flat-telescope-stage-comparison; Stacks Tags 06YS and 06YJ
for the model constructions, not for the supplied-tensorator assertion.
(blueprint: lem-sc-flat-telescope-shift-gauge).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

set_option maxHeartbeats 800000 in
-- Elaborating the cone augmentation uses the concrete sheaf coproduct instances.
private theorem exists_flat_telescope_resolution (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    ∃ (R : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (s : R ⟶ P), isFlatTelescope Y R ∧ QuasiIso s := by
  obtain ⟨E, t, q, hbounded, hflat, hq, _, hcompat⟩ :=
    CochainComplex.exists_flat_truncation_tower P
  let a : (∐ E) ⟶ P := Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))
  let φ : (∐ E) ⟶ (∐ E) :=
    𝟙 (∐ E) - Sigma.desc (fun n : ℕ ↦ t n ≫ Sigma.ι E (n + 1))
  have hzero : φ ≫ a = 0 := by
    dsimp [φ, a]
    rw [Preadditive.sub_comp, Category.id_comp]
    apply sub_eq_zero.mpr
    apply Sigma.hom_ext
    intro n
    simp only [Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
    exact (hcompat n).symm
  have hdesc : CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain (∐ E) P (-1)) =
        CochainComplex.HomComplex.Cochain.ofHom (φ ≫ a) := by
    rw [hzero]
    simp
  let s : CochainComplex.mappingCone φ ⟶ P := CochainComplex.mappingCone.desc φ 0 a hdesc
  have hinr : CochainComplex.mappingCone.inr φ ≫ s = a :=
    CochainComplex.mappingCone.inr_desc φ 0 a hdesc
  have hinl : (CochainComplex.mappingCone.inl φ).comp
      (CochainComplex.HomComplex.Cochain.ofHom s) (add_zero _) = 0 :=
    CochainComplex.mappingCone.inl_desc φ 0 a hdesc
  refine ⟨CochainComplex.mappingCone φ, s, ⟨E, t, hbounded, hflat, rfl⟩, ?_⟩
  exact CochainComplex.quasiIso_flat_truncation_telescope P E t q hq hcompat s hinr hinl

/-- Normalize the source shift comparison, without asserting a comparison to the
termwise pullback functor or invertibility of any counit component.

Source: parent lem-sc-normalized-flat-telescope-stage-comparison, steps 1–2;
Stacks Tags 06YS and 06YJ for flat models. The gauge calculation is the parent's
agent expansion, rather than an assertion of those tags.

Proof. First construct the componentwise gauge on telescope-shift representatives,
natural for stage-induced maps. Every map between representatives admits a common
source refinement with a quasi-isomorphism to its source and stage maps to both
ends. The source functor inverts this quasi-isomorphism. Precompose the desired
naturality square with its invertible image, apply stage naturality to both legs,
and cancel. Thus the local components are natural for every homotopy map between
these representatives.

Every complex admits a telescope augmentation: take compatible bounded-above
flat replacements of its good truncations, sum their augmentations, and descend
the resulting map through the cone of one minus transition with zero first cone
component. The flat truncation telescope comparison proves this augmentation a
quasi-isomorphism. The telescope representatives therefore form a resolving class.
Extend the component homomorphisms by the resolving-class right-fraction theorem.
Naturality along a telescope augmentation expresses each extended component as
the conjugate of an invertible model component by an invertible localized map.
Hence all components are invertible and assemble into a natural automorphism.
The extension equals the model gauge on both the telescope and its translate;
substituting these two equalities proves the required equation. Only the model
calculation remains in the imported local theorem. Zero towers and empty schemes
satisfy the same identities. No chosen data are defined using this existence proof.
(blueprint: lem-sc-flat-telescope-shift-gauge). -/
theorem exists_flat_telescope_shift_gauge
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    [(derivedPullback f).CommShift ℤ] [NatTrans.CommShift ε ℤ] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ a : (DerivedCategory.Qh ⋙ derivedPullback f) ≅
          (DerivedCategory.Qh ⋙ derivedPullback f),
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
          (_ : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        a.hom.app (X⟦(1 : ℤ)⟧) ≫
            ((DerivedCategory.Qh ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (a.hom.app X)⟦(1 : ℤ)⟧' := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let H := HomotopyCategory A (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let L := Q ⋙ derivedPullback f
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have hinv : W.IsInvertedBy L := by
    intro X X' s hs
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    exact inferInstanceAs (IsIso ((derivedPullback f).map (Q.map s)))
  have hres : ∀ X : H, ∃ (R : H) (s : R ⟶ X),
      flatTelescopeShiftRepresentative Y R ∧ W s := by
    intro X
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨R, s, hR, hs⟩ := exists_flat_telescope_resolution Y P
    exact ⟨q.obj R, q.map s, ⟨R, hR, Or.inl rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  obtain ⟨e, α, hα, hsquare⟩ := exists_flat_telescope_model_shift_gauge f ε hε
  have hnat : ∀ (X X' : H) (hX : flatTelescopeShiftRepresentative Y X)
      (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X'),
      L.map s ≫ (α X' hX').hom = (α X hX).hom ≫ L.map s := by
    intro X X' hX hX' s
    obtain ⟨R, a, b, hR, ha, hstagea, hstageb, hab⟩ :=
      exists_flat_telescope_stage_map_refinement Y hX hX' s
    have : IsIso (L.map a) := hinv a ha
    apply (cancel_epi (L.map a)).1
    calc
      L.map a ≫ L.map s ≫ (α X' hX').hom =
          L.map b ≫ (α X' hX').hom := by rw [← L.map_comp_assoc, hab]
      _ = (α R hR).hom ≫ L.map b := hα R X' hR hX' b hstageb
      _ = (α R hR).hom ≫ L.map a ≫ L.map s := by rw [← hab, L.map_comp]
      _ = L.map a ≫ (α X hX).hom ≫ L.map s := by
        rw [← Category.assoc, ← hα R X hR hX a hstagea, Category.assoc]
  obtain ⟨β, hβ⟩ := exists_natTrans_from_resolvingClass W
    (flatTelescopeShiftRepresentative Y) hres L L hinv
    (fun X hX ↦ (α X hX).hom) hnat
  have hβiso (X : H) : IsIso (β.app X) := by
    obtain ⟨R, s, hR, hs⟩ := hres X
    have : IsIso (L.map s) := hinv s hs
    have heq : β.app X = inv (L.map s) ≫ (α R hR).hom ≫ L.map s := by
      apply (cancel_epi (L.map s)).1
      simpa only [IsIso.hom_inv_id_assoc] using
        (β.naturality s).trans (by rw [hβ R hR])
    rw [heq]
    infer_instance
  let a : L ≅ L := NatIso.ofComponents (fun X ↦ asIso (β.app X))
    (fun s ↦ β.naturality s)
  refine ⟨e, a, ?_⟩
  intro P hP
  dsimp only
  change β.app _ ≫ _ = _ ≫ _ ≫ (β.app _)⟦(1 : ℤ)⟧'
  rw [hβ (q.obj P⟦(1 : ℤ)⟧) ⟨P, hP, Or.inr rfl⟩,
    hβ (q.obj P) ⟨P, hP, Or.inl rfl⟩]
  exact hsquare P hP

end AlgebraicGeometry
