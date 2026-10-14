/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.CategoryTheory.RightKanExtensionCoherentShift
import Sheaf.AlgebraicGeometry.FlatTelescopeShiftGauge

/-! # Normalization on maps of flat telescope models

Source: Stacks Project, Tags 06YS and 06YJ, and the supplied-tensorator
calculation in the parent plan. (blueprint: lem-sc-normalized-flat-telescope-stage-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

set_option maxHeartbeats 800000 in
-- The chosen counit and recorded pullback have large dependent types to compare.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Joint normalization on explicit model maps, before extension to arbitrary
homotopy morphisms. Source: Stacks Project, Tags 06YS and 06YJ; parent steps 1
and 2, and the model-map part of step 3. The tensorator normalization is the
agent expansion of that plan, not a statement of either Stacks tag.

Proof. Express each telescope as the cone of one minus the transition on its
countable sum of bounded-above flat stages. Each stage, the sum, and the cone
are K-flat. Compute pullback on those complexes by termwise tensor pullback;
its sum and cone comparisons give invertible representative comparisons.
Use the structure sheaf concentrated in degree zero and its translate as unit
models. Normalize the unit comparison by the supplied monoidal unit map.
Rewrite translation as tensor with that shifted unit, using the Koszul map
and translated left unitor. Construct the shifted-unit and telescope comparisons
jointly with this rewrite. The supplied tensorator's associativity and unit
identities identify the two rewrites with the same composite on both summands
of the telescope cone. Consequently their inclusion, transition, and projection
maps commute and the stated shift identity holds. For a compatible family of
stage maps the sum and cone comparisons commute term by term; translation
preserves those equalities. Comparison along a common K-flat presentation
identifies the results after transport by homotopy isomorphisms, so these
components depend only on the indicated homotopy objects. This gives naturality
for the explicitly defined stage maps, including their allowed transports and
translates. Extension to every homotopy morphism is a separate refinement step.
The zero tower has zero sum and cone, and the same formulas apply on an empty
scheme. No data are defined by choosing a witness of this existence theorem.
(blueprint: lem-sc-normalized-flat-telescope-stage-comparison). -/
theorem exists_normalized_flat_telescope_stage_comparison
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'), flatTelescopeStageMap Y s →
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX').hom =
            (α X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧' := by
  classical
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      E, hE, hEmap, hEadd, ε, hleft, htri, hε⟩ :=
    Classical.choose_spec (exists_derivedPullback.{u, w} f)
  have hE' : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun _ _ s ↦ hEmap s)
  subst E
  let L := DerivedCategory.Qh ⋙ derivedPullback f
  let G : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Z :=
    (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Z)
  change L ⟶ G at ε
  obtain ⟨sF, hsF⟩ := Functor.rightKanExtension_coherentShift
    G (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
      (derivedPullback f) ε hleft.isRightKanExtension
  let : (derivedPullback f).CommShift ℤ := sF
  let : NatTrans.CommShift ε ℤ := hsF
  obtain ⟨e, a, ha⟩ := exists_flat_telescope_shift_gauge f ε hleft
  have htelK (P : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (htel : isFlatTelescope Y P) : CochainComplex.IsKFlat (R := Y.sheaf) P := by
    obtain ⟨E, t, hb, hf, rfl⟩ := htel
    apply (CochainComplex.kFlat_closure Y.sheaf).2.2.2.1 E t
    intro n
    exact (CochainComplex.kFlat_closure Y.sheaf).1 (E n) (hb n) (hf n)
  have hεiso (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X) : IsIso (ε.app X) := by
    obtain ⟨P, hP, hX | hX⟩ := hX
    · subst X
      exact hε P (htelK P hP)
    · subst X
      let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
      have : IsIso (ε.app X) := hε P (htelK P hP)
      have hs := NatTrans.shift_app_comm ε (1 : ℤ) X
      have he : ε.app (X⟦(1 : ℤ)⟧) =
          (L.commShiftIso (1 : ℤ)).hom.app X ≫ (ε.app X)⟦(1 : ℤ)⟧' ≫
            (G.commShiftIso (1 : ℤ)).inv.app X := by
        rw [← Category.assoc, hs, Category.assoc, Iso.hom_inv_id_app]
        exact (Category.comp_id _).symm
      rw [he]
      infer_instance
  let η : L ⟶ G := a.hom ≫ ε
  have hηiso (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X) : IsIso (η.app X) := by
    have := hεiso X hX
    dsimp only [η, NatTrans.comp_app]
    infer_instance
  let α := fun X hX ↦ @asIso _ _ _ _ (η.app X) (hηiso X hX)
  refine ⟨e, α, ?_, ?_⟩
  · intro X X' hX hX' s _
    exact η.naturality s
  · intro P htel
    dsimp only [α, asIso_hom]
    change η.app _ ≫ _ = _ ≫ _ ≫ (η.app _)⟦(1 : ℤ)⟧'
    dsimp only [η, NatTrans.comp_app]
    rw [Category.assoc, ← NatTrans.shift_app_comm ε (1 : ℤ),
      ← Category.assoc, ha P htel]
    simp only [Category.assoc, ← Functor.map_comp]



end AlgebraicGeometry
