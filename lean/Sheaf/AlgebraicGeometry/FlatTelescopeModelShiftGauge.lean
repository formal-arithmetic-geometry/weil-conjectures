/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FlatTelescopeBoundedNormalizationExtension
import Sheaf.Algebra.Homology.KFlatTelescopeClosure

/-! # Local shift gauge on flat telescope models

Source: the supplied-tensorator calculation in steps 1–2 of
lem-sc-normalized-flat-telescope-stage-comparison; Stacks Tags 06YS and 06YJ
for the model constructions, not for the supplied-tensorator assertion.
(blueprint: lem-sc-flat-telescope-model-shift-gauge).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Comparing the two counits elaborates their large dependent functor types.
/-- The supplied-tensorator gauge on concrete models, natural only for stage maps.
No transformation on the entire homotopy category is supplied.

Source: steps 1–2 and the model-ratio clause of step 3 of
lem-sc-flat-telescope-shift-gauge; the agent expansion of the parent's
supplied-tensorator normalization. Stacks Tags 06YS and 06YJ supply the models.

Proof. Represent a telescope by the cone of one minus transition on a sum of
bounded-above flat stages. Represent the unit in degree zero and its translate
in degree minus one. Identify the unshifted unit using the supplied monoidal
unit map. Rewrite translation on each stage by the first-variable Koszul map
followed by the translated left unitor. Apply the inverse supplied tensorator
and the translated unit comparison e. The two monoidal unit identities identify
the degree-zero normalizations, and tensorator associativity identifies repeated
tensor rewrites. Apply the calculation to both summands of the transition cone;
naturality makes it commute with the transition and hence the cone differential.
Take its ratio with the supplied original shift-compatible comparison. Each ratio
is a composite of isomorphisms, with inverse the reverse ratio. These ratios give
the displayed equation. The same calculation commutes with tower maps and their
sum and cone maps. Transport along the homotopy presentation isomorphisms used
in the definition of a stage map. Comparing presentations through common flat
refinements identifies the resulting ratios, so they depend on the indicated
homotopy object rather than its presentation. This gives the stage-map naturality
asserted here. Naturality for arbitrary homotopy morphisms and extension to all
objects are separate arguments. Zero towers and empty schemes satisfy the same
identities, without cancellation of any noninvertible map.
(blueprint: lem-sc-flat-telescope-model-shift-gauge). -/
theorem exists_flat_telescope_model_shift_gauge
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
      ∃ a : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            (DerivedCategory.Qh ⋙ derivedPullback f).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X)
          (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X'),
          flatTelescopeStageMap Y s →
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (a X' hX').hom =
            (a X hX).hom ≫ (DerivedCategory.Qh ⋙ derivedPullback f).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
          (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        (a (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩).hom ≫
            ((DerivedCategory.Qh ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            ((a X ⟨P, htel, Or.inl rfl⟩).hom)⟦(1 : ℤ)⟧' := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let L := DerivedCategory.Qh ⋙ derivedPullback f
  let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Z)
  have hεK (P : CochainComplex A ℤ) (hP : CochainComplex.IsKFlat (R := Y.sheaf) P) :
      IsIso (ε.app (q.obj P)) := by
    obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      E, hE, hEmap, hEadd, δ, hδ, htri, hK⟩ :=
      Classical.choose_spec (exists_derivedPullback f)
    have hE' : E = Scheme.Modules.tensorPullback f :=
      CategoryTheory.Functor.ext hE (fun _ _ s ↦ hEmap s)
    subst E
    let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
    have : (derivedPullback f).IsLeftDerivedFunctor δ W := hδ
    have : IsIso ((derivedPullback f).leftDerivedLift δ W (derivedPullback f) ε) :=
      ((derivedPullback f).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
        δ W (derivedPullback f) ε).mp hε
    have : IsIso (δ.app (q.obj P)) := hK P hP
    rw [← Functor.leftDerived_fac_app (derivedPullback f) δ W (derivedPullback f) ε]
    infer_instance
  have htelK (P : CochainComplex A ℤ) (hP : isFlatTelescope Y P) :
      CochainComplex.IsKFlat (R := Y.sheaf) P := by
    obtain ⟨E, t, hb, hf, rfl⟩ := hP
    apply (CochainComplex.kFlat_closure Y.sheaf).2.2.2.1 E t
    intro n
    exact (CochainComplex.kFlat_closure Y.sheaf).1 (E n) (hb n) (hf n)
  have hεiso (X : HomotopyCategory A (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X) : IsIso (ε.app X) := by
    obtain ⟨P, hP, h | h⟩ := hX
    · subst X
      exact hεK P (htelK P hP)
    · subst X
      have : IsIso (ε.app (q.obj P)) := hεK P (htelK P hP)
      have he : ε.app ((q.obj P)⟦(1 : ℤ)⟧) =
          (L.commShiftIso (1 : ℤ)).hom.app (q.obj P) ≫
            (ε.app (q.obj P))⟦(1 : ℤ)⟧' ≫
            (G.commShiftIso (1 : ℤ)).inv.app (q.obj P) := by
        rw [← Category.assoc, NatTrans.shift_app_comm ε (1 : ℤ), Category.assoc,
          Iso.hom_inv_id_app]
        exact (Category.comp_id _).symm
      rw [he]
      infer_instance
  obtain ⟨e, β, hβnat, hβshift⟩ := exists_bounded_flat_model_normalization f
  obtain ⟨α, hαnat, hαshift⟩ :=
    exists_flat_telescope_comparison_of_bounded_normalization f e β hβnat hβshift
  let a := fun X hX ↦ α X hX ≪≫ (@asIso _ _ _ _ (ε.app X) (hεiso X hX)).symm
  refine ⟨e, a, ?_, ?_⟩
  · intro X X' hX hX' s hs
    have : IsIso (ε.app X') := hεiso X' hX'
    have : IsIso (ε.app X) := hεiso X hX
    apply (cancel_mono (ε.app X')).1
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, asIso_inv]
    rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [Category.assoc, ε.naturality]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    exact hαnat X X' hX hX' s hs
  · intro P hP
    dsimp only
    let X := q.obj P
    have : IsIso (ε.app X) := hεiso X ⟨P, hP, Or.inl rfl⟩
    have : IsIso (ε.app (X⟦(1 : ℤ)⟧)) := hεiso _ ⟨P, hP, Or.inr rfl⟩
    apply (cancel_mono ((ε.app X)⟦(1 : ℤ)⟧')).1
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, asIso_inv]
    rw [Category.assoc, NatTrans.shift_app_comm ε (1 : ℤ)]
    dsimp only [X, q, A]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [Functor.map_comp]
    simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]
    simpa only [Iso.trans_hom, Category.assoc] using hαshift P hP

end AlgebraicGeometry
