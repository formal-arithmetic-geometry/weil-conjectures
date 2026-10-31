/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.PathCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Sections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # Coherent fibres of arbitrary condensed coefficient modules

Source: latest blueprint, sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/
det-def-sfb-module-pushforward-pullback.proof.md, composition comparisons, refined by
the eight-step DAG proof to geometric fibres and source automorphisms.
(blueprint: lem-wf-condensed-fibre-comparison-coherence)

Sections are represented by maps from the regular module. Evaluation at its unit identifies
these with terminal sections. In this representation terminal evaluation of a pushforward
is the adjunction Hom bijection followed by the inverse canonical regular-module comparison.
Thus the transport below uses the adjunction unit, including its terminal normalization.
Linearity is stated by an explicit scalar equation, without choosing a second module structure.

The associative and unit coherence of the module pullback comparisons (the node's module
coherence clause, DAG proof steps 1 and 2) is not restated: it is the existing upstream
`ProEtale.CondensedRing.upperStarComp_assoc`, `ProEtale.CondensedRing.upperStarComp_id_left`
and `ProEtale.CondensedRing.upperStarComp_id_right` (with `upperStarId` as the specified unit
comparison), obtained there by conjugating the pushforward laws exactly as in steps 1 and 2.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxRecDepth 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ordinary section group, represented by maps from the regular module.
Source: latest blueprint, coefficient module adjunction and terminal evaluation
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
abbrev fibreModuleSections {X : Scheme.{u}}
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  Mod.regular (condensedRingObj Λ X) ⟶ N

/-- The external scalar action: pull a section of the condensed ring back from the point
and precompose with its multiplication endomorphism of the regular coefficient module.
Source: latest blueprint, pulled-back coefficients; DAG proof step 3
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
def fibreSectionSMul {X : Scheme.{u}}
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (a : Γ Λ) (v : fibreModuleSections Λ N) : fibreModuleSections Λ N :=
  Mod.regularEndRingHom (Γ.mapFunctorMonoidHom (upperStarFromPoint X) a) ≫ v

/-- Terminal evaluation of a direct image in the regular-module representation of sections.
The Hom bijection and the canonical regular-module pullback comparison give the identification
Gamma(Y,a_*P) = Gamma(X,P); no choice of an isomorphism is made.
Source: latest blueprint, module adjunction; DAG proof step 3
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
def fibrePushforwardSections {X Y : Scheme.{u}} (a : X ⟶ Y)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (v : fibreModuleSections Λ ((lowerStar Λ a).obj P)) : fibreModuleSections Λ P :=
  (upperStarObjRegularIso Λ a).inv ≫
    ((upperStarLowerStarAdjunction Λ a).homEquiv _ _).symm v

/-- Sections of the actual adjunction unit, then terminal evaluation of the direct image.
For a source automorphism this is the map I_h in the node.
Source: latest blueprint, module adjunction; DAG proof steps 4 and 5
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
def fibreUnitSections {X Y : Scheme.{u}} (a : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (v : fibreModuleSections Λ N) : fibreModuleSections Λ ((upperStar Λ a).obj N) :=
  fibrePushforwardSections Λ a ((upperStar Λ a).obj N)
    (v ≫ (upperStarLowerStarAdjunction Λ a).unit.app N)

/-- The fibre comparison c: sections of the inverse specified mate compositor.
Source: latest blueprint, pullback composition; DAG proof step 6
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
def condensedFibreComparison {S X Y : Scheme.{u}} (f : X ⟶ Y) (z : S ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (v : fibreModuleSections Λ ((upperStar Λ z).obj ((upperStar Λ f).obj M))) :
    fibreModuleSections Λ ((upperStar Λ (z ≫ f)).obj M) :=
  v ≫ (upperStarComp Λ z f).inv.app M

/-- The reparametrization r is I_h followed by the specified fibre comparison c_{z,h}.
Source: latest blueprint, module composition; DAG proof steps 7 and 8
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
def condensedFibreReparam {S X : Scheme.{u}} (z : S ⟶ X) (h : S ≅ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (v : fibreModuleSections Λ ((upperStar Λ z).obj M)) :
    fibreModuleSections Λ ((upperStar Λ (h.hom ≫ z)).obj M) :=
  condensedFibreComparison Λ z h.hom M
    (fibreUnitSections Λ h.hom ((upperStar Λ z).obj M) v)

private theorem section_left_unit {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (I : D ⥤ D) (U : I ≅ 𝟭 D) (K : C ⥤ D) (T : K ≅ F)
    (A : K ≅ F ⋙ I)
    (hA : A = T ≪≫ F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F U.symm)
    (M : C) {V : D} (v : V ⟶ I.obj (F.obj M)) :
    v ≫ A.inv.app M = (v ≫ U.hom.app (F.obj M)) ≫ T.inv.app M := by
  rw [hA]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.assoc, Category.id_comp]

private theorem section_right_unit {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (I : C ⥤ C) (U : I ≅ 𝟭 C) (K : C ⥤ D) (T : K ≅ F)
    (A : K ≅ I ⋙ F)
    (hA : A = T ≪≫ F.leftUnitor.symm ≪≫ Functor.isoWhiskerRight U.symm F)
    (M : C) {V : D} (v : V ⟶ F.obj M) :
    (v ≫ F.map (U.inv.app M)) ≫ A.inv.app M = v ≫ T.inv.app M := by
  rw [hA]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.assoc, Category.id_comp]
  rw [← Functor.map_comp_assoc, U.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [F.map_id, Category.id_comp]

private theorem fibreUnitSections_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (v : fibreModuleSections Λ N) :
    fibreUnitSections Λ f N v =
      (upperStarObjRegularIso Λ f).inv ≫ (upperStar Λ f).map v := by
  simp only [fibreUnitSections, fibrePushforwardSections,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_symm_unit,
    Category.comp_id]

private theorem fibreUnitSections_natural {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (t : M ⟶ N) (v : fibreModuleSections Λ M) :
    fibreUnitSections Λ f N (v ≫ t) =
      fibreUnitSections Λ f M v ≫ (upperStar Λ f).map t := by
  rw [fibreUnitSections_eq, fibreUnitSections_eq, Functor.map_comp, Category.assoc]

omit [IsCommMonObj Λ] in
private theorem fibreConstantScalar_pull {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Γ Λ) :
    Γ.map (condensedPullbackHom Λ f)
      (Γ.mapFunctor (ProEtale.upperStar Ab.{u + 1} f)
        (Γ.mapFunctorMonoidHom (upperStarFromPoint Y) a)) =
      Γ.mapFunctorMonoidHom (upperStarFromPoint X) a := by
  ext1
  change (Functor.LaxMonoidal.ε (ProEtale.upperStar Ab.{u + 1} f) ≫
      (ProEtale.upperStar Ab.{u + 1} f).map
        (Functor.LaxMonoidal.ε (upperStarFromPoint Y) ≫
          (upperStarFromPoint Y).map a.hom)) ≫
      (upperStarFromPointComp f).hom.app Λ =
    Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map a.hom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (upperStarFromPointComp f).hom.naturality a.hom
  simp only [Functor.comp_map] at hn
  rw [hn]
  simp only [← Category.assoc]
  rw [← Functor.LaxMonoidal.comp_ε, NatTrans.IsMonoidal.unit]

private theorem fibrePull_regularEnd {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Γ Λ) :
    (upperStarObjRegularIso Λ f).inv ≫ (upperStar Λ f).map
        (Mod.regularEndRingHom (Γ.mapFunctorMonoidHom (upperStarFromPoint Y) a)) =
      Mod.regularEndRingHom (Γ.mapFunctorMonoidHom (upperStarFromPoint X) a) ≫
        (upperStarObjRegularIso Λ f).inv := by
  have h := restrictEnd_regularEndRingHom Λ f
    (Γ.mapFunctorMonoidHom (upperStarFromPoint Y) a)
  rw [fibreConstantScalar_pull Λ f a, restrictEnd_apply] at h
  rw [← cancel_mono (upperStarObjRegularIso Λ f).hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

private theorem fibrePullUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (monoidal_upperStar Λ f).toLaxMonoidal.ε = (upperStarObjRegularIso Λ f).inv := by
  apply Mod.hom_ext
  change (inv (condensedPullbackHom Λ f) ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).inv.app
        (Mod.regular _)).hom) ≫
      ((Mod.extendScalars (condensedPullbackHom Λ f)).map (𝟙 (Mod.regular _))).hom =
    inv (condensedPullbackHom Λ f) ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).inv.app
        (Mod.regular _)).hom
  erw [CategoryTheory.Functor.map_id, Mod.id_hom', Category.comp_id]

private theorem fibrePullUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.Monoidal.εIso (upperStar Λ f) = (upperStarObjRegularIso Λ f).symm := by
  apply Iso.ext
  exact fibrePullUnit Λ f

private theorem fibrePullUnit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStarObjRegularIso Λ f).inv ≫
        (upperStar Λ f).map (upperStarObjRegularIso Λ g).inv ≫
        (upperStarComp Λ f g).inv.app (Mod.regular (condensedRingObj Λ Z)) =
      (upperStarObjRegularIso Λ (f ≫ g)).inv := by
  have he : (upperStarComp Λ f g).hom.app (Mod.regular (condensedRingObj Λ Z)) ≫
      (upperStar Λ f).map (upperStarObjRegularIso Λ g).hom ≫
      (upperStarObjRegularIso Λ f).hom = (upperStarObjRegularIso Λ (f ≫ g)).hom := by
    have hh := upperStarComp_hom_app_unit Λ f g
    rw [fibrePullUnitIso, fibrePullUnitIso, fibrePullUnitIso] at hh
    exact hh
  apply (cancel_mono (upperStarObjRegularIso Λ (f ≫ g)).hom).1
  rw [Iso.inv_hom_id, ← he]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

private theorem fibreCongrInv_heq {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (v : fibreModuleSections Λ ((upperStar Λ g).obj M)) :
    HEq (v ≫ (upperStarCongr Λ e).inv.app M) v := by
  subst g
  simpa only [upperStarCongr_self, Iso.refl_inv, NatTrans.id_app, Category.comp_id]
    using HEq.rfl (a := v)

private theorem fibreComparison_assoc {S W X Y : Scheme.{u}}
    (g : W ⟶ X) (f : X ⟶ Y) (w : S ⟶ W)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (v : fibreModuleSections Λ
      ((upperStar Λ w).obj ((upperStar Λ g).obj ((upperStar Λ f).obj M)))) :
    HEq (condensedFibreComparison Λ (g ≫ f) w M
        (v ≫ (upperStar Λ w).map ((upperStarComp Λ g f).inv.app M)))
      (condensedFibreComparison Λ f (w ≫ g) M
        (condensedFibreComparison Λ g w ((upperStar Λ f).obj M) v)) := by
  have he := congrArg (fun e ↦ e.inv.app M) (upperStarComp_assoc Λ w g f)
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at he
  dsimp only [condensedFibreComparison]
  rw [Category.assoc, he]
  simpa only [Category.assoc] using
    fibreCongrInv_heq Λ (Category.assoc w g f).symm M
      ((v ≫ (upperStarComp Λ w g).inv.app ((upperStar Λ f).obj M)) ≫
        (upperStarComp Λ (w ≫ g) f).inv.app M)

private theorem fibreUnitSections_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (v : fibreModuleSections Λ N) :
    condensedFibreComparison Λ g f N
      (fibreUnitSections Λ f ((upperStar Λ g).obj N) (fibreUnitSections Λ g N v)) =
        fibreUnitSections Λ (f ≫ g) N v := by
  simp only [fibreUnitSections_eq, condensedFibreComparison, Functor.map_comp,
    Category.assoc]
  change (upperStarObjRegularIso Λ f).inv ≫
      (upperStar Λ f).map (upperStarObjRegularIso Λ g).inv ≫
      (upperStar Λ g ⋙ upperStar Λ f).map v ≫ (upperStarComp Λ f g).inv.app N = _
  rw [(upperStarComp Λ f g).inv.naturality v]
  simpa only [Category.assoc] using
    congrArg (fun q ↦ q ≫ (upperStar Λ (f ≫ g)).map v) (fibrePullUnit_comp Λ f g)

private theorem fibreUnitSections_id (X : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (v : fibreModuleSections Λ N) :
    fibreUnitSections Λ (𝟙 X) N v ≫ (upperStarId Λ X).hom.app N = v := by
  rw [fibreUnitSections_eq, Category.assoc, (upperStarId Λ X).hom.naturality v]
  have he : (upperStarId Λ X).hom.app (Mod.regular (condensedRingObj Λ X)) =
      (Functor.Monoidal.εIso (upperStar Λ (𝟙 X))).inv := upperStarId_hom_app_unit Λ X
  rw [← Category.assoc, he, fibrePullUnitIso]
  simp only [Iso.symm_inv, Iso.inv_hom_id, Category.id_comp, Functor.id_map]

set_option maxHeartbeats 1600000 in
-- The endpoints include the full internal-module coefficient structures.
/-- The canonical c, I and r are natural additive, external-scalar-linear bijections.
Source: latest blueprint, composition comparisons and module adjunction
(blueprint: lem-wf-condensed-fibre-comparison-coherence).

Proof: step 3 identifies terminal direct-image evaluation and checks its external scalars
using the coefficient mate equation, conjugate-iso unit equation and composite adjunction.
Step 4 evaluates the unit equation to obtain naturality and linearity of I. Step 5 uses
the inverse source automorphism: its direct image is an equivalence by the right-adjoint
coherence; the counit-isomorphism theorem on the opposite adjunction makes the original
unit invertible. Step 6 takes sections of the inverse pullback compositor to obtain c.
Step 7 composes c with I to obtain r. Additivity follows from these additive functors
and the additive adjunction bijections. No constructibility or Weil datum is used. -/
theorem condensedFibre_comparisons_linear_natural (k : Type u) [Field k] [IsAlgClosed k] :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (z : Spec (.of k) ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      Function.Bijective (condensedFibreComparison Λ f z M) ∧
      (∀ v w, condensedFibreComparison Λ f z M (v + w) =
        condensedFibreComparison Λ f z M v + condensedFibreComparison Λ f z M w) ∧
      (∀ a v, condensedFibreComparison Λ f z M (fibreSectionSMul Λ a v) =
        fibreSectionSMul Λ a (condensedFibreComparison Λ f z M v)) ∧
      ∀ (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
        (t : M ⟶ N) v,
        condensedFibreComparison Λ f z N
            (v ≫ (upperStar Λ z).map ((upperStar Λ f).map t)) =
          condensedFibreComparison Λ f z M v ≫ (upperStar Λ (z ≫ f)).map t) ∧
    (∀ (h : Spec (.of k) ≅ Spec (.of k))
      (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of k)))),
      Function.Bijective (fibreUnitSections Λ h.hom N) ∧
      (∀ v w, fibreUnitSections Λ h.hom N (v + w) =
        fibreUnitSections Λ h.hom N v + fibreUnitSections Λ h.hom N w) ∧
      (∀ a v, fibreUnitSections Λ h.hom N (fibreSectionSMul Λ a v) =
        fibreSectionSMul Λ a (fibreUnitSections Λ h.hom N v)) ∧
      ∀ (P : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k)))) (t : N ⟶ P) v,
        fibreUnitSections Λ h.hom P (v ≫ t) =
          fibreUnitSections Λ h.hom N v ≫ (upperStar Λ h.hom).map t) ∧
    (∀ {X : Scheme.{u}} (z : Spec (.of k) ⟶ X) (h : Spec (.of k) ≅ Spec (.of k))
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      Function.Bijective (condensedFibreReparam Λ z h M) ∧
      (∀ v w, condensedFibreReparam Λ z h M (v + w) =
        condensedFibreReparam Λ z h M v + condensedFibreReparam Λ z h M w) ∧
      (∀ a v, condensedFibreReparam Λ z h M (fibreSectionSMul Λ a v) =
        fibreSectionSMul Λ a (condensedFibreReparam Λ z h M v)) ∧
      ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
        (t : M ⟶ N) v,
        condensedFibreReparam Λ z h N (v ≫ (upperStar Λ z).map t) =
          condensedFibreReparam Λ z h M v ≫ (upperStar Λ (h.hom ≫ z)).map t) := by
  have hc :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (z : Spec (.of k) ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      Function.Bijective (condensedFibreComparison Λ f z M) ∧
      (∀ v w, condensedFibreComparison Λ f z M (v + w) =
        condensedFibreComparison Λ f z M v + condensedFibreComparison Λ f z M w) ∧
      (∀ a v, condensedFibreComparison Λ f z M (fibreSectionSMul Λ a v) =
        fibreSectionSMul Λ a (condensedFibreComparison Λ f z M v)) ∧
      ∀ (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
        (t : M ⟶ N) v,
        condensedFibreComparison Λ f z N
            (v ≫ (upperStar Λ z).map ((upperStar Λ f).map t)) =
          condensedFibreComparison Λ f z M v ≫ (upperStar Λ (z ≫ f)).map t) := by
    intro X Y f z M
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ((upperStarComp Λ z f).symm.app M).homToEquiv.bijective
    · intro v w
      dsimp [condensedFibreComparison]
      rw [Preadditive.add_comp]
    · intro a v
      simp only [condensedFibreComparison, fibreSectionSMul, Category.assoc]
    · intro N t v
      dsimp [condensedFibreComparison]
      change v ≫ ((upperStar Λ f ⋙ upperStar Λ z).map t) ≫
        (upperStarComp Λ z f).inv.app N = _
      simpa only [Category.assoc] using
        congrArg (fun q ↦ v ≫ q) ((upperStarComp Λ z f).inv.naturality t)
  have hi :
    (∀ (h : Spec (.of k) ≅ Spec (.of k))
      (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of k)))),
      Function.Bijective (fibreUnitSections Λ h.hom N) ∧
      (∀ v w, fibreUnitSections Λ h.hom N (v + w) =
        fibreUnitSections Λ h.hom N v + fibreUnitSections Λ h.hom N w) ∧
      (∀ a v, fibreUnitSections Λ h.hom N (fibreSectionSMul Λ a v) =
        fibreSectionSMul Λ a (fibreUnitSections Λ h.hom N v)) ∧
      ∀ (P : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k)))) (t : N ⟶ P) v,
        fibreUnitSections Λ h.hom P (v ≫ t) =
          fibreUnitSections Λ h.hom N v ≫ (upperStar Λ h.hom).map t) := by
    intro h N
    refine ⟨?_, ?_, ?_, ?_⟩
    · have he : fibreUnitSections Λ h.hom N =
          (upperStarObjRegularIso Λ h.hom).homFromEquiv ∘ (upperStar Λ h.hom).map := by
        funext v
        exact fibreUnitSections_eq Λ h.hom N v
      rw [he]
      exact (upperStarObjRegularIso Λ h.hom).homFromEquiv.bijective.comp
        ((Functor.FullyFaithful.ofFullyFaithful (upperStar Λ h.hom)).map_bijective
          (Mod.regular _) N)
    · intro v w
      simp only [fibreUnitSections_eq, Functor.map_add, Preadditive.comp_add]
    · intro a v
      simp only [fibreUnitSections_eq, fibreSectionSMul, Functor.map_comp]
      rw [← Category.assoc, fibrePull_regularEnd, Category.assoc]
    · intro P t v
      simp only [fibreUnitSections_eq, Functor.map_comp, Category.assoc]
  refine ⟨hc, hi, ?_⟩
  intro X z h M
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hc z h.hom M).1.comp (hi h ((upperStar Λ z).obj M)).1
  · intro v w
    dsimp only [condensedFibreReparam]
    rw [(hi h _).2.1, (hc z h.hom M).2.1]
  · intro a v
    dsimp only [condensedFibreReparam]
    rw [(hi h _).2.2.1, (hc z h.hom M).2.2.1]
  · intro N t v
    dsimp only [condensedFibreReparam]
    rw [(hi h _).2.2.2, (hc z h.hom M).2.2.2]

private theorem fibreReparam_natural {S X : Scheme.{u}} (z : S ⟶ X) (h : S ≅ S)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (t : M ⟶ N) (v : fibreModuleSections Λ ((upperStar Λ z).obj M)) :
    condensedFibreReparam Λ z h N (v ≫ (upperStar Λ z).map t) =
      condensedFibreReparam Λ z h M v ≫ (upperStar Λ (h.hom ≫ z)).map t := by
  dsimp only [condensedFibreReparam, condensedFibreComparison]
  rw [fibreUnitSections_natural]
  change (fibreUnitSections Λ h.hom ((upperStar Λ z).obj M) v ≫
    (upperStar Λ z ⋙ upperStar Λ h.hom).map t) ≫
      (upperStarComp Λ h.hom z).inv.app N = _
  simpa only [Category.assoc] using
    congrArg (fun q ↦ fibreUnitSections Λ h.hom ((upperStar Λ z).obj M) v ≫ q)
      ((upperStarComp Λ h.hom z).inv.naturality t)

-- Keep the composite arrow as a parameter so that specializing to an isomorphism hom
-- preserves the section type without unfolding the internal module construction.
private theorem fibreUnit_cocycle {S X : Scheme.{u}} (z : S ⟶ X)
    (h a b : S ⟶ S) (e : b = a ≫ h)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (v : fibreModuleSections Λ ((upperStar Λ z).obj M)) :
    HEq (condensedFibreComparison Λ (h ≫ z) a M
      (fibreUnitSections Λ a ((upperStar Λ (h ≫ z)).obj M)
        (condensedFibreComparison Λ z h M
          (fibreUnitSections Λ h ((upperStar Λ z).obj M) v))))
      (condensedFibreComparison Λ z b M
        (fibreUnitSections Λ b ((upperStar Λ z).obj M) v)) := by
  subst b
  have hb := fibreComparison_assoc Λ h z a M
    (fibreUnitSections Λ a ((upperStar Λ h).obj ((upperStar Λ z).obj M))
      (fibreUnitSections Λ h ((upperStar Λ z).obj M) v))
  have hl := congrArg (condensedFibreComparison Λ (h ≫ z) a M)
    (fibreUnitSections_natural Λ a ((upperStarComp Λ h z).inv.app M)
      (fibreUnitSections Λ h ((upperStar Λ z).obj M) v))
  have hr := congrArg (condensedFibreComparison Λ z (a ≫ h) M)
    (fibreUnitSections_comp Λ a h ((upperStar Λ z).obj M) v)
  exact (heq_of_eq hl).trans (hb.trans (heq_of_eq hr))

private theorem fibreUnit_identity {S X : Scheme.{u}} (z : S ⟶ X)
    (f : S ⟶ S) (e : f = 𝟙 S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (v : fibreModuleSections Λ ((upperStar Λ z).obj M)) :
    HEq (condensedFibreComparison Λ z f M
      (fibreUnitSections Λ f ((upperStar Λ z).obj M) v)) v := by
  subst f
  have hr := section_left_unit (upperStar Λ z) (upperStar Λ (𝟙 S))
    (upperStarId Λ S) (upperStar Λ (𝟙 S ≫ z))
    (upperStarCongr Λ (Category.id_comp z)) (upperStarComp Λ (𝟙 S) z)
    (upperStarComp_id_left Λ z) M
    (fibreUnitSections Λ (𝟙 S) ((upperStar Λ z).obj M) v)
  have he := congrArg
    (fun q ↦ q ≫ (upperStarCongr Λ (Category.id_comp z)).inv.app M)
    (fibreUnitSections_id Λ S ((upperStar Λ z).obj M) v)
  exact (heq_of_eq (hr.trans he)).trans (fibreCongrInv_heq Λ (Category.id_comp z) M v)

private theorem fibreReparam_cocycle (S : Scheme.{u}) :
    (∀ {X : Scheme.{u}} (z : S ⟶ X)
      (h a : S ≅ S)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (v : fibreModuleSections Λ ((upperStar Λ z).obj M)),
      HEq (condensedFibreReparam Λ (h.hom ≫ z) a M (condensedFibreReparam Λ z h M v))
        (condensedFibreReparam Λ z (a ≪≫ h) M v)) := by
  intro X z h a M v
  exact fibreUnit_cocycle Λ z h.hom a.hom (a ≪≫ h).hom rfl M v

private theorem fibreReparam_id (S : Scheme.{u}) :
    (∀ {X : Scheme.{u}} (z : S ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (v : fibreModuleSections Λ ((upperStar Λ z).obj M)),
      HEq (condensedFibreReparam Λ z (Iso.refl _) M v) v) := by
  intro X z M v
  exact fibreUnit_identity Λ z (Iso.refl S).hom rfl M v

private theorem fibreReparam_mixed (S : Scheme.{u}) :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (z : S ⟶ X)
      (h : S ≅ S)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (v : fibreModuleSections Λ ((upperStar Λ z).obj ((upperStar Λ f).obj M))),
      HEq (condensedFibreReparam Λ (z ≫ f) h M (condensedFibreComparison Λ f z M v))
        (condensedFibreComparison Λ f (h.hom ≫ z) M
          (condensedFibreReparam Λ z h ((upperStar Λ f).obj M) v))) := by
  intro X Y f z h M v
  have hb := fibreComparison_assoc Λ z f h.hom M
    (fibreUnitSections Λ h.hom ((upperStar Λ z).obj ((upperStar Λ f).obj M)) v)
  dsimp only [condensedFibreReparam]
  change HEq (condensedFibreComparison Λ (z ≫ f) h.hom M
    (fibreUnitSections Λ h.hom ((upperStar Λ (z ≫ f)).obj M)
      (v ≫ (upperStarComp Λ z f).inv.app M))) _
  rw [fibreUnitSections_natural]
  exact hb

set_option maxHeartbeats 1600000 in
-- The endpoints carry the internal module structures.
/-- Fibre composition, source-automorphism cocycle, identity, and the mixed square.
HEq only identifies the endpoints differing by scheme composition associativity or a unit;
the first equation explicitly inserts the prescribed module compositor at the source.
Source: latest blueprint, composition comparisons, with DAG proof steps 6--8
(blueprint: lem-wf-condensed-fibre-comparison-coherence).

Proof: step 6 evaluates the associative module comparison at w. Step 7 uses naturality
of I at the (h,z) comparison, then associativity at (a,h,z), then the evaluated composite
unit equation D_{a,h} I_a I_h = I_{ha}; the unit equation gives r_id = id. Step 8 uses
naturality of I at the (z,f) comparison followed by associativity at (h,z,f), obtaining
the mixed square. Induction on the number of arrows gives every iterated version:
zero arrows uses the specified unit, and appending an arrow uses the corresponding
binary identity. The module coherence (`upperStarComp_assoc`, `upperStarComp_id_left`,
`upperStarComp_id_right`) makes reassociation and inserted identities inert. -/
theorem condensedFibre_comparison_coherence (k : Type u) [Field k] [IsAlgClosed k] :
    (∀ {W X Y : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ Y) (w : Spec (.of k) ⟶ W)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (v : fibreModuleSections Λ
        ((upperStar Λ w).obj ((upperStar Λ g).obj ((upperStar Λ f).obj M)))),
      HEq (condensedFibreComparison Λ (g ≫ f) w M
          (v ≫ (upperStar Λ w).map ((upperStarComp Λ g f).inv.app M)))
        (condensedFibreComparison Λ f (w ≫ g) M
          (condensedFibreComparison Λ g w ((upperStar Λ f).obj M) v))) ∧
    (∀ {X : Scheme.{u}} (z : Spec (.of k) ⟶ X)
      (h a : Spec (.of k) ≅ Spec (.of k))
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (v : fibreModuleSections Λ ((upperStar Λ z).obj M)),
      HEq (condensedFibreReparam Λ (h.hom ≫ z) a M (condensedFibreReparam Λ z h M v))
        (condensedFibreReparam Λ z (a ≪≫ h) M v)) ∧
    (∀ {X : Scheme.{u}} (z : Spec (.of k) ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (v : fibreModuleSections Λ ((upperStar Λ z).obj M)),
      HEq (condensedFibreReparam Λ z (Iso.refl _) M v) v) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (z : Spec (.of k) ⟶ X)
      (h : Spec (.of k) ≅ Spec (.of k))
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (v : fibreModuleSections Λ ((upperStar Λ z).obj ((upperStar Λ f).obj M))),
      HEq (condensedFibreReparam Λ (z ≫ f) h M (condensedFibreComparison Λ f z M v))
        (condensedFibreComparison Λ f (h.hom ≫ z) M
          (condensedFibreReparam Λ z h ((upperStar Λ f).obj M) v))) := by
  refine ⟨?_, fibreReparam_cocycle Λ _, fibreReparam_id Λ _, fibreReparam_mixed Λ _⟩
  intro W X Y g f w M v
  exact fibreComparison_assoc Λ g f w M v


/-- Iterated inverse image along a finite composable path, including the empty path.
Source: latest blueprint, iterated composition comparisons; DAG proof step 8
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
def fibrePathPull {X : Scheme.{u}} : {Y : Scheme.{u}} → Quiver.Path X Y →
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  | _, .nil => 𝟭 _
  | _, .cons p f => upperStar Λ f ⋙ fibrePathPull p

/-- The iterated comparison made from the specified unit and binary mate comparisons.
Source: latest blueprint, iterated composition comparisons; DAG proof step 8
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
def fibrePathComparison {X : Scheme.{u}} : {Y : Scheme.{u}} →
    (p : Quiver.Path X Y) → fibrePathPull Λ p ≅ upperStar Λ (composePath p)
  | _, .nil => (upperStarId Λ X).symm
  | _, .cons p f =>
      Functor.isoWhiskerLeft (upperStar Λ f) (fibrePathComparison p) ≪≫
        (upperStarComp Λ (composePath p) f).symm

/-- Finite fibre transport through the canonical iterated module comparison.
The iteration theorem specifies its empty and one-more-arrow equations, so that it is
also the result of applying the binary fibre comparisons one at a time.
Source: latest blueprint, iterated composition comparisons; DAG proof step 8
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
def iteratedFibreComparison {X Y S : Scheme.{u}} (p : Quiver.Path X Y) (w : S ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (v : fibreModuleSections Λ ((upperStar Λ w).obj ((fibrePathPull Λ p).obj M))) :
    fibreModuleSections Λ ((upperStar Λ (w ≫ composePath p)).obj M) :=
  condensedFibreComparison Λ (composePath p) w M
    (v ≫ (upperStar Λ w).map ((fibrePathComparison Λ p).hom.app M))

/-- The composite source automorphism, in the order in which reparametrizations are applied.
Source: latest blueprint, iterated source comparisons; DAG proof step 8
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
def iteratedFibreAutomorphism {S : Scheme.{u}} : List (S ≅ S) → (S ≅ S)
  | [] => Iso.refl _
  | h :: hs => iteratedFibreAutomorphism hs ≪≫ h

/-- The specified r map for a finite composite source automorphism.
The iteration theorem states its empty and one-more-automorphism equations, identifying
it with the result of applying each actual r map successively.
Source: latest blueprint, iterated source comparisons; DAG proof step 8
(blueprint: lem-wf-condensed-fibre-comparison-coherence). -/
def iteratedFibreReparam {S X : Scheme.{u}} (hs : List (S ≅ S)) (z : S ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (v : fibreModuleSections Λ ((upperStar Λ z).obj M)) :
    fibreModuleSections Λ ((upperStar Λ ((iteratedFibreAutomorphism hs).hom ≫ z)).obj M) :=
  condensedFibreReparam Λ z (iteratedFibreAutomorphism hs) M v

private theorem fibreRight_identity {S X : Scheme.{u}} (w : S ⟶ X)
    (f : X ⟶ X) (e : f = 𝟙 X)
    (U : 𝟭 _ ≅ upperStar Λ f)
    (hU : U ≪≫ upperStarCongr Λ e = (upperStarId Λ X).symm)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (v : fibreModuleSections Λ ((upperStar Λ w).obj M)) :
    HEq (condensedFibreComparison Λ f w M
      (v ≫ (upperStar Λ w).map (U.hom.app M))) v := by
  subst f
  have he : U = (upperStarId Λ X).symm := by
    simpa only [upperStarCongr_self, Iso.trans_refl] using hU
  subst U
  have hr := section_right_unit (upperStar Λ w) (upperStar Λ (𝟙 X))
    (upperStarId Λ X) (upperStar Λ (w ≫ 𝟙 X))
    (upperStarCongr Λ (Category.comp_id w)) (upperStarComp Λ w (𝟙 X))
    (upperStarComp_id_right Λ w) M v
  exact (heq_of_eq hr).trans (fibreCongrInv_heq Λ (Category.comp_id w) M v)

set_option maxHeartbeats 1600000 in
-- Keep the source scheme abstract while checking the module coherence calculation.
private theorem fibrePath_nil (S : Scheme.{u}) :
    (∀ {X : Scheme.{u}} (w : S ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (v : fibreModuleSections Λ ((upperStar Λ w).obj M)),
      HEq (iteratedFibreComparison Λ Quiver.Path.nil w M v) v) := by
  intro X w M v
  exact fibreRight_identity Λ w (composePath (Quiver.Path.nil : Quiver.Path X X)) rfl
    (fibrePathComparison Λ Quiver.Path.nil)
    (by simp only [composePath, fibrePathComparison, upperStarCongr_self, Iso.trans_refl]) M v

private theorem fibrePath_step {S X Y Z : Scheme.{u}} (w : S ⟶ X)
    (g : X ⟶ Y) (f : Y ⟶ Z) (q : X ⟶ Z) (eq : q = g ≫ f)
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (E : F ≅ upperStar Λ g)
    (Q : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (eQ : Q = upperStar Λ f ⋙ F) (P : Q ≅ upperStar Λ q)
    (hP : HEq P
      (Functor.isoWhiskerLeft (upperStar Λ f) E ≪≫ (upperStarComp Λ g f).symm))
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (v : fibreModuleSections Λ ((upperStar Λ w).obj (Q.obj M))) :
    HEq (condensedFibreComparison Λ q w M (v ≫ (upperStar Λ w).map (P.hom.app M)))
      (condensedFibreComparison Λ f (w ≫ g) M
        (condensedFibreComparison Λ g w ((upperStar Λ f).obj M)
          (Eq.mp (congrArg
            (fun H : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) ⥤
              Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ↦
                fibreModuleSections Λ ((upperStar Λ w).obj (H.obj M))) eQ) v ≫
            (upperStar Λ w).map (E.hom.app ((upperStar Λ f).obj M))))) := by
  subst q
  subst Q
  have he : P = Functor.isoWhiskerLeft (upperStar Λ f) E ≪≫
      (upperStarComp Λ g f).symm := eq_of_heq hP
  subst P
  dsimp only [Functor.comp_obj] at v
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom]
  have h := fibreComparison_assoc Λ g f w M
    (v ≫ (upperStar Λ w).map (E.hom.app ((upperStar Λ f).obj M)))
  rw [Functor.map_comp,
    ← Category.assoc v ((upperStar Λ w).map (E.hom.app ((upperStar Λ f).obj M)))
      ((upperStar Λ w).map ((upperStarComp Λ g f).inv.app M))]
  exact h

set_option maxHeartbeats 1600000 in
-- Keep the source scheme abstract while checking the module coherence calculation.
private theorem fibrePath_cons (S : Scheme.{u}) :
    (∀ {X Y Z : Scheme.{u}} (p : Quiver.Path X Y) (f : Y ⟶ Z)
      (w : S ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (v : fibreModuleSections Λ
        ((upperStar Λ w).obj ((fibrePathPull Λ (p.cons f)).obj M))),
      HEq (iteratedFibreComparison Λ (p.cons f) w M v)
        (condensedFibreComparison Λ f (w ≫ composePath p) M
          (iteratedFibreComparison Λ p w ((upperStar Λ f).obj M) v))) := by
  intro X Y Z p f w M v
  have h := fibrePath_step Λ w (composePath p) f (composePath (p.cons f)) rfl
    (fibrePathPull Λ p) (fibrePathComparison Λ p) (fibrePathPull Λ (p.cons f)) rfl
    (fibrePathComparison Λ (p.cons f)) (by rfl) M v
  change HEq (condensedFibreComparison Λ (composePath (p.cons f)) w M
    (v ≫ (upperStar Λ w).map ((fibrePathComparison Λ (p.cons f)).hom.app M)))
    (condensedFibreComparison Λ f (w ≫ composePath p) M
      (condensedFibreComparison Λ (composePath p) w ((upperStar Λ f).obj M)
        (v ≫ (upperStar Λ w).map
          ((fibrePathComparison Λ p).hom.app ((upperStar Λ f).obj M)))))
  exact h

set_option maxHeartbeats 1600000 in
-- Keep the source scheme abstract while checking the module coherence calculation.
private theorem fibreReparam_nil (S : Scheme.{u}) :
    (∀ {X : Scheme.{u}} (z : S ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (v : fibreModuleSections Λ ((upperStar Λ z).obj M)),
      HEq (iteratedFibreReparam Λ [] z M v) v) := by
  intro X z M v
  exact fibreUnit_identity Λ z (iteratedFibreAutomorphism []).hom rfl M v

set_option maxHeartbeats 1600000 in
-- Keep the source scheme abstract while checking the module coherence calculation.
private theorem fibreReparam_cons (S : Scheme.{u}) :
    (∀ {X : Scheme.{u}} (hs : List (S ≅ S))
      (h : S ≅ S) (z : S ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (v : fibreModuleSections Λ ((upperStar Λ z).obj M)),
      HEq (iteratedFibreReparam Λ (h :: hs) z M v)
        (iteratedFibreReparam Λ hs (h.hom ≫ z) M (condensedFibreReparam Λ z h M v))) := by
  intro X hs h z M v
  exact (fibreUnit_cocycle Λ z h.hom (iteratedFibreAutomorphism hs).hom
    (iteratedFibreAutomorphism (h :: hs)).hom rfl M v).symm

set_option maxHeartbeats 1600000 in
-- Keep the source scheme abstract while checking the module coherence calculation.
private theorem fibrePath_mixed (S : Scheme.{u}) :
    (∀ {X Y : Scheme.{u}} (p : Quiver.Path X Y) (w : S ⟶ X)
      (h : S ≅ S)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (v : fibreModuleSections Λ ((upperStar Λ w).obj ((fibrePathPull Λ p).obj M))),
      HEq (condensedFibreReparam Λ (w ≫ composePath p) h M
          (iteratedFibreComparison Λ p w M v))
        (iteratedFibreComparison Λ p (h.hom ≫ w) M
          (condensedFibreReparam Λ w h ((fibrePathPull Λ p).obj M) v))) := by
  intro X Y p w h M v
  have ht := fibreReparam_natural Λ w h ((fibrePathComparison Λ p).hom.app M) v
  have hb := fibreReparam_mixed Λ S (composePath p) w h M
    (v ≫ (upperStar Λ w).map ((fibrePathComparison Λ p).hom.app M))
  rw [ht] at hb
  exact hb

set_option maxHeartbeats 1600000 in
-- The finite-path endpoints carry the full internal-module coefficient data.
/-- The fibre and reparametrization identities for every finite iteration, including the
empty iteration, together with the iterated mixed square.
Source: latest blueprint, composition comparisons; DAG proof step 8
(blueprint: lem-wf-condensed-fibre-comparison-coherence).

Proof: the first and third clauses are the unit laws. The second clause follows from
module associativity and the binary fibre identity. The fourth is the source cocycle.
The mixed square for a path cons follows by two binary mixed squares. Naturality
transports the inserted comparisons. Induction then identifies the canonical finite
transports with successive applications of the binary maps. The associative and unit
module equations (`upperStarComp_assoc`, `upperStarComp_id_left`, `upperStarComp_id_right`)
make reassociation and insertion of identities inert. -/
theorem condensedFibre_comparison_iteration (k : Type u) [Field k] [IsAlgClosed k] :
    (∀ {X : Scheme.{u}} (w : Spec (.of k) ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (v : fibreModuleSections Λ ((upperStar Λ w).obj M)),
      HEq (iteratedFibreComparison Λ Quiver.Path.nil w M v) v) ∧
    (∀ {X Y Z : Scheme.{u}} (p : Quiver.Path X Y) (f : Y ⟶ Z)
      (w : Spec (.of k) ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (v : fibreModuleSections Λ
        ((upperStar Λ w).obj ((fibrePathPull Λ (p.cons f)).obj M))),
      HEq (iteratedFibreComparison Λ (p.cons f) w M v)
        (condensedFibreComparison Λ f (w ≫ composePath p) M
          (iteratedFibreComparison Λ p w ((upperStar Λ f).obj M) v))) ∧
    (∀ {X : Scheme.{u}} (z : Spec (.of k) ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (v : fibreModuleSections Λ ((upperStar Λ z).obj M)),
      HEq (iteratedFibreReparam Λ [] z M v) v) ∧
    (∀ {X : Scheme.{u}} (hs : List (Spec (.of k) ≅ Spec (.of k)))
      (h : Spec (.of k) ≅ Spec (.of k)) (z : Spec (.of k) ⟶ X)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (v : fibreModuleSections Λ ((upperStar Λ z).obj M)),
      HEq (iteratedFibreReparam Λ (h :: hs) z M v)
        (iteratedFibreReparam Λ hs (h.hom ≫ z) M (condensedFibreReparam Λ z h M v))) ∧
    (∀ {X Y : Scheme.{u}} (p : Quiver.Path X Y) (w : Spec (.of k) ⟶ X)
      (h : Spec (.of k) ≅ Spec (.of k))
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (v : fibreModuleSections Λ ((upperStar Λ w).obj ((fibrePathPull Λ p).obj M))),
      HEq (condensedFibreReparam Λ (w ≫ composePath p) h M
          (iteratedFibreComparison Λ p w M v))
        (iteratedFibreComparison Λ p (h.hom ≫ w) M
          (condensedFibreReparam Λ w h ((fibrePathPull Λ p).obj M) v))) := by
  exact ⟨fibrePath_nil Λ _, fibrePath_cons Λ _, fibreReparam_nil Λ _,
    fibreReparam_cons Λ _, fibrePath_mixed Λ _⟩

end AlgebraicGeometry.ProEtale.CondensedRing
