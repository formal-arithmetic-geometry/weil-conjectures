module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.CondensedActionModule
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.CategoryTheory.Sites.Subsheaf
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction

variable {R : Profinite.CondensedRing.{u}} [IsCommMonObj R.X]
  {P : Type u} [TopologicalSpace P] [Group P] [IsTopologicalGroup P]

/-- The sectionwise sheaf of modules of an internal module. -/
abbrev sectionSheaf (M : Modules R) :=
  (InternalAbelianSheafModule.sectionModuleFunctor (coherentTopology Profinite.{u}) R.X).obj M

lemma map_hom_apply_eq (M : Modules R) {S T : Profinite.{u}} (f : T ⟶ S)
    (m : sectionModule R M S) :
    (M.X.obj.map f.op).hom m = (sectionSheaf M).val.map f.op m := rfl

/-- The fixed sections form a sub-presheaf of modules. -/
def fixedSubmodule (M : ActionModule R P) : (sectionSheaf M.module).val.Submodule where
  obj S :=
    { carrier := {m | FixedAll M S.unop m}
      zero_mem' := by
        intro T f g
        simp
      add_mem' := by
        intro m n hm hn T f g
        simp only [map_add, hm T f g, hn T f g]
      smul_mem' := by
        intro r m hm T f g
        rw [map_hom_apply_eq, PresheafOfModules.map_smul, map_smul, ← map_hom_apply_eq,
          hm T f g] }
  map {S S'} f := by
    intro m hm T g p
    have h := hm T (g ≫ f.unop) p
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp, AddCommGrpCat.hom_comp,
      AddMonoidHom.coe_comp, Function.comp_apply] at h
    exact h

end Profinite.CondensedAction

namespace Profinite.CondensedAction

variable {R : Profinite.CondensedRing.{u}} [IsCommMonObj R.X]
  {P : Type u} [TopologicalSpace P] [Group P] [IsTopologicalGroup P]

lemma FixedAll.act_eq {M : ActionModule R P} {S : Profinite.{u}} {m : sectionModule R M.module S}
    (h : FixedAll M S m) (g : C(S, P)) : M.act S g m = m := by
  have h1 := h S (𝟙 S) g
  rw [op_id, M.module.X.obj.map_id] at h1
  exact h1

theorem fixedSubmodule_isSheaf (M : ActionModule R P) :
    Presheaf.IsSheaf (coherentTopology Profinite.{u})
      (fixedSubmodule M).toPresheafOfModules.presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget AddCommGrpCat.{u + 1}),
    isSheaf_iff_isSheaf_of_type]
  have hM : Presieve.IsSheaf (coherentTopology Profinite.{u})
      (M.module.X.obj ⋙ forget AddCommGrpCat.{u + 1}) := by
    rw [← isSheaf_iff_isSheaf_of_type,
      ← Presheaf.isSheaf_iff_isSheaf_forget (s := forget AddCommGrpCat.{u + 1})]
    exact M.module.X.property
  let F : Subfunctor (M.module.X.obj ⋙ forget AddCommGrpCat.{u + 1}) :=
    { obj S := {m | FixedAll M S.unop m}
      map f := (fixedSubmodule M).map f }
  change Presieve.IsSheaf _ F.toFunctor
  refine (Subfunctor.isSheaf_iff _ hM).2 fun S m hm T f p ↦ ?_
  refine (hM _ ((coherentTopology Profinite.{u}).pullback_stable f hm)).isSeparatedFor.ext
    fun Z g hg ↦ ?_
  have key : (M.module.X.obj.map g.op).hom (M.act T p ((M.module.X.obj.map f.op).hom m)) =
      (M.module.X.obj.map g.op).hom ((M.module.X.obj.map f.op).hom m) := by
    rw [M.naturality T Z g p]
    have h := FixedAll.act_eq hg (p.comp g.hom.hom)
    simp only [op_comp, Functor.map_comp, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
      Function.comp_apply] at h
    exact h
  exact key

variable (R) in
/-- Sectionwise sheaves of modules over the section ring sheaf of `R`. -/
abbrev SectionModules :=
  SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat RingCat)).obj
      (InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) R.X))

variable (R) in
/-- The internal-module equivalence on the coherent profinite site. -/
abbrev sectionEquivalence : Modules R ≌ SectionModules R :=
  InternalAbelianSheafModule.sectionModuleEquivalence (coherentTopology Profinite.{u}) R.X

/-- The sheaf of modules of fixed sections. -/
def fixedSheaf (M : ActionModule R P) : SectionModules R :=
  ⟨(fixedSubmodule M).toPresheafOfModules, fixedSubmodule_isSheaf M⟩

/-- Equivariant maps preserve fixed sections. -/
lemma FixedAll.map {M N : ActionModule R P} (a : M ⟶ N) {S : Profinite.{u}}
    {m : sectionModule R M.module S} (h : FixedAll M S m) :
    FixedAll N S ((a.val.hom.hom.app (op S)).hom m) := by
  intro T f g
  have hn : (N.module.X.obj.map f.op).hom ((a.val.hom.hom.app (op S)).hom m) =
      (a.val.hom.hom.app (op T)).hom ((M.module.X.obj.map f.op).hom m) :=
    (ConcreteCategory.congr_hom (a.val.hom.hom.naturality f.op) m).symm
  rw [hn, ← a.property T g, h T f g]

variable (R P) in
/-- The fixed-section functor to sectionwise sheaves of modules. -/
def fixedFunctor : ActionModule R P ⥤ SectionModules R where
  obj M := fixedSheaf M
  map {M N} a := ⟨(fixedSubmodule N).lift ((fixedSubmodule M).ι ≫
    ((sectionEquivalence R).functor.map a.val).val) fun S x ↦ FixedAll.map a x.property⟩
  map_id M := by
    ext S x
    rfl
  map_comp a b := by
    ext S x
    rfl

variable (R P) in
/-- The inclusion of fixed sections into all sections. -/
def fixedInclusion :
    fixedFunctor R P ⟶ forgetAction ⋙ (sectionEquivalence R).functor where
  app M := ⟨(fixedSubmodule M).ι⟩
  naturality {M N} a := by
    ext S x
    rfl

variable (R P) in
/-- The invariants functor: fixed sections, read back as internal modules. -/
def invariantsFunctor : ActionModule R P ⥤ Modules R :=
  fixedFunctor R P ⋙ (sectionEquivalence R).inverse

variable (R P) in
/-- The inclusion of invariants into the underlying internal module. -/
def invariantsInclusion : invariantsFunctor R P ⟶ forgetAction where
  app M := (sectionEquivalence R).inverse.map ((fixedInclusion R P).app M) ≫
    (sectionEquivalence R).unitInv.app M.module
  naturality {M N} a := by
    have h := (fixedInclusion R P).naturality a
    simp only [Functor.comp_map] at h
    simp only [invariantsFunctor, Functor.comp_obj, Functor.comp_map, Category.assoc,
      ← Functor.map_comp_assoc, h]
    simp [forgetAction]

/-- The sectionwise inclusion of invariants is the counit followed by the fixed inclusion. -/
lemma functor_map_invariantsInclusion (M : ActionModule R P) :
    (sectionEquivalence R).functor.map ((invariantsInclusion R P).app M) =
      (sectionEquivalence R).counit.app ((fixedFunctor R P).obj M) ≫
        (fixedInclusion R P).app M := by
  rw [invariantsInclusion, Functor.map_comp, ← Equivalence.counit_app_functor]
  exact (sectionEquivalence R).counit.naturality ((fixedInclusion R P).app M)

/-- Sections of the invariants inclusion: the counit followed by the fixed inclusion. -/
lemma invariantsInclusion_app_apply (M : ActionModule R P) (S : Profinite.{u})
    (x : sectionModule R ((invariantsFunctor R P).obj M) S) :
    (((invariantsInclusion R P).app M).hom.hom.app (op S)).hom x =
      (((sectionEquivalence R).counit.app ((fixedFunctor R P).obj M)).val.app (op S) x).val :=
  congrArg (fun φ ↦ φ.val.app (op S) x) (functor_map_invariantsInclusion M)

lemma sectionModules_iso_inv_hom_apply {A B : SectionModules R} (e : A ≅ B) (X : Profinite.{u}ᵒᵖ)
    (x : B.val.obj X) : e.hom.val.app X (e.inv.val.app X x) = x :=
  congrArg (fun φ : B ⟶ B ↦ φ.val.app X x) e.inv_hom_id

lemma sectionModules_iso_hom_inv_apply {A B : SectionModules R} (e : A ≅ B) (X : Profinite.{u}ᵒᵖ)
    (x : A.val.obj X) : e.inv.val.app X (e.hom.val.app X x) = x :=
  congrArg (fun φ : A ⟶ A ↦ φ.val.app X x) e.hom_inv_id

lemma invariantsInclusion_injective (M : ActionModule R P) (S : Profinite.{u}) :
    Function.Injective ((((invariantsInclusion R P).app M).hom.hom.app (op S)).hom) := by
  intro x y h
  rw [invariantsInclusion_app_apply, invariantsInclusion_app_apply] at h
  let e := (sectionEquivalence R).counitIso.app ((fixedFunctor R P).obj M)
  have h' := congrArg (e.inv.val.app (op S)) (Subtype.ext h)
  exact (sectionModules_iso_hom_inv_apply e (op S) x).symm.trans
    (h'.trans (sectionModules_iso_hom_inv_apply e (op S) y))

lemma invariantsInclusion_image (M : ActionModule R P) (S : Profinite.{u})
    (m : sectionModule R M.module S) :
    (∃ x : sectionModule R ((invariantsFunctor R P).obj M) S,
      (((invariantsInclusion R P).app M).hom.hom.app (op S)).hom x = m) ↔ FixedAll M S m := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [invariantsInclusion_app_apply] at hx
    rw [← hx]
    exact Subtype.property _
  · refine ⟨((sectionEquivalence R).counitIso.app
      ((fixedFunctor R P).obj M)).inv.val.app (op S) ⟨m, h⟩, ?_⟩
    rw [invariantsInclusion_app_apply]
    exact congrArg Subtype.val (sectionModules_iso_inv_hom_apply
      ((sectionEquivalence R).counitIso.app ((fixedFunctor R P).obj M)) (op S) ⟨m, h⟩)

end Profinite.CondensedAction
