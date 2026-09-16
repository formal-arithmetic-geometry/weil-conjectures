module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Stalk

@[expose] public section
universe u
open CategoryTheory Limits Opposite TopologicalSpace PresheafOfModules

namespace SheafOfModules

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X} {M : SheafOfModules.{u} R}

/-- target -/
noncomputable abbrev valRestrict (M : SheafOfModules.{u} R) : PresheafOfModules.{u} R.obj :=
  (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj ((SheafOfModules.forget R).obj M)

example : (valRestrict M).presheaf = M.val.presheaf := rfl
example : (valRestrict M).sections = M.val.sections := rfl

/-- the constant presheaf of types -/
noncomputable abbrev constPresheaf (I : Type u) : (Opens X)ᵒᵖ ⥤ Type u :=
  (Functor.const _).obj I

/-- natural transformation -/
noncomputable def sectionsNatTrans (I : Type u) (s : I → M.sections) :
    constPresheaf (X := X) I ⟶ M.val.presheaf ⋙ CategoryTheory.forget Ab where
  app V := ↾fun i ↦ (s i).1 V
  naturality _ _ f := by ext i; simpa using ((s i).2 f).symm

noncomputable def freeObjHom (I : Type u) (s : I → M.sections) :
    freeObj (R := R.obj) (constPresheaf (X := X) I) ⟶ valRestrict M :=
  freeObjDesc (sectionsNatTrans I s)

end SheafOfModules

namespace Step2

open PresheafOfModules

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X} {M : SheafOfModules.{u} R}
variable (I : Type u) (s : I → M.sections)

example : True := trivial

#check @PresheafOfModules.sheafificationAdjunction
#check (PresheafOfModules.sheafification (𝟙 R.obj) :
  PresheafOfModules.{u} R.obj ⥤ SheafOfModules.{u} R)
#check (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj) :
  PresheafOfModules.sheafification.{u} (𝟙 R.obj) ⊣ _)

lemma freeObjHom_app_freeMk (V : (Opens X)ᵒᵖ) (i : I) :
    Hom.app (SheafOfModules.freeObjHom I s) V (ModuleCat.freeMk i) = (s i).1 V := by
  exact ModuleCat.freeDesc_apply _ i


/-- the sheafification of the free presheaf of modules on the constant presheaf `I` -/
noncomputable def freeSheafify (I : Type u) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj (freeObj (SheafOfModules.constPresheaf (X := X) I))

/-- unit -/
noncomputable def freeSheafifyUnit (I : Type u) :
    freeObj (SheafOfModules.constPresheaf (X := X) I) ⟶
      (SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)).obj (freeSheafify (R := R) I) :=
  (sheafificationAdjunction (𝟙 R.obj)).unit.app _

/-- descent -/
noncomputable def freeSheafifyDesc : freeSheafify (R := R) I ⟶ M :=
  ((sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).symm (SheafOfModules.freeObjHom I s)

lemma freeSheafifyUnit_comp :
    freeSheafifyUnit (R := R) I ≫
      (SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)).map (freeSheafifyDesc I s) =
      SheafOfModules.freeObjHom I s := by
  have h := Equiv.apply_symm_apply ((sheafificationAdjunction (𝟙 R.obj)).homEquiv
    (freeObj (SheafOfModules.constPresheaf (X := X) I)) M) (SheafOfModules.freeObjHom I s)
  rwa [Adjunction.homEquiv_unit] at h

/-- tautological sections of the free presheaf of modules -/
noncomputable def freeObjSection (i : I) :
    (freeObj (R := R.obj) (SheafOfModules.constPresheaf (X := X) I)).sections :=
  PresheafOfModules.sectionsMk (fun _ ↦ ModuleCat.freeMk i) (by
    intro V W f
    exact ModuleCat.freeDesc_apply _ i)

end Step2
