/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Directed ring-sheaf colimits as module-sheaf colimits

Source: agent assembly from Stacks Project, Modules on Sites, Tags 03DB
(lemma-limits-colimits) and 03EP (lemma-tensor-commute-colimits), item (2).
(blueprint: lem-sfb-directed-ring-sheaf-module-colimit).

The conclusion is the explicit existence-and-uniqueness universal property. Compatibility
and factorization are equalities on sections, so no separate choice of linear transition
maps or cocone legs is involved.

## Main definitions

* `siteRingSheafModule`: the existing regular module restricted along the scalar map.

## Main statements

* `directedRingSheaf_module_colimit`: the explicit module-colimit universal property.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The module underlying a ring sheaf with its specified scalar map: restrict the regular
module along that map. Thus on each object its scalar action is `r • x = s(r) * x`.
This is only an abbreviation for Mathlib's restriction of scalars and regular module.
Source: Stacks Project, Modules on Sites, module structures used in Tags 03DB and 03EP.
(blueprint: lem-sfb-directed-ring-sheaf-module-colimit). -/
noncomputable abbrev siteRingSheafModule {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R A : Sheaf J CommRingCat.{w}} (s : R ⟶ A) :
    ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map s)).obj
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A))

set_option backward.isDefEq.respectTransparency false in
/-- A scalar-compatible ring map is linear on the restricted regular modules. -/
private noncomputable def siteRingSheafModuleMap
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R B D : Sheaf J CommRingCat.{w}}
    {sB : R ⟶ B} {sD : R ⟶ D} (f : B ⟶ D) (hf : sB ≫ f = sD) :
    siteRingSheafModule sB ⟶ siteRingSheafModule sD where
  val := PresheafOfModules.homMk
    (Functor.whiskerRight f.hom
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
        intro U r x
        change B.obj.obj U at x
        change R.obj.obj U at r
        change f.hom.app U (sB.hom.app U r * x) =
          sD.hom.app U r * f.hom.app U x
        rw [map_mul]
        congr 1
        exact congrArg (fun t ↦ t.hom.app U r) hf)

/-- The ring-colimit cocone has the module-colimit universal property with exactly the
same maps on sections and the scalar actions induced by the specified structure maps.
Source: agent assembly from Stacks Project, Modules on Sites, Tags 03DB and 03EP(2).
(blueprint: lem-sfb-directed-ring-sheaf-module-colimit).

Proof:
1. The compatible scalar maps make each transition map and cocone leg linear. Form
   the diagram D of restricted regular modules and its cocone d with the original
   maps on sections.
2. On the coefficient-sized small model of the site, forgetting commutative rings
   to abelian groups preserves sheafification: it preserves limits and filtered
   colimits, including colimits over covering sieves. Transport this property to C.
3. The sheafification comparison and the fully faithful sheafification adjunction
   imply that forgetting ring sheaves preserves I-colimits. Thus the underlying
   abelian cocone of q, which is the underlying abelian cocone of d, is a colimit.
4. By lem-weil-pbc-module-sheaves-colimits-forgetful, forgetting module sheaves
   preserves I-colimits. It also reflects isomorphisms and module-sheaf colimits
   exist, so it reflects this colimit. Hence d is a module colimit.
5. Package fᵢ as a cocone on D. The descent map of d supplies existence, and its
   uniqueness property supplies uniqueness, both with the required sectionwise
   factorization equations.

This sheafification argument avoids constructing multiplication on a module colimit;
it is the general-site version of the argument in the source library's
SheafAlgebrasDirectedColimitModuleCore. -/
theorem directedRingSheaf_module_colimit
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (I : Type w) [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (A : I ⥤ Sheaf J CommRingCat.{w})
    (sᵢ : (Functor.const I).obj R ⟶ A)
    (q : Cocone A) (_hq : IsColimit q) (s : R ⟶ q.pt)
    (_hs : ∀ i : I, sᵢ.app i ≫ q.ι.app i = s)
    (M : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (fᵢ : ∀ i : I, siteRingSheafModule (sᵢ.app i) ⟶ M)
    (_hf : ∀ (i j : I) (h : i ≤ j) (U : Cᵒᵖ) (x : (A.obj i).obj.obj U),
      (fᵢ j).val.app U ((A.map (homOfLE h)).hom.app U x) = (fᵢ i).val.app U x) :
    ∃! f : siteRingSheafModule s ⟶ M,
      ∀ (i : I) (U : Cᵒᵖ) (x : (A.obj i).obj.obj U),
        f.val.app U ((q.ι.app i).hom.app U x) = (fᵢ i).val.app U x := by
  set_option backward.isDefEq.respectTransparency false in
  classical
  let O := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{w}
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op)
        CommRingCat.{w} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  have : HasSheafify J CommRingCat.{w} := hasSheafifyEssentiallySmallSite J _
  have : HasSheafify J AddCommGrpCat.{w} := hasSheafifyEssentiallySmallSite J _
  have : J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  have : PreservesLimits U := inferInstance
  have : PreservesFilteredColimits U :=
    comp_preservesFilteredColimits (forget₂ CommRingCat RingCat)
      (forget₂ RingCat AddCommGrpCat)
  have : ((equivSmallModel.{w} C).inverse.inducedTopology J).PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification _ U
  have : J.PreservesSheafification U := inferInstance
  have : PreservesColimitsOfShape I U := inferInstance
  have : PreservesColimitsOfShape I (sheafCompose J U) := by
    rw [(sheafificationAdjunction J CommRingCat.{w}).preservesColimitsOfShape_iff]
    exact preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J U (sheafificationAdjunction J CommRingCat.{w})
        (sheafificationAdjunction J AddCommGrpCat.{w}))
  let D : I ⥤ SheafOfModules.{w} O :=
    { obj := fun i ↦ siteRingSheafModule (sᵢ.app i)
      map := fun {i j} h ↦ siteRingSheafModuleMap (A.map h) (by
        simpa using (sᵢ.naturality h).symm)
      map_id := by
        intro i
        ext V x
        change (A.map (𝟙 i)).hom.app V x = x
        simp
      map_comp := by
        intro i j k f g
        ext V x
        change (A.map (f ≫ g)).hom.app V x =
          (A.map g).hom.app V ((A.map f).hom.app V x)
        simp }
  let d : Cocone D :=
    { pt := siteRingSheafModule s
      ι :=
        { app := fun i ↦ siteRingSheafModuleMap (q.ι.app i) (_hs i)
          naturality := by
            intro i j h
            ext V x
            exact congrArg (fun t ↦ t.hom.app V x) (q.w h) } }
  have ha : IsColimit ((sheafCompose J U).mapCocone q) :=
    isColimitOfPreserves (sheafCompose J U) _hq
  have : PreservesColimitsOfShape I (SheafOfModules.toSheaf.{w} O) :=
    ((moduleSheaves_colimits_forgetful O).2.2.2.2.2 I).2.1
  have : ReflectsColimit D (SheafOfModules.toSheaf O) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  have hd : IsColimit d := isColimitOfReflects (SheafOfModules.toSheaf O) ha
  let c : Cocone D :=
    { pt := M
      ι :=
        { app := fᵢ
          naturality := by
            intro i j h
            ext V x
            exact _hf i j (leOfHom h) V x } }
  refine ⟨hd.desc c, ?_, ?_⟩
  · intro i V x
    exact congrArg (fun t ↦ t.val.app V x) (hd.fac c i)
  · intro f hf
    apply hd.uniq c f
    intro i
    ext V x
    exact hf i V x

end CategoryTheory
