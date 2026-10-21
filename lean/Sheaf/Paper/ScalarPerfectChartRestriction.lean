/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Scalar extension commutes with further chart restriction

Source: Stacks Project, sites-modules.tex, Tags 03DH and 04IX.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v s
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}

section Sheafification
variable {U V : C} (f : V ⟶ U) (A : Sheaf J RingCat.{s})
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify (J.over U) AddCommGrpCat.{s}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify (J.over V) AddCommGrpCat.{s}]

private def rawOverMap :
    PresheafOfModules.{s} (A.over U).obj ⥤ PresheafOfModules.{s} (A.over V).obj :=
  PresheafOfModules.pushforward (F := Over.map f) (Sheaf.pushforwardOverMapIso A f).inv.hom

@[irreducible] private def sheafifyMap (P : PresheafOfModules.{s} (A.over U).obj) :
    (PresheafOfModules.sheafification (R := A.over V) (𝟙 _)).obj
      ((rawOverMap f A).obj P) ⟶
    (overMap.{s} A f).obj ((PresheafOfModules.sheafification
      (R := A.over U) (𝟙 _)).obj P) :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := A.over V) (𝟙 _)).homEquiv _ _).symm
    ((rawOverMap f A).map ((PresheafOfModules.sheafificationAdjunction
      (R := A.over U) (𝟙 _)).unit.app P))

private theorem sheafifyMap_unit (P : PresheafOfModules.{s} (A.over U).obj) :
    toSheafify (J.over V) ((Over.map f).op ⋙ P.presheaf) ≫
      (PresheafOfModules.toPresheaf _).map (sheafifyMap f A P).val =
      Functor.whiskerLeft (Over.map f).op (toSheafify (J.over U) P.presheaf) := by
  unfold sheafifyMap
  have h := ((PresheafOfModules.sheafificationAdjunction
    (R := A.over V) (𝟙 _)).homEquiv ((rawOverMap f A).obj P)
    ((overMap.{s} A f).obj ((PresheafOfModules.sheafification
      (R := A.over U) (𝟙 _)).obj P))).apply_symm_apply
    ((rawOverMap f A).map ((PresheafOfModules.sheafificationAdjunction
      (R := A.over U) (𝟙 _)).unit.app P))
  exact congrArg ((PresheafOfModules.toPresheaf (A.over V).obj).map) h

private theorem sheafifyMap_isIso (P : PresheafOfModules.{s} (A.over U).obj) :
    IsIso (sheafifyMap f A P) := by
  let a := toSheafify (J.over V) ((Over.map f).op ⋙ P.presheaf)
  let b := (PresheafOfModules.toPresheaf _).map (sheafifyMap f A P).val
  have : Presheaf.IsLocallyInjective (J.over V) a :=
    ((J.over V).W_toSheafify _).isLocallyInjective
  have : Presheaf.IsLocallySurjective (J.over V) a :=
    ((J.over V).W_toSheafify _).isLocallySurjective
  have hi : Presheaf.IsLocallyInjective (J.over V)
      (Functor.whiskerLeft (Over.map f).op (toSheafify (J.over U) P.presheaf)) :=
    Presheaf.isLocallyInjective_whisker (J.over V) (J.over U) (Over.map f) _
  have hs : Presheaf.IsLocallySurjective (J.over V)
      (Functor.whiskerLeft (Over.map f).op (toSheafify (J.over U) P.presheaf)) :=
    Presheaf.isLocallySurjective_whisker (J.over V) (J.over U) (Over.map f) _
  have hi' : Presheaf.IsLocallyInjective (J.over V) b := by
    rw [← Presheaf.comp_isLocallyInjective_iff (J.over V) a b]
    rw [sheafifyMap_unit]
    exact hi
  have hs' : Presheaf.IsLocallySurjective (J.over V) b := by
    rw [← Presheaf.comp_isLocallySurjective_iff (J.over V) a b]
    rw [sheafifyMap_unit]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (A.over V))]
  apply (Sheaf.isLocallyBijective_iff_isIso (J := J.over V)
    ((SheafOfModules.toSheaf (A.over V)).map (sheafifyMap f A P))).mp
  exact ⟨hi', hs'⟩

private theorem sheafifyMap_naturality {P Q : PresheafOfModules.{s} (A.over U).obj}
    (g : P ⟶ Q) :
    (PresheafOfModules.sheafification (R := A.over V) (𝟙 _)).map
        ((rawOverMap f A).map g) ≫ sheafifyMap f A Q =
      sheafifyMap f A P ≫ (overMap.{s} A f).map
        ((PresheafOfModules.sheafification (R := A.over U) (𝟙 _)).map g) := by
  unfold sheafifyMap
  let L := PresheafOfModules.sheafification (R := A.over U) (𝟙 _)
  let L' := PresheafOfModules.sheafification (R := A.over V) (𝟙 _)
  let a := PresheafOfModules.sheafificationAdjunction (R := A.over U) (𝟙 _)
  let b := PresheafOfModules.sheafificationAdjunction (R := A.over V) (𝟙 _)
  let T := rawOverMap f A
  change L'.map (T.map g) ≫
      (b.homEquiv (T.obj Q) ((overMap.{s} A f).obj (L.obj Q))).symm
        (T.map (a.unit.app Q)) =
    (b.homEquiv (T.obj P) ((overMap.{s} A f).obj (L.obj P))).symm
      (T.map (a.unit.app P)) ≫ (overMap.{s} A f).map (L.map g)
  erw [← b.homEquiv_naturality_left_symm, ← b.homEquiv_naturality_right_symm]
  congr 1
  change T.map g ≫ T.map (a.unit.app Q) =
    T.map (a.unit.app P) ≫ T.map
      ((forget (A.over U) ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map (L.map g))
  rw [← T.map_comp, ← T.map_comp]
  exact congrArg T.map (a.unit.naturality g)



end Sheafification

variable [EssentiallySmall.{s} C]
  [HasSheafify J CommRingCat.{s}] [HasSheafify J AddCommGrpCat.{s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [∀ W : C, EssentiallySmall.{s} (Over W)]
  [∀ W : C, HasSheafify (J.over W) CommRingCat.{s}]
  [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{s}]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{s}]
  {U V : C} (f : V ⟶ U)

attribute [local irreducible] changeOfRingsHomOfUniverses scalarExtensionSection

section ScalarExtension
variable {B₀ B₁ : Sheaf J CommRingCat.{s}} (φ : B₀ ⟶ B₁)
  (M : SheafOfModules.{s} (scalarPerfectRingUnderlying.{c, v, s} J B₀))

private def extensionRawIso :
    changeOfRingsPresheafOfUniverses.{v, max c v, s, s} ((J.overPullback CommRingCat.{s} V).map φ)
      (M.over V) ≅
    (rawOverMap f (scalarPerfectRingUnderlying.{c, v, s} J B₁)).obj
      (changeOfRingsPresheafOfUniverses.{v, max c v, s, s}
        ((J.overPullback CommRingCat.{s} U).map φ)
        (M.over U)) :=
  PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by
    intro W W' g
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact (changeOfRingsMap_tmulOfUniverses.{v, max c v, s, s}
      ((J.overPullback CommRingCat.{s} V).map φ) (M.over V) g 1 x).trans
      (changeOfRingsMap_tmulOfUniverses.{v, max c v, s, s}
        ((J.overPullback CommRingCat.{s} U).map φ) (M.over U)
        ((Over.map f).op.map g) 1 x).symm)

private def extensionOverMapIso :
    (scalarPerfectExtensionFunctor.{max c v, v, s} (J.over V)
      ((J.overPullback CommRingCat.{s} V).map φ)).obj (M.over V) ≅
    (overMap.{s} (scalarPerfectRingUnderlying.{c, v, s} J B₁) f).obj
      ((scalarPerfectExtensionFunctor.{max c v, v, s} (J.over U)
        ((J.overPullback CommRingCat.{s} U).map φ)).obj (M.over U)) := by
  have := sheafifyMap_isIso f (scalarPerfectRingUnderlying.{c, v, s} J B₁)
    (changeOfRingsPresheafOfUniverses.{v, max c v, s, s}
      ((J.overPullback CommRingCat.{s} U).map φ) (M.over U))
  exact (PresheafOfModules.sheafification (R := (scalarPerfectRingUnderlying.{c, v, s} J B₁).over V)
    (𝟙 _)).mapIso (extensionRawIso f φ M) ≪≫
    asIso (sheafifyMap f (scalarPerfectRingUnderlying.{c, v, s} J B₁)
      (changeOfRingsPresheafOfUniverses.{v, max c v, s, s}
        ((J.overPullback CommRingCat.{s} U).map φ) (M.over U)))

private def extensionRawHom (T : C)
    {M N : SheafOfModules.{s} (scalarPerfectRingUnderlying.{c, v, s} J B₀)} (g : M ⟶ N) :
    changeOfRingsPresheafOfUniverses.{v, max c v, s, s}
      ((J.overPullback CommRingCat.{s} T).map φ) (M.over T) ⟶
    changeOfRingsPresheafOfUniverses.{v, max c v, s, s}
      ((J.overPullback CommRingCat.{s} T).map φ) (N.over T) :=
  { app := fun W ↦ (ModuleCat.extendScalars
        (((J.overPullback CommRingCat.{s} T).map φ).hom.app W).hom).map
          ((g.over T).val.app W)
    naturality := changeOfRingsHom_naturalityOfUniverses
      ((J.overPullback CommRingCat.{s} T).map φ) (M.over T) (g.over T) }

omit [HasSheafify J CommRingCat.{s}] [HasSheafify J AddCommGrpCat.{s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [∀ W : C, HasSheafify (J.over W) CommRingCat.{s}] in
private theorem extensionRawIso_naturality
    {M N : SheafOfModules.{s} (scalarPerfectRingUnderlying.{c, v, s} J B₀)} (g : M ⟶ N) :
    extensionRawHom φ V g ≫ (extensionRawIso f φ N).hom =
      (extensionRawIso f φ M).hom ≫
        (rawOverMap f (scalarPerfectRingUnderlying.{c, v, s} J B₁)).map
          (extensionRawHom φ U g) := by
  ext W : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  rfl

omit [HasSheafify J CommRingCat.{s}] [HasSheafify J AddCommGrpCat.{s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [∀ W : C, HasSheafify (J.over W) CommRingCat.{s}] in
private theorem extensionOverMapIso_naturality
    {M N : SheafOfModules.{s} (scalarPerfectRingUnderlying.{c, v, s} J B₀)} (g : M ⟶ N) :
    (scalarPerfectExtensionFunctor.{max c v, v, s} (J.over V)
      ((J.overPullback CommRingCat.{s} V).map φ)).map (g.over V) ≫
        (extensionOverMapIso f φ N).hom =
      (extensionOverMapIso f φ M).hom ≫
        (overMap.{s} (scalarPerfectRingUnderlying.{c, v, s} J B₁) f).map
          ((scalarPerfectExtensionFunctor.{max c v, v, s} (J.over U)
            ((J.overPullback CommRingCat.{s} U).map φ)).map (g.over U)) := by
  let L := PresheafOfModules.sheafification
    (R := (scalarPerfectRingUnderlying.{c, v, s} J B₁).over V) (𝟙 _)
  let L₀ := PresheafOfModules.sheafification
    (R := (scalarPerfectRingUnderlying.{c, v, s} J B₁).over U) (𝟙 _)
  let H := overMap.{s} (scalarPerfectRingUnderlying.{c, v, s} J B₁) f
  let g' := extensionRawHom φ U g
  dsimp only [scalarPerfectExtensionFunctor, changeOfRingsHomOfUniverses,
    extensionOverMapIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  unfold changeOfRingsHomOfUniverses
  change L.map (extensionRawHom φ V g) ≫
      (L.map (extensionRawIso f φ N).hom ≫ sheafifyMap f _ _) =
    (L.map (extensionRawIso f φ M).hom ≫ sheafifyMap f _ _) ≫ H.map (L₀.map g')
  rw [← L.map_comp_assoc, extensionRawIso_naturality, L.map_comp, Category.assoc]
  rw [sheafifyMap_naturality f (scalarPerfectRingUnderlying.{c, v, s} J B₁) g']
  rfl

end ScalarExtension


variable
  (R : Type s) [CommRing R]
  {B : Sheaf J CommRingCat.{s}} (φ : scalarPerfectRing J R ⟶ B)

omit [∀ W : C, HasSheafify (J.over W) CommRingCat.{s}] in
/-- Further restriction of scalar models agrees naturally with the direct chart model.
Source: Stacks Project, sites-modules.tex, Tags 03DH and 04IX. At a test object
W over the smaller chart, both sectionwise scalar extensions have the same tensor
module and restriction maps. The comparison from sheafification to restricted
sheafification is invertible since its composition with the local unit is the
restricted global unit, which is locally bijective by cocontinuity. This comparison
is natural in module maps, and therefore in the differentials of any complex.
(blueprint: lem-sfb-scalar-perfect-chart-restriction). -/
theorem scalarPerfectChartRestrictionIso :
    Nonempty (scalarPerfectChartFunctor J R φ V ≅
      scalarPerfectChartFunctor J R φ U ⋙
        overMap.{s} (scalarPerfectRingUnderlying.{c, v, s} J B) f) := by
  exact ⟨NatIso.ofComponents
    (fun M ↦ extensionOverMapIso f φ ((scalarPerfectConstantFunctor J R).obj M))
    (fun g ↦ extensionOverMapIso_naturality f φ
      ((scalarPerfectConstantFunctor J R).map g))⟩

end SheafOfModules
