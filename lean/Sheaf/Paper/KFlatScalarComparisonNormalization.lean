/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.CategoryTheory.FlatRestrictionOrdinaryComparisons
import all Sheaf.CategoryTheory.SiteAlgebraicCompositionUnit
import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import all Sheaf.CategoryTheory.DerivedExactSquareComposition
import Sheaf.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import Sheaf.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Sheaf.Algebra.Homology.SheafRingDerivedHomComparison
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import all Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import all Sheaf.CategoryTheory.DerivedCategory.CokernelAdjointExchange
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
import all Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitExistence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison

/-! # Normalization of scalar pullback on K-flat representatives

Source: blueprint main-20261015, det-prop-scalar-six-pullback (1); Stacks Project,
Tags 03EL, 0G7E, 06YY, 07A6 and 0D6D
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).

## Main statements

- `kflat_scalar_comparison_normalization`: balanced comparison and specified derived mate.
- `θ_composition`, `θ_identity`: geometric composition and identity normalization.

The ordinary comparison is specified on generalized pure tensors, including its
scalar-extension units. The derived comparison is the inverse mate of the action
identification, rather than an unspecified isomorphism of functors. Its representative
formula uses the counits of the existing universal derived-change-of-rings models.
-/

@[expose] public section
set_option autoImplicit false
universe u w u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules.ScalarPullback

/-- The module category already used by the scalar-change model.
Source: Stacks 03D2 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev Modules {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (A : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)

/-- Forget a module to its underlying sheaf of sets.
Source: Stacks 03D2 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
noncomputable abbrev underlying {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (A : Sheaf J CommRingCat.{u}) : Modules A ⥤ Sheaf J (Type u) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u} ⋙ uliftFunctor.{u, u})

/-- Restriction of scalars along the given sheaf ring map.
Source: Stacks 03D2 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
noncomputable abbrev restriction {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    Modules B ⥤ Modules A :=
  restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)

section InverseImageAliases

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The existing algebraic inverse-image presentation in the small-site universe.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev InverseImage (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u}) :=
  AlgebraicInverseImageOfUniverses.{u, u, u, u, u, u} L A B

variable {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}

/-- The existing module projection, with its sheaf-composition instances elaborated once.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev inverseModules (I : InverseImage L A B) : Modules A ⥤ Modules B := I.modules

/-- The existing ring identification of the algebraic inverse-image presentation.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev inverseRing (I : InverseImage L A B) :
    L.obj ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj A) ≅
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj B :=
  I.ringUnderlying

/-- The existing underlying-module identification of the inverse-image presentation.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev inverseUnderlying (I : InverseImage L A B) :
    inverseModules I ⋙ underlying B ≅ underlying A ⋙ L :=
  I.moduleUnderlying

end InverseImageAliases

/-- The image of a balanced pure tensor in the model's ordinary scalar extension.
The equality transport only identifies the model's object with the existing sheafification.
Source: Stacks 03EL (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
noncomputable def pure {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ) (M : Modules A) (U : Cᵒᵖ)
    (b : B.obj.obj U) (x : M.val.obj U) : (m.E.obj M).val.obj U :=
  (eqToHom (m.obj_eq M).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
      (b ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x))

/-- The inverse scalar-adjunction mate of a restriction/action square.
Source: Stacks 07A7 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
def mate {AY : Type u₁} {BY : Type u₂} {AX : Type u₃} {BX : Type u₄}
    [Category.{v₁} AY] [Category.{v₂} BY] [Category.{v₃} AX] [Category.{v₄} BX]
    {TY : AY ⥤ BY} {rY : BY ⥤ AY} {TX : AX ⥤ BX} {rX : BX ⥤ AX}
    (dY : TY ⊣ rY) (dX : TX ⊣ rX) {IA : AY ⥤ AX} {IB : BY ⥤ BX}
    (a : rY ⋙ IA ⟶ IB ⋙ rX) : IA ⋙ TX ⟶ TY ⋙ IB :=
  ((mateEquiv dY dX).symm (TwoSquare.mk _ _ _ _ a)).natTrans

/-- The normalized coefficient adjunction, expressed with the model's cochain counit.
This is the unit clause of the existing derived coefficient adjunction, transported
from homotopy localization to cochain localization by quotientCompQhIso.
Source: Stacks 07A6 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
def AdjunctionNormalized {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (a : m.E ⊣ restriction φ) (d : m.T ⊣ (restriction φ).mapDerivedCategory) : Prop :=
  (∀ (M : Modules A) (U : Cᵒᵖ) (x : M.val.obj U),
    (a.unit.app M).val.app U x = pure m M U 1 x) ∧
  ∀ (P : CochainComplex (Modules A) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u, u, u} (J := J) (R := A) P →
    (∀ n : ℤ, IsFlatOnSite.{u, u, u, u} (J := J) (R := A) (P.X n)) →
    d.unit.app (DerivedCategory.Q.obj P) ≫
        (restriction φ).mapDerivedCategory.map (m.ε.app P) ≫
        (restriction φ).mapDerivedCategoryFactors.hom.app
          ((m.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def unliftInverseImageAux
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (I : InverseImage L A B) : AlgebraicInverseImage L A B := by
  let eR := SheafOfModules.sheafUliftIso J CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eS := SheafOfModules.sheafUliftIso K CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eM := Functor.isoWhiskerLeft (toSheaf ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) <|
    SheafOfModules.sheafUliftIso J AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let eN := Functor.isoWhiskerLeft (toSheaf ((sheafCompose K
    (forget₂ CommRingCat.{u} RingCat.{u})).obj B)) <|
    SheafOfModules.sheafUliftIso K AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let er := L.mapIso (eR.app A).symm ≪≫ I.ringUnderlying ≪≫ eS.app B
  let em := Functor.isoWhiskerLeft I.modules eN.symm ≪≫ I.moduleUnderlying ≪≫
    Functor.isoWhiskerRight eM L
  refine
    { ringUnderlying := er
      modules := I.modules
      moduleUnderlying := em
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I.ringAdd T (a ≫ (eR.app A).inv) (b ≫ (eR.app A).inv)
      (t ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I.ringMul T (a ≫ (eR.app A).inv) (b ≫ (eR.app A).inv)
      (t ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringZero T (a ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringOne T (a ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleAdd M T (a ≫ (eM.app M).inv) (b ≫ (eM.app M).inv)
      (t ≫ (eM.app M).inv) h V x
    simpa [em, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I.moduleZero M T (a ≫ (eM.app M).inv) h V x
    simpa [em, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleSMul M T (a ≫ (eR.app A).inv) (b ≫ (eM.app M).inv)
      (t ≫ (eM.app M).inv) h V x
    simpa [er, em, eR, eS, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial,
      Functor.map_comp] using hr

-- Keep the presentation's data projections small. The graph-law proofs live in the
-- auxiliary construction, so using a module or ring projection does not copy those proofs.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def unliftInverseImage
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (I : InverseImage L A B) : AlgebraicInverseImage L A B := by
  let eR := SheafOfModules.sheafUliftIso J CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eS := SheafOfModules.sheafUliftIso K CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eM := Functor.isoWhiskerLeft (toSheaf ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) <|
    SheafOfModules.sheafUliftIso J AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let eN := Functor.isoWhiskerLeft (toSheaf ((sheafCompose K
    (forget₂ CommRingCat.{u} RingCat.{u})).obj B)) <|
    SheafOfModules.sheafUliftIso K AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let er := L.mapIso (eR.app A).symm ≪≫ I.ringUnderlying ≪≫ eS.app B
  let em := Functor.isoWhiskerLeft I.modules eN.symm ≪≫ I.moduleUnderlying ≪≫
    Functor.isoWhiskerRight eM L
  exact
    { ringUnderlying := er
      modules := I.modules
      moduleUnderlying := em
      ringAdd := (unliftInverseImageAux I).ringAdd
      ringMul := (unliftInverseImageAux I).ringMul
      ringZero := (unliftInverseImageAux I).ringZero
      ringOne := (unliftInverseImageAux I).ringOne
      moduleAdd := (unliftInverseImageAux I).moduleAdd
      moduleZero := (unliftInverseImageAux I).moduleZero
      moduleSMul := (unliftInverseImageAux I).moduleSMul }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def compositeInverseImageAux
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {H : GrothendieckTopology E}
    {F : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf H (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    {S : Sheaf H CommRingCat.{u}}
    (I : InverseImage F A B) (I' : InverseImage G B S) : InverseImage (F ⋙ G) A S := by
  let er := G.mapIso I.ringUnderlying ≪≫ I'.ringUnderlying
  let em : (I.modules ⋙ I'.modules) ⋙ underlying S ≅ underlying A ⋙ (F ⋙ G) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft I.modules I'.moduleUnderlying ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight I.moduleUnderlying G ≪≫ Functor.associator _ _ _
  refine
    { ringUnderlying := er
      modules := I.modules ⋙ I'.modules
      moduleUnderlying := em
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I'.ringAdd (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (F.map b ≫ I.ringUnderlying.hom) (F.map t ≫ I.ringUnderlying.hom)
      (I.ringAdd T a b t h) V x
    simpa [er, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I'.ringMul (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (F.map b ≫ I.ringUnderlying.hom) (F.map t ≫ I.ringUnderlying.hom)
      (I.ringMul T a b t h) V x
    simpa [er, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I'.ringZero (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (I.ringZero T a h) V x
    simpa [er, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I'.ringOne (F.obj T) (F.map a ≫ I.ringUnderlying.hom)
      (I.ringOne T a h) V x
    simpa [er, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I'.moduleAdd (I.modules.obj M) (F.obj T)
      (F.map a ≫ I.moduleUnderlying.inv.app M)
      (F.map b ≫ I.moduleUnderlying.inv.app M)
      (F.map t ≫ I.moduleUnderlying.inv.app M) (I.moduleAdd M T a b t h) V x
    simpa [em, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I'.moduleZero (I.modules.obj M) (F.obj T)
      (F.map a ≫ I.moduleUnderlying.inv.app M) (I.moduleZero M T a h) V x
    simpa [em, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I'.moduleSMul (I.modules.obj M) (F.obj T)
      (F.map a ≫ I.ringUnderlying.hom)
      (F.map b ≫ I.moduleUnderlying.inv.app M)
      (F.map t ≫ I.moduleUnderlying.inv.app M) (I.moduleSMul M T a b t h) V x
    simpa [er, em, Functor.map_comp] using hr

-- Separate the composite presentation's explicit data from its graph-law proofs.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def compositeInverseImage
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {H : GrothendieckTopology E}
    {F : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf H (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    {S : Sheaf H CommRingCat.{u}}
    (I : InverseImage F A B) (I' : InverseImage G B S) : InverseImage (F ⋙ G) A S := by
  let er := G.mapIso I.ringUnderlying ≪≫ I'.ringUnderlying
  let em : (I.modules ⋙ I'.modules) ⋙ underlying S ≅ underlying A ⋙ (F ⋙ G) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft I.modules I'.moduleUnderlying ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight I.moduleUnderlying G ≪≫ Functor.associator _ _ _
  exact
    { ringUnderlying := er
      modules := I.modules ⋙ I'.modules
      moduleUnderlying := em
      ringAdd := (compositeInverseImageAux I I').ringAdd
      ringMul := (compositeInverseImageAux I I').ringMul
      ringZero := (compositeInverseImageAux I I').ringZero
      ringOne := (compositeInverseImageAux I I').ringOne
      moduleAdd := (compositeInverseImageAux I I').moduleAdd
      moduleZero := (compositeInverseImageAux I I').moduleZero
      moduleSMul := (compositeInverseImageAux I I').moduleSMul }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleComparison
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits F]
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (γ : F ≅ G) (I : InverseImage F A B) (I' : InverseImage G A B)
    (hr : γ.hom.app _ ≫ (inverseRing I').hom = (inverseRing I).hom) :
    inverseModules I ≅ inverseModules I' := by
  let f (M : Modules A) : (inverseModules I).obj M ⟶ (inverseModules I').obj M :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          { toFun := ((CategoryTheory.moduleComparisonApp γ I I' M).hom.app U)
            map_add' := ((CategoryTheory.moduleComparisonApp γ I I' M).hom.app U).hom.map_add
            map_smul' := by
              intro r x
              have h := CategoryTheory.module_compare_smul γ.hom I I' M U r x
              have he : CategoryTheory.compareMap γ.hom I.ringUnderlying I'.ringUnderlying =
                  𝟙 _ := by
                dsimp [CategoryTheory.compareMap]
                rw [hr, Iso.inv_hom_id]
              rw [he] at h
              exact h }
        naturality := by
          intro U V g
          ext x
          exact CategoryTheory.congr_fun
            ((CategoryTheory.moduleComparisonApp γ I I' M).hom.naturality g) x } }
  have hf (M : Modules A) : (underlying B).map (f M) =
      I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫ I'.moduleUnderlying.inv.app M := by
    exact CategoryTheory.moduleComparisonApp_underlying γ I I' M
  let β : inverseModules I ⟶ inverseModules I' :=
    { app := f
      naturality := by
        intro M N g
        apply (underlying B).map_injective
        rw [Functor.map_comp, Functor.map_comp, hf, hf]
        have h := (I.moduleUnderlying ≪≫
          Functor.isoWhiskerLeft (underlying A) γ ≪≫ I'.moduleUnderlying.symm).hom.naturality g
        simpa only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
          NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
          Functor.whiskerLeft_app, Functor.comp_map, Category.assoc] using h }
  have hi (M : Modules A) : IsIso (β.app M) := by
    have h : (underlying B).map (β.app M) =
        I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫ I'.moduleUnderlying.inv.app M := by
      exact CategoryTheory.moduleComparisonApp_underlying γ I I' M
    have : IsIso ((underlying B).map (β.app M)) := by rw [h]; infer_instance
    exact isIso_of_reflects_iso _ (underlying B)
  exact NatIso.ofComponents (fun M ↦ asIso (β.app M)) (fun g ↦ β.naturality g)

set_option backward.isDefEq.respectTransparency false in
private theorem moduleComparison_underlying
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits F]
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (γ : F ≅ G) (I : InverseImage F A B) (I' : InverseImage G A B)
    (hr : γ.hom.app _ ≫ (inverseRing I').hom = (inverseRing I).hom)
    (M : Modules A) :
    (underlying B).map ((moduleComparison γ I I' hr).hom.app M) =
      I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫ I'.moduleUnderlying.inv.app M := by
  unfold moduleComparison
  exact CategoryTheory.moduleComparisonApp_underlying γ I I' M

set_option backward.isDefEq.respectTransparency false in
private theorem moduleComparison_hom_apply
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits F]
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (γ : F ≅ G) (I : InverseImage F A B) (I' : InverseImage G A B)
    (hr : γ.hom.app _ ≫ (inverseRing I').hom = (inverseRing I).hom)
    (M : Modules A) (U : Dᵒᵖ) (x : ((inverseModules I).obj M).val.obj U) :
    ((moduleComparison γ I I' hr).hom.app M).val.app U x =
      ((I'.moduleUnderlying.inv.app M).hom.app U
        ((γ.hom.app ((underlying A).obj M)).hom.app U
          ((I.moduleUnderlying.hom.app M).hom.app U (ULift.up x)))).down := by
  exact congrArg (fun q ↦ (q.hom.app U (ULift.up x)).down)
    (moduleComparison_underlying γ I I' hr M)

-- Use the comparison's underlying and section formulas without unfolding its proof fields.
attribute [local irreducible] moduleComparison

section Action

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {AY BY : Sheaf J CommRingCat.{u}} {AX BX : Sheaf K CommRingCat.{u}}
  {φY : AY ⟶ BY} {φX : AX ⟶ BX}
  {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  (IA : InverseImage L AY AX)
  (IB : InverseImage L BY BX)
  (ring_compat : L.map ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY) ≫
      (inverseRing IB).hom = (inverseRing IA).hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- Compare the two scalar-restriction presentations and their underlying graph operations.
include ring_compat in
/-- The unique restriction/action identification fixed by the underlying inverse images.
Source: Stacks 03D2, blueprint det-prop-scalar-six-pullback (1)
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).
Proof: transport addition and scalar multiplication using the generalized graph equations
of IA and IB. Ring compatibility makes the two restricted actions equal. Their underlying
sheaf isomorphism therefore lifts uniquely to a module isomorphism, naturally in H;
faithfulness of the underlying-sheaf functor gives uniqueness. -/
theorem action_existsUnique (leftExact : PreservesFiniteLimits L) :
    ∃! a : restriction φY ⋙ (inverseModules IA) ≅ (inverseModules IB) ⋙ restriction φX,
      ∀ (H : Modules BY) (U : Dᵒᵖ)
        (x : ((inverseModules IA).obj ((restriction φY).obj H)).val.obj U),
        (a.hom.app H).val.app U x =
          (((inverseUnderlying IB).inv.app H).hom.app U
            (((inverseUnderlying IA).hom.app ((restriction φY).obj H)).hom.app U
              (ULift.up x))).down := by
  classical
  let := leftExact
  let A := unliftInverseImage IA
  let B := unliftInverseImage IB
  let UY : Modules BY ⥤ Sheaf J (Type u) :=
    toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj BY) ⋙
      sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
  let UX : Modules AX ⥤ Sheaf K (Type u) :=
    toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj AX) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})
  let eJ := SheafOfModules.sheafUliftIso J CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eK := SheafOfModules.sheafUliftIso K CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  have hc : A.ringUnderlying.hom ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map φX =
      L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map φY) ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj BY))
            (rfl : L = L)) ≫ B.ringUnderlying.hom := by
    have h := congrArg (fun q ↦ L.map (eJ.inv.app AY) ≫ q ≫ eK.hom.app BX)
      ring_compat
    change (L.map (eJ.inv.app AY) ≫ IA.ringUnderlying.hom ≫ eK.hom.app AX) ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map φX =
        L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map φY) ≫
          𝟙 _ ≫ (L.map (eJ.inv.app BY) ≫ IB.ringUnderlying.hom ≫ eK.hom.app BX)
    simp only [Category.id_comp, Category.assoc]
    rw [← eK.hom.naturality φX]
    rw [← L.map_comp_assoc, eJ.inv.naturality φY, L.map_comp_assoc]
    exact h.symm
  have hex (M : Modules BY) :=
    CategoryTheory.FlatRingedDiagramInput.inverse_change_hom A B φY φX rfl hc M
  let f (M : Modules BY) := (hex M).choose
  have hf (M : Modules BY) : UX.map (f M) =
      A.moduleUnderlying.hom.app ((restriction φY).obj M) ≫ B.moduleUnderlying.inv.app M := by
    exact (hex M).choose_spec
  have hf_section (M : Modules BY) (V : Dᵒᵖ)
      (x : ((inverseModules IA).obj ((restriction φY).obj M)).val.obj V) :
      (f M).val.app V x =
        (((inverseUnderlying IB).inv.app M).hom.app V
          (((inverseUnderlying IA).hom.app ((restriction φY).obj M)).hom.app V
            (ULift.up x))).down := by
    have hraw := hf M
    dsimp only [A, B, unliftInverseImage, Iso.trans_hom, Iso.trans_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app] at hraw
    let e := SheafOfModules.sheafUliftIso J AddCommGrpCat.{u}
      (CategoryTheory.forget AddCommGrpCat.{u})
    let N := (toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj BY)).obj M
    simp only [Category.assoc] at hraw
    change UX.map (f M) = _ ≫ IA.moduleUnderlying.hom.app ((restriction φY).obj M) ≫
      L.map (e.hom.app N) ≫ L.map (e.inv.app N) ≫ IB.moduleUnderlying.inv.app M ≫ _ at hraw
    rw [← L.map_comp_assoc, Iso.hom_inv_id_app] at hraw
    erw [L.map_id, Category.id_comp] at hraw
    have h := congrArg (fun q ↦ q.hom.app V x) hraw
    exact h
  have hf_lifted (M : Modules BY) : (underlying AX).map (f M) =
      IA.moduleUnderlying.hom.app ((restriction φY).obj M) ≫
        IB.moduleUnderlying.inv.app M := by
    ext V x
    exact congrArg ULift.up (hf_section M V x.down)
  have hi (M : Modules BY) : IsIso (f M) := by
    have : IsIso ((underlying AX).map (f M)) := by rw [hf_lifted]; infer_instance
    exact isIso_of_reflects_iso (f M) (underlying AX)
  let β : restriction φY ⋙ inverseModules IA ⟶ inverseModules IB ⋙ restriction φX :=
    { app := f
      naturality := by
        intro M N g
        apply (underlying AX).map_injective
        change (underlying AX).map ((inverseModules IA).map ((restriction φY).map g) ≫ f N) =
          (underlying AX).map (f M ≫ (restriction φX).map ((inverseModules IB).map g))
        rw [Functor.map_comp, Functor.map_comp, hf_lifted, hf_lifted]
        erw [← Category.assoc,
          IA.moduleUnderlying.hom.naturality ((restriction φY).map g),
          Category.assoc, IB.moduleUnderlying.inv.naturality g, Category.assoc]
        rfl }
  let a : restriction φY ⋙ inverseModules IA ≅ inverseModules IB ⋙ restriction φX :=
    NatIso.ofComponents (fun M ↦ asIso (f M)) (fun g ↦ β.naturality g)
  refine ⟨a, hf_section, ?_⟩
  intro a' ha'
  apply Iso.ext
  ext M V x
  exact (ha' M V x).trans (hf_section M V x).symm

/-- The canonical ordinary action identification, chosen from its unique underlying map.
Source: Stacks 03D2, blueprint det-prop-scalar-six-pullback (1)
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
@[irreducible]
noncomputable def a_h (leftExact : PreservesFiniteLimits L) :
    restriction φY ⋙ (inverseModules IA) ≅ (inverseModules IB) ⋙ restriction φX :=
  Classical.choose (action_existsUnique IA IB ring_compat leftExact).exists

private theorem a_h_spec (leftExact : PreservesFiniteLimits L)
    (H : Modules BY) (U : Dᵒᵖ)
    (x : ((inverseModules IA).obj ((restriction φY).obj H)).val.obj U) :
    ((a_h IA IB ring_compat leftExact).hom.app H).val.app U x =
      (((inverseUnderlying IB).inv.app H).hom.app U
        (((inverseUnderlying IA).hom.app ((restriction φY).obj H)).hom.app U
          (ULift.up x))).down := by
  unfold a_h
  exact (Classical.choose_spec
    (action_existsUnique IA IB ring_compat leftExact).exists) H U x

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (Modules AY)] [HasDerivedCategory.{w} (Modules BY)]
  [HasDerivedCategory.{w} (Modules AX)] [HasDerivedCategory.{w} (Modules BX)]
  [(inverseModules IA).Additive] [(inverseModules IB).Additive]
  [PreservesFiniteLimits (inverseModules IA)] [PreservesFiniteColimits (inverseModules IA)]
  [PreservesFiniteLimits (inverseModules IB)] [PreservesFiniteColimits (inverseModules IB)]
  [PreservesFiniteLimits (restriction φY)] [PreservesFiniteColimits (restriction φY)]
  [PreservesFiniteLimits (restriction φX)] [PreservesFiniteColimits (restriction φX)]

/-- Exact localization of the canonical ordinary action identification.
Source: Stacks 06YY, blueprint det-prop-scalar-six-pullback (1)
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
@[irreducible]
noncomputable def aD_h (leftExact : PreservesFiniteLimits L) :
    (restriction φY).mapDerivedCategory ⋙ (inverseModules IA).mapDerivedCategory ≅
      (inverseModules IB).mapDerivedCategory ⋙ (restriction φX).mapDerivedCategory := by
  letI := comp_preservesFiniteLimits (restriction φY) (inverseModules IA)
  letI := comp_preservesFiniteColimits (restriction φY) (inverseModules IA)
  letI := comp_preservesFiniteLimits (inverseModules IB) (restriction φX)
  letI := comp_preservesFiniteColimits (inverseModules IB) (restriction φX)
  exact (Functor.mapDerivedCategoryCompIso (restriction φY) (inverseModules IA)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (a_h IA IB ring_compat leftExact) ≪≫
      Functor.mapDerivedCategoryCompIso (inverseModules IB) (restriction φX)

/-- The specified geometric scalar comparison, as the inverse mate of the canonical action.
Source: blueprint det-prop-scalar-six-pullback (1), Stacks 07A7
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
@[irreducible]
noncomputable def θ_h (leftExact : PreservesFiniteLimits L)
    {TY : DerivedCategory (Modules AY) ⥤ DerivedCategory (Modules BY)}
    {TX : DerivedCategory (Modules AX) ⥤ DerivedCategory (Modules BX)}
    (dY : TY ⊣ (restriction φY).mapDerivedCategory)
    (dX : TX ⊣ (restriction φX).mapDerivedCategory) :
    (inverseModules IA).mapDerivedCategory ⋙ TX ⟶ TY ⋙ (inverseModules IB).mapDerivedCategory :=
  mate dY dX (aD_h IA IB ring_compat leftExact).hom

end Action

section

-- Tensor arguments use the comparison API; keep the localized monoidal structure closed.
attribute [local irreducible] SheafOfModules.monoidalCategory
  DerivedCategory.Q DerivedCategory.Qh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_adjunction_exists
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ) :
    ∃ (a : m.E ⊣ restriction φ) (d : m.T ⊣ (restriction φ).mapDerivedCategory),
      AdjunctionNormalized m a d ∧
      ∀ P : CochainComplex (Modules A) ℤ,
        d.unit.app (DerivedCategory.Q.obj P) ≫
          (restriction φ).mapDerivedCategory.map (m.ε.app P) ≫
          (restriction φ).mapDerivedCategoryFactors.hom.app
            ((m.E.mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  classical
  obtain ⟨εh, huni, hεP⟩ :=
    exists_homotopy_leftDerived_comparison m.E m.T m.ε m.universal
  obtain ⟨_, _, ho⟩ := sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, ha⟩ := ho m.E m.obj_eq m.map_eq
  obtain ⟨d, hd⟩ := sheafRingDerivedHomComparison φ m.E m.obj_eq m.map_eq a m.T εh huni
  have ht := adjunction_cochain_transpose m.E (restriction φ) a m.T m.ε εh hεP d hd
  have hunit (P : CochainComplex (Modules A) ℤ) :
      d.unit.app (DerivedCategory.Q.obj P) ≫
        (restriction φ).mapDerivedCategory.map (m.ε.app P) ≫
        (restriction φ).mapDerivedCategoryFactors.hom.app
          ((m.E.mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) := by
    have h := ht P ((m.E.mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
    simp only [Adjunction.homEquiv_unit] at h
    erw [CategoryTheory.Functor.map_id, Category.comp_id,
      CategoryTheory.Functor.map_id, Category.comp_id] at h
    rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  refine ⟨a, d, ⟨?_, fun P _ _ ↦ hunit P⟩, hunit⟩
  intro M U x
  have h := ha M (m.E.obj M) (eqToHom (m.obj_eq M).symm) U x
  dsimp only [pure]
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverse_map_section
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)} (I : InverseImage L A B)
    {M N : Modules A} (f : M ⟶ N) (Z : Sheaf J (Type u))
    (x : Z ⟶ (underlying A).obj M) (U : Dᵒᵖ) (t : (L.obj Z).obj.obj U) :
    ((inverseModules I).map f).val.app U
        (((inverseUnderlying I).inv.app M).hom.app U ((L.map x).hom.app U t)).down =
      (((inverseUnderlying I).inv.app N).hom.app U
        ((L.map (x ≫ (underlying A).map f)).hom.app U t)).down := by
  have h := congrArg (fun q ↦ (q.hom.app U ((L.map x).hom.app U t)).down)
    ((inverseUnderlying I).inv.naturality f)
  change (((inverseUnderlying I).inv.app N).hom.app U
      ((L.map ((underlying A).map f)).hom.app U ((L.map x).hom.app U t))).down =
    ((inverseModules I).map f).val.app U
      (((inverseUnderlying I).inv.app M).hom.app U ((L.map x).hom.app U t)).down at h
  erw [L.map_comp]
  change ((inverseModules I).map f).val.app U
      (((inverseUnderlying I).inv.app M).hom.app U ((L.map x).hom.app U t)).down =
    (((inverseUnderlying I).inv.app N).hom.app U
      ((L.map ((underlying A).map f)).hom.app U ((L.map x).hom.app U t))).down
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem action_section
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {AY BY : Sheaf J CommRingCat.{u}} {AX BX : Sheaf K CommRingCat.{u}}
    {φY : AY ⟶ BY} {φX : AX ⟶ BX}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)} [PreservesFiniteLimits L]
    (IA : InverseImage L AY AX) (IB : InverseImage L BY BX)
    (hc : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY) ≫
        (inverseRing IB).hom = (inverseRing IA).hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)
    (M : Modules BY) (Z : Sheaf J (Type u)) (x : Z ⟶ (underlying BY).obj M)
    (U : Dᵒᵖ) (t : (L.obj Z).obj.obj U) :
    ((a_h IA IB hc inferInstance).hom.app M).val.app U
        (((inverseUnderlying IA).inv.app ((restriction φY).obj M)).hom.app U
          ((L.map x).hom.app U t)).down =
      (((inverseUnderlying IB).inv.app M).hom.app U ((L.map x).hom.app U t)).down := by
  rw [a_h_spec]
  have h := congrArg (fun q ↦ q.hom.app U ((L.map x).hom.app U t))
    ((inverseUnderlying IA).inv_hom_id_app ((restriction φY).obj M))
  have h' :
      (((inverseUnderlying IA).hom.app ((restriction φY).obj M)).hom.app U
        (((inverseUnderlying IA).inv.app ((restriction φY).obj M)).hom.app U
          ((L.map x).hom.app U t))) = (L.map x).hom.app U t := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      types_comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
      types_id_apply] using h
  exact congrArg (fun y ↦ (((inverseUnderlying IB).inv.app M).hom.app U y).down) h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverse_unit_comparison
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u)) (I : InverseImage L A B) :
    ∃ e : (inverseModules I).obj (unit ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj A)) ≅
        unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B),
      ∀ U x, e.hom.val.app U x =
        ((inverseRing I).hom.hom.app U
          (((inverseUnderlying I).hom.app
            (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))).hom.app U
              (ULift.up x))).down := by
  let I₀ := unliftInverseImage I
  obtain ⟨e, he⟩ := SheafOfModules.inverseImage_unit_iso A B L I₀
  have h : (RingedTensor.underlying B).map e.inv =
      I₀.moduleUnderlying.hom.app (unit (RingedTensor.ringSheaf A)) ≫ I₀.ringUnderlying.hom := by
    apply (cancel_epi ((RingedTensor.underlying B).map e.hom)).mp
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, he]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id]
  refine ⟨e.symm, ?_⟩
  intro U x
  dsimp only [I₀, unliftInverseImage, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app] at h
  have hc :
      (sheafUliftIso J AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})).hom.app
          ((toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)).obj
            (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))) ≫
        (sheafUliftIso J CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})).inv.app A =
          𝟙 _ := by
    ext V z
    rfl
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc] at h
  erw [hc, L.map_id, Category.id_comp] at h
  have hx := congrArg (fun q ↦ q.hom.app U x) h
  convert hx using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverse_tensor_comparison_exists
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) [PreservesFiniteLimits L] (I : InverseImage L A B) :
    ∃ e : ∀ M N : Modules A,
        (inverseModules I).obj ((monoidalCategory A).tensorObj M N) ≅
          (monoidalCategory B).tensorObj ((inverseModules I).obj M) ((inverseModules I).obj N),
      ∀ (M N : Modules A) (Z : Sheaf J (Type u))
        (x : Z ⟶ (underlying A).obj M) (y : Z ⟶ (underlying A).obj N)
        (z : Z ⟶ (underlying A).obj ((monoidalCategory A).tensorObj M N)),
        (∀ V t, (z.hom.app V t).down =
          RingedTensor.pure A M N V (x.hom.app V t).down (y.hom.app V t).down) →
        ∀ V t, (e M N).hom.val.app V
          (((inverseUnderlying I).inv.app ((monoidalCategory A).tensorObj M N)).hom.app V
            ((L.map z).hom.app V t)).down =
          RingedTensor.pure B _ _ V
            (((inverseUnderlying I).inv.app M).hom.app V ((L.map x).hom.app V t)).down
            (((inverseUnderlying I).inv.app N).hom.app V ((L.map y).hom.app V t)).down := by
  obtain ⟨e, _, he⟩ := RingedTensor.exists_inverseImageTensorComparison
    A B L (unliftInverseImage I) R adj
  refine ⟨e, ?_⟩
  intro M N Z x y z hz V t
  let eJ := Functor.isoWhiskerLeft (toSheaf ((sheafCompose J
    (forget₂ CommRingCat RingCat)).obj A)) <|
      sheafUliftIso J AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  have hq (Q : Modules A) (q : Z ⟶ (underlying A).obj Q) :
      ((L.map (q ≫ eJ.hom.app Q) ≫
        (unliftInverseImage I).moduleUnderlying.inv.app Q).hom.app V t) =
      (((inverseUnderlying I).inv.app Q).hom.app V ((L.map q).hom.app V t)).down := by
    change ((L.map (q ≫ eJ.hom.app Q) ≫ L.map (eJ.inv.app Q) ≫
      (inverseUnderlying I).inv.app Q).hom.app V t).down = _
    rw [← L.map_comp_assoc]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply]
    rfl
  have h := he M N Z (x ≫ eJ.hom.app M) (y ≫ eJ.hom.app N)
    (z ≫ eJ.hom.app _) hz V t
  simp only [hq] at h
  dsimp only [unliftInverseImage, inverseModules] at h ⊢
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverse_tensor_hom_ext
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) [PreservesFiniteLimits L] (I : InverseImage L A B)
    (M N : Modules A) {H : Modules B}
    (f g : (inverseModules I).obj ((monoidalCategory A).tensorObj M N) ⟶ H)
    (h : ∀ (Z : Sheaf J (Type u))
      (x : Z ⟶ (underlying A).obj M) (y : Z ⟶ (underlying A).obj N)
      (z : Z ⟶ (underlying A).obj ((monoidalCategory A).tensorObj M N)),
      (∀ V t, (z.hom.app V t).down =
        RingedTensor.pure A M N V (x.hom.app V t).down (y.hom.app V t).down) →
      ∀ U t, f.val.app U
        (((inverseUnderlying I).inv.app ((monoidalCategory A).tensorObj M N)).hom.app U
          ((L.map z).hom.app U t)).down =
      g.val.app U
        (((inverseUnderlying I).inv.app ((monoidalCategory A).tensorObj M N)).hom.app U
          ((L.map z).hom.app U t)).down) : f = g := by
  obtain ⟨e, he⟩ := inverse_tensor_comparison_exists L R adj I
  apply (cancel_epi (e M N).inv).mp
  apply RingedTensor.pure_hom_ext B
  intro U m n
  let X := (underlying A).obj M
  let Y := (underlying A).obj N
  let Z := (CategoryTheory.MonoidalCategory.tensorObj X Y)
  let x : Z ⟶ X := CartesianMonoidalCategory.fst X Y
  let y : Z ⟶ Y := CartesianMonoidalCategory.snd X Y
  let z : Z ⟶ (underlying A).obj ((monoidalCategory A).tensorObj M N) :=
    ⟨{ app := fun V ↦ ↾(fun p ↦ ULift.up
          (RingedTensor.pure A M N V p.1.down p.2.down))
       naturality := by
         intro V W i
         ext p
         exact congrArg ULift.up (RingedTensor.pure_restrict A M N i p.1.down p.2.down).symm }⟩
  let t := CategoryTheory.FlatRingedDiagramInput.pairPreimage L X Y U
    (((inverseUnderlying I).hom.app M).hom.app U (ULift.up m))
    (((inverseUnderlying I).hom.app N).hom.app U (ULift.up n))
  have hm : (((inverseUnderlying I).inv.app M).hom.app U
      ((L.map x).hom.app U t)).down = m := by
    rw [CategoryTheory.FlatRingedDiagramInput.pairPreimage_fst]
    exact congrArg (fun q ↦ (q.hom.app U (ULift.up m)).down)
      ((inverseUnderlying I).hom_inv_id_app M)
  have hn : (((inverseUnderlying I).inv.app N).hom.app U
      ((L.map y).hom.app U t)).down = n := by
    rw [CategoryTheory.FlatRingedDiagramInput.pairPreimage_snd]
    exact congrArg (fun q ↦ (q.hom.app U (ULift.up n)).down)
      ((inverseUnderlying I).hom_inv_id_app N)
  have hz : ∀ V p, (z.hom.app V p).down =
      RingedTensor.pure A M N V (x.hom.app V p).down (y.hom.app V p).down :=
    fun _ _ ↦ rfl
  have he' := he M N Z x y z hz U t
  rw [hm, hn] at he'
  let v := (((inverseUnderlying I).inv.app ((monoidalCategory A).tensorObj M N)).hom.app U
    ((L.map z).hom.app U t)).down
  have hv : (e M N).inv.val.app U (RingedTensor.pure B _ _ U m n) = v := by
    rw [← he']
    exact congrArg (fun q ↦ q.val.app U v) ((e M N).hom_inv_id)
  change f.val.app U ((e M N).inv.val.app U _) =
    g.val.app U ((e M N).inv.val.app U _)
  rw [hv]
  exact h Z x y z hz U t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem model_tensor_presentation
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ) (M : Modules A) :
    ∃ e : (monoidalCategory A).tensorObj
        ((restriction φ).obj (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))) M ≅
        (restriction φ).obj (m.E.obj M),
      ∀ U b x, e.hom.val.app U (RingedTensor.pure A _ M U b x) = pure m M U b x := by
  obtain ⟨e, he⟩ := exists_extensionTensorComparison φ M
  refine ⟨e ≪≫ (restriction φ).mapIso (eqToIso (m.obj_eq M).symm), ?_⟩
  intro U b x
  change (eqToHom (m.obj_eq M).symm).val.app U
      (e.hom.val.app U (RingedTensor.pure A _ M U b x)) = _
  rw [show e.hom.val.app U (RingedTensor.pure A _ M U b x) =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (b ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x) from he U b x]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pure_smul_one
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (M : Modules A) (U : Cᵒᵖ) (b : B.obj.obj U) (x : M.val.obj U) :
    pure m M U b x = b • pure m M U 1 x := by
  dsimp only [pure]
  have h : b ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x =
      b • ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  let η := (PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
      (changeOfRingsPresheaf.{u, u, u} φ M)
  change (eqToHom (m.obj_eq M).symm).val.app U
      ((η.app U) (b ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x)) =
    b • (eqToHom (m.obj_eq M).symm).val.app U
      ((η.app U) ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x))
  rw [h]
  erw [(η.app U).hom.map_smul, ((eqToHom (m.obj_eq M).symm).val.app U).hom.map_smul]

-- Use the section and localization APIs without expanding their constructions.
attribute [local irreducible] pure RingedTensor.pure
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Compare the tensor presentation and the mate through their section transport formulas.
private theorem ordinary_comparison_exists
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {AY BY : Sheaf J CommRingCat.{u}} {AX BX : Sheaf K CommRingCat.{u}}
    (φY : AY ⟶ BY) (φX : AX ⟶ BX)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) [PreservesFiniteLimits L]
    (IA : InverseImage L AY AX)
    (IB : InverseImage L BY BX)
    (ring_compat : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY) ≫
        (inverseRing IB).hom = (inverseRing IA).hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)
    [HasDerivedCategory.{w} (Modules AY)] [HasDerivedCategory.{w} (Modules BY)]
    [HasDerivedCategory.{w} (Modules AX)] [HasDerivedCategory.{w} (Modules BX)]
    (mY : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φY)
    (mX : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φX)
    (aY : mY.E ⊣ restriction φY) (aX : mX.E ⊣ restriction φX)
    (haY : ∀ M U x, (aY.unit.app M).val.app U x = pure mY M U 1 x)
    (haX : ∀ M U x, (aX.unit.app M).val.app U x = pure mX M U 1 x) :
    ∃ χ : mY.E ⋙ (inverseModules IB) ≅ (inverseModules IA) ⋙ mX.E,
    (∀ (M : Modules AY) (Z : Sheaf J (Type u))
      (b : Z ⟶ (sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj BY)
      (x : Z ⟶ (underlying AY).obj M)
      (z : Z ⟶ (underlying BY).obj (mY.E.obj M)),
      (∀ (U : Cᵒᵖ) (t : Z.obj.obj U),
        @id ((mY.E.obj M).val.obj U) (z.hom.app U t).down =
          pure mY M U (@id (BY.obj.obj U) (b.hom.app U t).down)
            (@id (M.val.obj U) (x.hom.app U t).down)) →
      ∀ (U : Dᵒᵖ) (t : (L.obj Z).obj.obj U),
        (χ.hom.app M).val.app U
          (((inverseUnderlying IB).inv.app (mY.E.obj M)).hom.app U ((L.map z).hom.app U t)).down =
        pure mX ((inverseModules IA).obj M) U
          (@id (BX.obj.obj U) ((L.map b ≫ (inverseRing IB).hom).hom.app U t).down)
          (((inverseUnderlying IA).inv.app M).hom.app U ((L.map x).hom.app U t)).down) ∧
    (∀ M : Modules AY,
      (inverseModules IA).map (aY.unit.app M) ≫
        (a_h IA IB ring_compat inferInstance).hom.app (mY.E.obj M) ≫
          (restriction φX).map (χ.hom.app M) = aX.unit.app ((inverseModules IA).obj M)) := by
  classical
  obtain ⟨χ, hpure⟩ :
      ∃ χ : mY.E ⋙ (inverseModules IB) ≅ (inverseModules IA) ⋙ mX.E,
    (∀ (M : Modules AY) (Z : Sheaf J (Type u))
      (b : Z ⟶ (sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj BY)
      (x : Z ⟶ (underlying AY).obj M)
      (z : Z ⟶ (underlying BY).obj (mY.E.obj M)),
      (∀ (U : Cᵒᵖ) (t : Z.obj.obj U),
        @id ((mY.E.obj M).val.obj U) (z.hom.app U t).down =
          pure mY M U (@id (BY.obj.obj U) (b.hom.app U t).down)
            (@id (M.val.obj U) (x.hom.app U t).down)) →
      ∀ (U : Dᵒᵖ) (t : (L.obj Z).obj.obj U),
        (χ.hom.app M).val.app U
          (((inverseUnderlying IB).inv.app (mY.E.obj M)).hom.app U ((L.map z).hom.app U t)).down =
        pure mX ((inverseModules IA).obj M) U
          (@id (BX.obj.obj U) ((L.map b ≫ (inverseRing IB).hom).hom.app U t).down)
          (((inverseUnderlying IA).inv.app M).hom.app U ((L.map x).hom.app U t)).down) := by
    let s := a_h IA IB ring_compat inferInstance
    let UY : Modules BY := unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj BY)
    let UX : Modules BX := unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj BX)
    let VY := (restriction φY).obj UY
    let VX := (restriction φX).obj UX
    obtain ⟨j, hj⟩ := inverse_unit_comparison L IB
    let eB : (inverseModules IA).obj VY ≅ VX :=
      s.app UY ≪≫ (restriction φX).mapIso j
    choose eY heY using model_tensor_presentation mY
    choose eX heX using model_tensor_presentation mX
    obtain ⟨et, het⟩ := inverse_tensor_comparison_exists L R adj IA
    let etB (M : Modules AY) :
        (monoidalCategory AX).tensorObj ((inverseModules IA).obj VY)
          ((inverseModules IA).obj M) ≅
        (monoidalCategory AX).tensorObj VX ((inverseModules IA).obj M) :=
      @MonoidalCategory.tensorIso (Modules AX) _ (monoidalCategory AX)
        _ _ _ _ eB (Iso.refl _)
    let δ (M : Modules AY) : (restriction φX).obj ((inverseModules IB).obj (mY.E.obj M)) ≅
        (restriction φX).obj (mX.E.obj ((inverseModules IA).obj M)) :=
      (s.app (mY.E.obj M)).symm ≪≫ (inverseModules IA).mapIso (eY M).symm ≪≫
        et VY M ≪≫ etB M ≪≫ eX ((inverseModules IA).obj M)
    have hδ : ∀ (M : Modules AY) (Z : Sheaf J (Type u))
      (b : Z ⟶ (sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj BY)
      (x : Z ⟶ (underlying AY).obj M)
      (z : Z ⟶ (underlying BY).obj (mY.E.obj M)),
      (∀ (U : Cᵒᵖ) (t : Z.obj.obj U),
        @id ((mY.E.obj M).val.obj U) (z.hom.app U t).down =
          pure mY M U (@id (BY.obj.obj U) (b.hom.app U t).down)
            (@id (M.val.obj U) (x.hom.app U t).down)) →
      ∀ (U : Dᵒᵖ) (t : (L.obj Z).obj.obj U),
        ((δ M).hom).val.app U
          (((inverseUnderlying IB).inv.app (mY.E.obj M)).hom.app U ((L.map z).hom.app U t)).down =
        pure mX ((inverseModules IA).obj M) U
          (@id (BX.obj.obj U) ((L.map b ≫ (inverseRing IB).hom).hom.app U t).down)
          (((inverseUnderlying IA).inv.app M).hom.app U ((L.map x).hom.app U t)).down := by
      intro M Z b x z hz U t
      let z' : Z ⟶ (underlying AY).obj ((monoidalCategory AY).tensorObj VY M) :=
        z ≫ (underlying AY).map (eY M).inv
      have hz' (V : Cᵒᵖ) (p : Z.obj.obj V) : (z'.hom.app V p).down =
          RingedTensor.pure AY VY M V (b.hom.app V p).down (x.hom.app V p).down := by
        change (eY M).inv.val.app V (z.hom.app V p).down = _
        let g : (mY.E.obj M).val.obj V →
            ((monoidalCategory AY).tensorObj VY M).val.obj V :=
          fun q ↦ (eY M).inv.val.app V q
        have h0 := congrArg g (hz V p)
        have h1 := congrArg g (heY M V (b.hom.app V p).down (x.hom.app V p).down)
        have h2 := congrArg (fun q ↦ q.val.app V
          (RingedTensor.pure AY VY M V (b.hom.app V p).down (x.hom.app V p).down))
          ((eY M).hom_inv_id)
        exact h0.trans (h1.symm.trans h2)
      let v := (((inverseUnderlying IA).inv.app ((monoidalCategory AY).tensorObj VY M)).hom.app U
        ((L.map z').hom.app U t)).down
      have hvY : ((inverseModules IA).map (eY M).hom).val.app U v =
          (((inverseUnderlying IA).inv.app ((restriction φY).obj (mY.E.obj M))).hom.app U
            ((L.map z).hom.app U t)).down := by
        rw [inverse_map_section]
        have hzid : z' ≫ (underlying AY).map (eY M).hom = z := by
          dsimp only [z']
          rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
            CategoryTheory.Functor.map_id]
          erw [Category.comp_id]
        rw [hzid]
        rfl
      have hin : (s.hom.app (mY.E.obj M)).val.app U
          (((inverseModules IA).map (eY M).hom).val.app U v) =
          (((inverseUnderlying IB).inv.app (mY.E.obj M)).hom.app U
            ((L.map z).hom.app U t)).down := by
        rw [hvY]
        exact action_section IA IB ring_compat _ Z z U t
      have hv : ((inverseModules IA).map (eY M).inv).val.app U
          ((s.inv.app (mY.E.obj M)).val.app U
            ((((inverseUnderlying IB).inv.app (mY.E.obj M)).hom.app U
              ((L.map z).hom.app U t)).down)) = v := by
        have h := congrArg (fun q ↦ q.val.app U v)
          (((inverseModules IA).mapIso (eY M) ≪≫ s.app (mY.E.obj M)).hom_inv_id)
        change ((inverseModules IA).map (eY M).inv).val.app U
          ((s.inv.app (mY.E.obj M)).val.app U
            ((s.hom.app (mY.E.obj M)).val.app U
              (((inverseModules IA).map (eY M).hom).val.app U v))) = v at h
        rw [hin] at h
        exact h
      have hb : eB.hom.val.app U
          ((((inverseUnderlying IA).inv.app VY).hom.app U
            ((L.map b).hom.app U t)).down) =
          ((L.map b ≫ (inverseRing IB).hom).hom.app U t).down := by
        change j.hom.val.app U ((s.hom.app UY).val.app U _) = _
        erw [action_section, hj]
        have h := congrArg (fun q ↦ q.hom.app U ((L.map b).hom.app U t))
          ((inverseUnderlying IB).inv_hom_id_app UY)
        erw [h]
        rfl
      change (eX ((inverseModules IA).obj M)).hom.val.app U
        ((etB M).hom.val.app U ((et VY M).hom.val.app U
          (((inverseModules IA).map (eY M).inv).val.app U
            ((s.inv.app (mY.E.obj M)).val.app U _)))) = _
      rw [hv]
      erw [het VY M Z b x z' hz' U t]
      change (eX ((inverseModules IA).obj M)).hom.val.app U
        (((monoidalCategory AX).tensorHom eB.hom (𝟙 _)).val.app U _) = _
      erw [RingedTensor.pure_map, heX]
      change pure mX ((inverseModules IA).obj M) U
        (eB.hom.val.app U ((((inverseUnderlying IA).inv.app VY).hom.app U
          ((L.map b).hom.app U t)).down))
        (((inverseUnderlying IA).inv.app M).hom.app U ((L.map x).hom.app U t)).down = _
      erw [hb]
      rfl
    -- Identify the comparison's inverse using the ordinary adjunction mate.
    clear_value δ
    let β : inverseModules IA ⋙ mX.E ⟶ mY.E ⋙ inverseModules IB := mate aY aX s.hom
    have hβ (M : Modules AY) :
        aX.unit.app ((inverseModules IA).obj M) ≫ (restriction φX).map (β.app M) =
          (inverseModules IA).map (aY.unit.app M) ≫ s.hom.app (mY.E.obj M) :=
      (unit_mateEquiv_symm aY aX (TwoSquare.mk _ _ _ _ s.hom) M).symm
    clear_value β
    have hβpure (M : Modules AY) (U : Dᵒᵖ) (b : BX.obj.obj U)
        (x : ((inverseModules IA).obj M).val.obj U) :
        (β.app M).val.app U (pure mX ((inverseModules IA).obj M) U b x) =
          b • @id (((inverseModules IB).obj (mY.E.obj M)).val.obj U)
            ((s.hom.app (mY.E.obj M)).val.app U
              (((inverseModules IA).map (aY.unit.app M)).val.app U x)) := by
      rw [pure_smul_one, ← haX]
      erw [map_smul]
      exact congrArg (fun y : ((inverseModules IB).obj (mY.E.obj M)).val.obj U ↦ b • y)
        (congrArg (fun f ↦ f.val.app U x) (hβ M))
    have hβgraph (M : Modules AY) (Z : Sheaf J (Type u))
        (b : Z ⟶ (sheafCompose J
          (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj BY)
        (x : Z ⟶ (underlying AY).obj M)
        (z : Z ⟶ (underlying BY).obj (mY.E.obj M))
        (hz : ∀ V t, (z.hom.app V t).down =
          pure mY M V (b.hom.app V t).down (x.hom.app V t).down)
        (U : Dᵒᵖ) (t : (L.obj Z).obj.obj U) :
        (β.app M).val.app U
          (pure mX ((inverseModules IA).obj M) U
            ((L.map b ≫ (inverseRing IB).hom).hom.app U t).down
            (((inverseUnderlying IA).inv.app M).hom.app U ((L.map x).hom.app U t)).down) =
          (((inverseUnderlying IB).inv.app (mY.E.obj M)).hom.app U
            ((L.map z).hom.app U t)).down := by
      clear hδ δ etB het et heX eX heY eY eB hj j VX VY UX UY
      rw [hβpure]
      erw [inverse_map_section, action_section]
      apply Eq.symm
      apply IB.moduleSMul (mY.E.obj M) Z b
        (x ≫ (underlying AY).map (aY.unit.app M)) z
      intro V t
      rw [hz, pure_smul_one, ← haY]
      rfl
    have heq (M : Modules AY) : (restriction φX).map (β.app M) = (δ M).inv := by
      apply (cancel_epi (δ M).hom).mp
      rw [Iso.hom_inv_id]
      apply (cancel_epi (s.hom.app (mY.E.obj M))).mp
      apply (cancel_epi ((inverseModules IA).map (eY M).hom)).mp
      erw [Category.comp_id]
      apply inverse_tensor_hom_ext L R adj IA VY M
      intro Z b x z hz U t
      let zY : Z ⟶ (underlying BY).obj (mY.E.obj M) :=
        z ≫ (underlying AY).map (eY M).hom
      have hzY (V : Cᵒᵖ) (t : Z.obj.obj V) :
          (zY.hom.app V t).down =
            pure mY M V (b.hom.app V t).down (x.hom.app V t).down := by
        change (eY M).hom.val.app V (z.hom.app V t).down = _
        rw [hz, heY]
      have hin : ((inverseModules IA).map (eY M).hom ≫
          s.hom.app (mY.E.obj M)).val.app U
          (((inverseUnderlying IA).inv.app ((monoidalCategory AY).tensorObj VY M)).hom.app U
            ((L.map z).hom.app U t)).down =
          (((inverseUnderlying IB).inv.app (mY.E.obj M)).hom.app U
            ((L.map zY).hom.app U t)).down := by
        change (s.hom.app (mY.E.obj M)).val.app U
          (((inverseModules IA).map (eY M).hom).val.app U _) = _
        rw [inverse_map_section]
        exact action_section IA IB ring_compat _ Z zY U t
      change (β.app M).val.app U ((δ M).hom.val.app U
        (((inverseModules IA).map (eY M).hom ≫ s.hom.app (mY.E.obj M)).val.app U _)) = _
      rw [hin, hδ M Z b x zY hzY U t]
      erw [hin]
      exact hβgraph M Z b x zY hzY U t
    have hi (M : Modules AY) : IsIso (β.app M) := by
      have h : IsIso ((restriction φX).map (β.app M)) := by rw [heq]; infer_instance
      have : IsIso ((underlying BX).map (β.app M)) := by
        change IsIso ((underlying AX).map ((restriction φX).map (β.app M)))
        infer_instance
      exact isIso_of_reflects_iso _ (underlying BX)
    have : IsIso β := NatIso.isIso_of_isIso_app β
    let χ := (asIso β).symm
    refine ⟨χ, ?_⟩
    have hc (M : Modules AY) : (restriction φX).map (χ.hom.app M) = (δ M).hom := by
      apply (cancel_epi ((restriction φX).map (β.app M))).mp
      calc
        _ = (restriction φX).map (β.app M ≫ χ.hom.app M) :=
          ((restriction φX).map_comp _ _).symm
        _ = 𝟙 _ := by
          rw [show β.app M ≫ χ.hom.app M = 𝟙 _ from (asIso β).hom_inv_id_app M,
            CategoryTheory.Functor.map_id]
        _ = (restriction φX).map (β.app M) ≫ (δ M).hom := by
          rw [heq, Iso.inv_hom_id]
    intro M Z b x z hz U t
    have h := hδ M Z b x z hz U t
    have hc' := congrArg (fun f ↦ f.val.app U
      ((((inverseUnderlying IB).inv.app (mY.E.obj M)).hom.app U
        ((L.map z).hom.app U t)).down)) (hc M)
    exact hc'.trans h
  -- Specialize the generalized pure-section formula at coefficient one.
  refine ⟨χ, hpure, ?_⟩
  intro M
  ext U x
  let Z := (underlying AY).obj M
  let b : Z ⟶ (sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj BY :=
    ⟨{ app := fun V ↦ ↾(fun _ ↦ ULift.up (1 : BY.obj.obj V))
       naturality := by
         intro V W f
         ext t
         exact congrArg ULift.up (map_one (BY.obj.map f).hom).symm }⟩
  let z : Z ⟶ (underlying BY).obj (mY.E.obj M) :=
    (underlying AY).map (aY.unit.app M)
  let t := ((inverseUnderlying IA).hom.app M).hom.app U (ULift.up x)
  have hz (V : Cᵒᵖ) (t : Z.obj.obj V) : (z.hom.app V t).down =
      pure mY M V (b.hom.app V t).down t.down := haY M V t.down
  have h := hpure M Z b (𝟙 Z) z hz U t
  have hb : ((L.map b ≫ (inverseRing IB).hom).hom.app U t).down = 1 :=
    IB.ringOne Z b (fun _ _ ↦ rfl) U t
  have hx : (((inverseUnderlying IA).inv.app M).hom.app U
      ((L.map (𝟙 Z)).hom.app U t)).down = x := by
    erw [L.map_id]
    exact congrArg (fun f ↦ (f.hom.app U (ULift.up x)).down)
      ((inverseUnderlying IA).hom_inv_id_app M)
  have hn : (((inverseUnderlying IA).hom.app ((restriction φY).obj (mY.E.obj M))).hom.app U
        (ULift.up (((inverseModules IA).map (aY.unit.app M)).val.app U x))) =
      (L.map z).hom.app U t := by
    exact congrArg (fun f ↦ f.hom.app U (ULift.up x))
      ((inverseUnderlying IA).hom.naturality (aY.unit.app M))
  change (χ.hom.app M).val.app U
      (((a_h IA IB ring_compat inferInstance).hom.app (mY.E.obj M)).val.app U
        (((inverseModules IA).map (aY.unit.app M)).val.app U x)) =
    (aX.unit.app ((inverseModules IA).obj M)).val.app U x
  rw [a_h_spec, hn, haX]
  rw [hb, hx] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Normalize four exact functors and their cochain comparison isomorphisms.
/-- The balanced comparison, its ordinary unit normalization, and its equality with the
specified scalar-adjunction mate on every flat-term K-flat representative. The last
isomorphism assertion concerns the entire unbounded derived category.

The two algebraic inverse images use the same geometric inverse image. The ring equation
says exactly that φX is the inverse image of φY under the displayed ring identifications.
The action isomorphism is fixed on underlying sheaves by moduleUnderlying. The derived
action is fixed by exact localization, not chosen freely. The pure-tensor equation is the
balanced-coequalizer characterization, tested on all generalized pairings before and
after inverse image; it is not a sectionwise-evaluation assumption about inverse image.
All exactness structures below are conclusions, not flatness assumptions on φY or φX.

Source: blueprint main-20261015 det-prop-scalar-six-pullback (1); Stacks 03EL, 04JC,
0G7E, 06YY, 07A6 and 06YS
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).

Proof:
1. Geometric inverse image is additive and exact with transported actions
(lem-trf-geometric-inverse-image-exact). Exact localization gives its representative
comparisons (lem-weil-pbc-exact-functor-derived-factorization). Restricting the transported
action is the same as transporting the restricted action, giving a and then aD.
2. Present restricted scalar extension as the tensor product with the new ring. Apply
the algebraic inverse-image tensor comparison (03EL) and its normalized unit comparison.
Together with the action square these give the restricted comparison δ. The ordinary
adjunction mate β has the prescribed formula on generalized pure tensors, by its unit
square and B-linearity. Tensor extensionality identifies restricted β with δ inverse;
reflection of isomorphisms makes β invertible. Its inverse χ has δ's pure formula.
At coefficient 1 this formula gives the ordinary unit equation.
3. Inverse image preserves flat-term K-flat complexes
(lem-weil-pbc-ringed-pullback-preserves-kflat). Thus both universal change-of-rings
counits are invertible on these representatives (lem-pur-derived-change-of-rings).
4. Descend the cochain comparison to the homotopy category and apply the derived Hom
comparison and cochain-adjunction compatibility. Transposing the identity gives the
normalized derived units on every complex. The ordinary unit equation then identifies
the mate's representative by the generic mate_computes calculation of
lem-sfb-derived-cokernel-adjoint-exchange. Canceling Q(χ) gives exactly the displayed
representative equality with the prescribed cochain counits.
5. Resolve any unbounded object by a flat-term K-flat complex (lem-pc-kflat-resolution).
The representative equality makes the mate invertible there. Naturality along the
localized resolution, which is an isomorphism, proves invertibility at every object.
6. The companion geometric composition and identity statements use the underlying-sheaf
identifications and exact localization. The transported action squares paste, and
lem-weil-pbc-mate-pasting gives their specified mates. No flatness or boundedness is used. -/
theorem kflat_scalar_comparison_normalization
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {AY BY : Sheaf J CommRingCat.{u}} {AX BX : Sheaf K CommRingCat.{u}}
    (φY : AY ⟶ BY) (φX : AX ⟶ BX)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) [PreservesFiniteLimits L]
    (IA : InverseImage L AY AX)
    (IB : InverseImage L BY BX)
    (ring_compat : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY) ≫
        (inverseRing IB).hom = (inverseRing IA).hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)
    [HasDerivedCategory.{w} (Modules AY)] [HasDerivedCategory.{w} (Modules BY)]
    [HasDerivedCategory.{w} (Modules AX)] [HasDerivedCategory.{w} (Modules BX)]
    (mY : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φY)
    (mX : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φX) :
    ∃ (_ : (inverseModules IA).Additive) (_ : (inverseModules IB).Additive)
      (_ : PreservesFiniteLimits (inverseModules IA))
      (_ : PreservesFiniteColimits (inverseModules IA))
      (_ : PreservesFiniteLimits (inverseModules IB))
      (_ : PreservesFiniteColimits (inverseModules IB))
      (_ : PreservesFiniteLimits (restriction φY))
      (_ : PreservesFiniteColimits (restriction φY))
      (_ : PreservesFiniteLimits (restriction φX))
      (_ : PreservesFiniteColimits (restriction φX)),
    ∃ (aY : mY.E ⊣ restriction φY) (aX : mX.E ⊣ restriction φX)
      (dY : mY.T ⊣ (restriction φY).mapDerivedCategory)
      (dX : mX.T ⊣ (restriction φX).mapDerivedCategory)
      (χ : mY.E ⋙ (inverseModules IB) ≅ (inverseModules IA) ⋙ mX.E),
    AdjunctionNormalized mY aY dY ∧ AdjunctionNormalized mX aX dX ∧
    (∀ (H : Modules BY) (U : Dᵒᵖ)
      (x : ((inverseModules IA).obj ((restriction φY).obj H)).val.obj U),
      ((a_h IA IB ring_compat inferInstance).hom.app H).val.app U x =
        (((inverseUnderlying IB).inv.app H).hom.app U
          (((inverseUnderlying IA).hom.app ((restriction φY).obj H)).hom.app U
            (ULift.up x))).down) ∧
    (∀ (H : CochainComplex (Modules BY) ℤ),
      (aD_h IA IB ring_compat inferInstance).hom.app (DerivedCategory.Q.obj H) =
        (inverseModules IA).mapDerivedCategory.map
          ((restriction φY).mapDerivedCategoryFactors.hom.app H) ≫
          (inverseModules IA).mapDerivedCategoryFactors.hom.app
            (((restriction φY).mapHomologicalComplex (.up ℤ)).obj H) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (a_h IA IB ring_compat inferInstance) (.up ℤ)).hom.app H) ≫
          (restriction φX).mapDerivedCategoryFactors.inv.app
            (((inverseModules IB).mapHomologicalComplex (.up ℤ)).obj H) ≫
          (restriction φX).mapDerivedCategory.map
            ((inverseModules IB).mapDerivedCategoryFactors.inv.app H)) ∧
    (∀ (M : Modules AY) (Z : Sheaf J (Type u))
      (b : Z ⟶ (sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj BY)
      (x : Z ⟶ (underlying AY).obj M)
      (z : Z ⟶ (underlying BY).obj (mY.E.obj M)),
      (∀ (U : Cᵒᵖ) (t : Z.obj.obj U),
        @id ((mY.E.obj M).val.obj U) (z.hom.app U t).down =
          pure mY M U (@id (BY.obj.obj U) (b.hom.app U t).down)
            (@id (M.val.obj U) (x.hom.app U t).down)) →
      ∀ (U : Dᵒᵖ) (t : (L.obj Z).obj.obj U),
        (χ.hom.app M).val.app U
          (((inverseUnderlying IB).inv.app (mY.E.obj M)).hom.app U ((L.map z).hom.app U t)).down =
        pure mX ((inverseModules IA).obj M) U
          (@id (BX.obj.obj U) ((L.map b ≫ (inverseRing IB).hom).hom.app U t).down)
          (((inverseUnderlying IA).inv.app M).hom.app U ((L.map x).hom.app U t)).down) ∧
    (∀ M : Modules AY,
      (inverseModules IA).map (aY.unit.app M) ≫
        (a_h IA IB ring_compat inferInstance).hom.app (mY.E.obj M) ≫
          (restriction φX).map (χ.hom.app M) = aX.unit.app ((inverseModules IA).obj M)) ∧
    (∀ (P : CochainComplex (Modules AY) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{u, u, u} (J := J) (R := AY) P →
      (∀ n : ℤ, IsFlatOnSite.{u, u, u, u} (J := J) (R := AY) (P.X n)) →
      IsIso (mX.ε.app (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (θ_h IA IB ring_compat inferInstance dY dX).app (DerivedCategory.Q.obj P) ≫
          (inverseModules IB).mapDerivedCategory.map (mY.ε.app P) ≫
          (inverseModules IB).mapDerivedCategoryFactors.hom.app
            ((mY.E.mapHomologicalComplex (.up ℤ)).obj P) =
        mX.T.map ((inverseModules IA).mapDerivedCategoryFactors.hom.app P) ≫
          mX.ε.app (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex χ (.up ℤ)).inv.app P)) ∧
    IsIso (θ_h IA IB ring_compat inferInstance dY dX) := by
  classical
  let g : GeometricMorphism (Sheaf K (Type u)) (Sheaf J (Type u)) :=
    ⟨L, R, adj, inferInstance⟩
  have hgeo := (GeometricMorphism.geometric_inverse_image_exact J K g).2.2
  obtain ⟨hAl, hAc⟩ := (exactFunctor_iff _).mp ((hgeo AY).2 AX IA).1
  obtain ⟨hBl, hBc⟩ := (exactFunctor_iff _).mp ((hgeo BY).2 BX IB).1
  have := hAl
  have := hAc
  have := hBl
  have := hBc
  have := Functor.additive_of_preserves_binary_products (inverseModules IA)
  have := Functor.additive_of_preserves_binary_products (inverseModules IB)
  obtain ⟨hYl, hYc, _⟩ := sheafRingCoefficientOrdinaryAdjunction φY
  obtain ⟨hXl, hXc, _⟩ := sheafRingCoefficientOrdinaryAdjunction φX
  have := hYl
  have := hYc
  have := hXl
  have := hXc
  obtain ⟨aY, dY, hnY, htY⟩ := normalized_adjunction_exists mY
  obtain ⟨aX, dX, hnX, htX⟩ := normalized_adjunction_exists mX
  obtain ⟨χ, hpure, hunit⟩ :=
    ordinary_comparison_exists φY φX L R adj IA IB ring_compat mY mX aY aX hnY.1 hnX.1
  have had : aD_h IA IB ring_compat inferInstance =
      Functor.mapDerivedCategorySquareIso (a_h IA IB ring_compat inferInstance) := by
    unfold aD_h
    rfl
  have hrep : ∀ (P : CochainComplex (Modules AY) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{u, u, u} (J := J) (R := AY) P →
      (∀ n : ℤ, IsFlatOnSite.{u, u, u, u} (J := J) (R := AY) (P.X n)) →
      IsIso (mX.ε.app (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (θ_h IA IB ring_compat inferInstance dY dX).app (DerivedCategory.Q.obj P) ≫
          (inverseModules IB).mapDerivedCategory.map (mY.ε.app P) ≫
          (inverseModules IB).mapDerivedCategoryFactors.hom.app
            ((mY.E.mapHomologicalComplex (.up ℤ)).obj P) =
        mX.T.map ((inverseModules IA).mapDerivedCategoryFactors.hom.app P) ≫
          mX.ε.app (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex χ (.up ℤ)).inv.app P) := by
    intro P hP hf
    have : (unliftInverseImage IA).modules.Additive := by
      change (inverseModules IA).Additive
      infer_instance
    have hk := SheafOfModules.kFlat_inverseImage_independent L R adj
      (unliftInverseImage IA) P hP hf
    refine ⟨mX.computes _ hk, ?_⟩
    have hm (X : DerivedCategory (Modules AY)) :
        dX.unit.app ((inverseModules IA).mapDerivedCategory.obj X) ≫
          (restriction φX).mapDerivedCategory.map
            ((θ_h IA IB ring_compat inferInstance dY dX).app X) =
        (inverseModules IA).mapDerivedCategory.map (dY.unit.app X) ≫
          (Functor.mapDerivedCategorySquareIso
            (a_h IA IB ring_compat inferInstance)).hom.app (mY.T.obj X) := by
      rw [← had]
      unfold θ_h
      exact (unit_mateEquiv_symm dY dX
        (TwoSquare.mk _ _ _ _ (aD_h IA IB ring_compat inferInstance).hom) X).symm
    have h := mate_computes mY.E mX.E (restriction φY) (restriction φX) aY aX
      mY.T mX.T dY dX mY.ε mX.ε (inverseModules IA) (inverseModules IB)
      (a_h IA IB ring_compat inferInstance) χ
      (θ_h IA IB ring_compat inferInstance dY dX) hm htY htX hunit P
    apply (cancel_mono (DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app P))).mp
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    erw [DerivedCategory.Q.map_id, Category.comp_id]
    exact h
  refine ⟨inferInstance, inferInstance, hAl, hAc, hBl, hBc,
    hYl, hYc, hXl, hXc, aY, aX, dY, dX, χ, hnY, hnX,
    a_h_spec IA IB ring_compat inferInstance, ?_, hpure, hunit, ?_, ?_⟩
  · intro H
    have h := Functor.exactSquare_fac (a_h IA IB ring_compat inferInstance) H
    rw [← had] at h
    change (aD_h IA IB ring_compat inferInstance).hom.app (DerivedCategory.Q.obj H) ≫
      (restriction φX).mapDerivedCategory.map
        ((inverseModules IB).mapDerivedCategoryFactors.hom.app H) ≫
      (restriction φX).mapDerivedCategoryFactors.hom.app
        (((inverseModules IB).mapHomologicalComplex (.up ℤ)).obj H) = _ at h
    apply (cancel_mono
      ((restriction φX).mapDerivedCategory.map
        ((inverseModules IB).mapDerivedCategoryFactors.hom.app H) ≫
      (restriction φX).mapDerivedCategoryFactors.hom.app
        (((inverseModules IB).mapHomologicalComplex (.up ℤ)).obj H))).mp
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [(restriction φX).mapDerivedCategory.map_id, Category.id_comp,
      Iso.inv_hom_id_app, Category.comp_id]
    exact h
  · exact hrep
  · let β := θ_h IA IB ring_compat inferInstance dY dX
    have hP (P : CochainComplex (Modules AY) ℤ)
        (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := AY) P)
        (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := AY) (P.X n)) :
        IsIso (β.app (DerivedCategory.Q.obj P)) := by
      have := mY.computes P hp
      have := (hrep P hp hf).1
      have : IsIso (β.app (DerivedCategory.Q.obj P) ≫
          (inverseModules IB).mapDerivedCategory.map (mY.ε.app P) ≫
          (inverseModules IB).mapDerivedCategoryFactors.hom.app
            ((mY.E.mapHomologicalComplex (.up ℤ)).obj P)) := by
        rw [(hrep P hp hf).2]
        infer_instance
      exact IsIso.of_isIso_comp_right (β.app (DerivedCategory.Q.obj P))
        ((inverseModules IB).mapDerivedCategory.map (mY.ε.app P) ≫
          (inverseModules IB).mapDerivedCategoryFactors.hom.app
            ((mY.E.mapHomologicalComplex (.up ℤ)).obj P))
    have hK (H : CochainComplex (Modules AY) ℤ) : IsIso (β.app (DerivedCategory.Q.obj H)) := by
      obtain ⟨P, p, hp, hf, hq, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := AY) H
      have hf' (n : ℤ) : IsFlatOnSite (J := J) (R := AY) (P.X n) :=
        (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso AY (P.X n)).symm (hf n)
      have := hP P hp hf'
      have : QuasiIso p := hq
      have : IsIso (((inverseModules IA).mapDerivedCategory ⋙ mX.T).map
          (DerivedCategory.Q.map p) ≫ β.app (DerivedCategory.Q.obj H)) := by
        rw [β.naturality]
        infer_instance
      exact IsIso.of_isIso_comp_left
        (((inverseModules IA).mapDerivedCategory ⋙ mX.T).map (DerivedCategory.Q.map p))
        (β.app (DerivedCategory.Q.obj H))
    have hX (X : DerivedCategory (Modules AY)) : IsIso (β.app X) := by
      let e := DerivedCategory.Q.objObjPreimageIso X
      have := hK (DerivedCategory.Q.objPreimage X)
      have : IsIso (((inverseModules IA).mapDerivedCategory ⋙ mX.T).map e.hom ≫
          β.app X) := by
        rw [β.naturality]
        infer_instance
      exact IsIso.of_isIso_comp_left
        (((inverseModules IA).mapDerivedCategory ⋙ mX.T).map e.hom) (β.app X)
    exact NatIso.isIso_of_isIso_app β

end

-- Keep the same localization API closed in the composition and identity calculations.
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors DerivedCategory.Q DerivedCategory.Qh

/-- Exact localization of a module composition identification.
This is the standard exact-functor comparison, with composite exactness derived internally.
Source: Stacks 06YY and 0D6D
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
@[irreducible]
noncomputable def compositionDerived
    {A B C : Type u₁} [Category.{v₁} A] [Category.{v₁} B] [Category.{v₁} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (c : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory := by
  letI := comp_preservesFiniteLimits F G
  letI := comp_preservesFiniteColimits F G
  exact (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso c

private theorem mate_identity_square
    {A B : Type*} [Category A] [Category B]
    {T : A ⥤ B} {r : B ⥤ A} (d : T ⊣ r)
    {F : A ⥤ A} {G : B ⥤ B} (i : F ≅ 𝟭 A) (j : G ≅ 𝟭 B)
    (a : r ⋙ F ⟶ G ⋙ r)
    (ha : ∀ M : B, a.app M ≫ r.map (j.hom.app M) = i.hom.app (r.obj M)) :
    Functor.whiskerRight i.inv T ≫ mate d d a ≫ Functor.whiskerLeft T j.hom =
      (Functor.leftUnitor T).hom ≫ (Functor.rightUnitor T).inv := by
  have ht (X : A) : (mate d d a).app X ≫ j.hom.app (T.obj X) = T.map (i.hom.app X) := by
    apply (d.homEquiv _ _).injective
    rw [d.homEquiv_unit, d.homEquiv_unit, r.map_comp, ← Category.assoc]
    have hu : F.map (d.unit.app X) ≫ a.app (T.obj X) =
        d.unit.app (F.obj X) ≫ r.map ((mate d d a).app X) :=
      unit_mateEquiv_symm d d (TwoSquare.mk _ _ _ _ a) X
    rw [← hu, Category.assoc, ha]
    have hn : F.map (d.unit.app X) ≫ i.hom.app (r.obj (T.obj X)) =
        i.hom.app X ≫ d.unit.app X := i.hom.naturality (d.unit.app X)
    rw [hn]
    exact d.unit.naturality (i.hom.app X)
  ext X
  change T.map (i.inv.app X) ≫ (mate d d a).app X ≫ j.hom.app (T.obj X) = 𝟙 _ ≫ 𝟙 _
  rw [ht, ← T.map_comp, Iso.inv_hom_id_app]
  erw [T.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem derived_identity_square
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ A) (G : B ⥤ B) (r : B ⥤ A)
    [F.Additive] [G.Additive] [r.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (i : F ≅ 𝟭 A) (j : G ≅ 𝟭 B) (a : r ⋙ F ≅ G ⋙ r)
    (ha : ∀ M : B, a.hom.app M ≫ r.map (j.hom.app M) = i.hom.app (r.obj M)) :
    ∀ H : DerivedCategory B,
      (Functor.mapDerivedCategorySquareIso a).hom.app H ≫
        r.mapDerivedCategory.map
          ((Functor.mapDerivedCategoryNatIso j ≪≫ Functor.mapDerivedCategoryIdIso B).hom.app H) =
      (Functor.mapDerivedCategoryNatIso i ≪≫ Functor.mapDerivedCategoryIdIso A).hom.app
        (r.mapDerivedCategory.obj H) := by
  let cF := Functor.exactDerivedRestrictionUnit F i
  let cG := Functor.exactDerivedRestrictionUnit G j
  let τ₁ : r.mapDerivedCategory ⋙ F.mapDerivedCategory ⟶ r.mapDerivedCategory :=
    (Functor.mapDerivedCategorySquareIso a).hom ≫ Functor.whiskerRight cG.hom r.mapDerivedCategory
  let τ₂ : r.mapDerivedCategory ⋙ F.mapDerivedCategory ⟶ r.mapDerivedCategory :=
    Functor.whiskerLeft r.mapDerivedCategory cF.hom
  let := comp_preservesFiniteLimits r F
  let := comp_preservesFiniteColimits r F
  let := comp_preservesFiniteLimits G r
  let := comp_preservesFiniteColimits G r
  have h : a ≪≫ Functor.isoWhiskerRight j r = Functor.isoWhiskerLeft r i := by
    apply Iso.ext
    ext M
    exact ha M
  have he : τ₁ = τ₂ := by
    apply (cancel_epi (Functor.mapDerivedCategoryCompIso r F).hom).1
    dsimp only [τ₁, τ₂, cF, cG, Functor.exactDerivedRestrictionUnit,
      Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom]
    simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
      Category.assoc, Iso.hom_inv_id_assoc]
    rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight j r),
      Functor.mapDerivedCategoryCompIso_id_comp]
    erw [Category.comp_id]
    rw [← Functor.mapDerivedCategoryNatIso_trans, h]
    rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft r i),
      Functor.mapDerivedCategoryCompIso_comp_id]
    erw [Category.comp_id]
  intro H
  exact congr_app he H

private theorem derived_composition_square {A₀ A₁ A₂ B₀ B₁ B₂ : Type u₁}
    [Category.{v₁} A₀] [Category.{v₁} A₁] [Category.{v₁} A₂]
    [Category.{v₁} B₀] [Category.{v₁} B₁] [Category.{v₁} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂]
    [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory.{w} A₀] [HasDerivedCategory.{w} A₁] [HasDerivedCategory.{w} A₂]
    [HasDerivedCategory.{w} B₀] [HasDerivedCategory.{w} B₁] [HasDerivedCategory.{w} B₂]
    (r₀ : B₀ ⥤ A₀) (r₁ : B₁ ⥤ A₁) (r₂ : B₂ ⥤ A₂)
    (gA : A₀ ⥤ A₁) (gB : B₀ ⥤ B₁)
    (fA : A₁ ⥤ A₂) (fB : B₁ ⥤ B₂)
    (hA : A₀ ⥤ A₂) (hB : B₀ ⥤ B₂)
    [r₀.Additive] [r₁.Additive] [r₂.Additive]
    [gA.Additive] [gB.Additive] [fA.Additive] [fB.Additive] [hA.Additive] [hB.Additive]
    [PreservesFiniteLimits r₀] [PreservesFiniteColimits r₀]
    [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
    [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
    [PreservesFiniteLimits gA] [PreservesFiniteColimits gA]
    [PreservesFiniteLimits gB] [PreservesFiniteColimits gB]
    [PreservesFiniteLimits fA] [PreservesFiniteColimits fA]
    [PreservesFiniteLimits fB] [PreservesFiniteColimits fB]
    [PreservesFiniteLimits hA] [PreservesFiniteColimits hA]
    [PreservesFiniteLimits hB] [PreservesFiniteColimits hB]
    (cA : gA ⋙ fA ≅ hA) (cB : gB ⋙ fB ≅ hB)
    (ag : r₀ ⋙ gA ≅ gB ⋙ r₁) (af : r₁ ⋙ fA ≅ fB ⋙ r₂)
    (ah : r₀ ⋙ hA ≅ hB ⋙ r₂)
    (ha : ∀ M : B₀, cA.hom.app (r₀.obj M) ≫ ah.hom.app M =
      fA.map (ag.hom.app M) ≫ af.hom.app (gB.obj M) ≫ r₂.map (cB.hom.app M))
    (M : DerivedCategory B₀) :
    (compositionDerived gA fA hA cA).hom.app (r₀.mapDerivedCategory.obj M) ≫
        (Functor.mapDerivedCategorySquareIso ah).hom.app M =
      fA.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso ag).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso af).hom.app (gB.mapDerivedCategory.obj M) ≫
        r₂.mapDerivedCategory.map ((compositionDerived gB fB hB cB).hom.app M) := by
  let := comp_preservesFiniteLimits gA fA
  let := comp_preservesFiniteColimits gA fA
  let := comp_preservesFiniteLimits gB fB
  let := comp_preservesFiniteColimits gB fB
  have hi : ∀ N : B₀, ah.hom.app N ≫ r₂.map (cB.inv.app N) =
      cA.inv.app (r₀.obj N) ≫ fA.map (ag.hom.app N) ≫ af.hom.app (gB.obj N) := by
    intro N
    apply (cancel_epi (cA.hom.app (r₀.obj N))).1
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, ha]
    simp only [Category.assoc, ← r₂.map_comp, Iso.hom_inv_id_app]
    erw [r₂.map_id, Category.comp_id]
  have hd := Functor.exactSquare_comp_inverse gB fB hB gA fA hA r₀ r₁ r₂
    ag af ah cB.symm cA.symm hi M
  have heA : (Functor.mapDerivedCategoryNatIso cA.symm ≪≫
      Functor.mapDerivedCategoryCompIso gA fA).hom = (compositionDerived gA fA hA cA).inv := by
    simp only [compositionDerived, Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm]
  have heB : (Functor.mapDerivedCategoryNatIso cB.symm ≪≫
      Functor.mapDerivedCategoryCompIso gB fB).hom = (compositionDerived gB fB hB cB).inv := by
    simp only [compositionDerived, Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm]
  change _ ≫ r₂.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso cB.symm ≪≫
    Functor.mapDerivedCategoryCompIso gB fB).hom.app M) =
      (Functor.mapDerivedCategoryNatIso cA.symm ≪≫
        Functor.mapDerivedCategoryCompIso gA fA).hom.app (r₀.mapDerivedCategory.obj M) ≫ _ at hd
  rw [heA, heB] at hd
  have he := congrArg (fun t ↦
    (compositionDerived gA fA hA cA).hom.app (r₀.mapDerivedCategory.obj M) ≫ t ≫
      r₂.mapDerivedCategory.map ((compositionDerived gB fB hB cB).hom.app M)) hd
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← r₂.mapDerivedCategory.map_comp, Iso.inv_hom_id_app, r₂.mapDerivedCategory.map_id,
    Category.comp_id] using he

private theorem mate_composition_square
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {T₀ : A₀ ⥤ B₀} {r₀ : B₀ ⥤ A₀} (d₀ : T₀ ⊣ r₀)
    {T₁ : A₁ ⥤ B₁} {r₁ : B₁ ⥤ A₁} (d₁ : T₁ ⊣ r₁)
    {T₂ : A₂ ⥤ B₂} {r₂ : B₂ ⥤ A₂} (d₂ : T₂ ⊣ r₂)
    {gA : A₀ ⥤ A₁} {gB : B₀ ⥤ B₁}
    {fA : A₁ ⥤ A₂} {fB : B₁ ⥤ B₂}
    {hA : A₀ ⥤ A₂} {hB : B₀ ⥤ B₂}
    (cA : gA ⋙ fA ≅ hA) (cB : gB ⋙ fB ≅ hB)
    (ag : r₀ ⋙ gA ⟶ gB ⋙ r₁) (af : r₁ ⋙ fA ⟶ fB ⋙ r₂)
    (ah : r₀ ⋙ hA ⟶ hB ⋙ r₂)
    (ha : ∀ M : B₀, cA.hom.app (r₀.obj M) ≫ ah.app M =
      fA.map (ag.app M) ≫ af.app (gB.obj M) ≫ r₂.map (cB.hom.app M))
    (X : A₀) :
    T₂.map (cA.hom.app X) ≫ (mate d₀ d₂ ah).app X ≫ cB.inv.app (T₀.obj X) =
      (mate d₁ d₂ af).app (gA.obj X) ≫ fB.map ((mate d₀ d₁ ag).app X) := by
  apply (cancel_mono (cB.hom.app (T₀.obj X))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  apply (d₂.homEquiv _ _).injective
  rw [d₂.homEquiv_unit, d₂.homEquiv_unit]
  simp only [Functor.map_comp]
  have uh := unit_mateEquiv_symm d₀ d₂ (TwoSquare.mk _ _ _ _ ah) X
  have uf := unit_mateEquiv_symm d₁ d₂ (TwoSquare.mk _ _ _ _ af) (gA.obj X)
  have ug := unit_mateEquiv_symm d₀ d₁ (TwoSquare.mk _ _ _ _ ag) X
  change hA.map (d₀.unit.app X) ≫ ah.app (T₀.obj X) =
    d₂.unit.app (hA.obj X) ≫ r₂.map ((mate d₀ d₂ ah).app X) at uh
  change fA.map (d₁.unit.app (gA.obj X)) ≫ af.app (T₁.obj (gA.obj X)) =
    d₂.unit.app (fA.obj (gA.obj X)) ≫
      r₂.map ((mate d₁ d₂ af).app (gA.obj X)) at uf
  change gA.map (d₀.unit.app X) ≫ ag.app (T₀.obj X) =
    d₁.unit.app (gA.obj X) ≫ r₁.map ((mate d₀ d₁ ag).app X) at ug
  rw [d₂.unit_naturality_assoc]
  rw [← uh,
    ← reassoc_of% (cA.hom.naturality (d₀.unit.app X)), ha]
  dsimp only [Functor.comp_obj]
  rw [← reassoc_of% uf]
  have hn := af.naturality ((mate d₀ d₁ ag).app X)
  change fA.map (r₁.map ((mate d₀ d₁ ag).app X)) ≫ af.app (gB.obj (T₀.obj X)) =
    af.app (T₁.obj (gA.obj X)) ≫ r₂.map (fB.map ((mate d₀ d₁ ag).app X)) at hn
  rw [← reassoc_of% hn]
  rw [← fA.map_comp_assoc, ug, fA.map_comp]
  simp only [Category.assoc]

section Composition

variable {CZ CY CX : Type u}
  [Category.{u} CZ] [Category.{u} CY] [Category.{u} CX]
  {JZ : GrothendieckTopology CZ} {JY : GrothendieckTopology CY}
  {JX : GrothendieckTopology CX}
  [HasSheafify JZ AddCommGrpCat.{u}] [JZ.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify JY AddCommGrpCat.{u}] [JY.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify JX AddCommGrpCat.{u}] [JX.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {AZ BZ : Sheaf JZ CommRingCat.{u}} {AY BY : Sheaf JY CommRingCat.{u}}
  {AX BX : Sheaf JX CommRingCat.{u}}
  {φZ : AZ ⟶ BZ} {φY : AY ⟶ BY} {φX : AX ⟶ BX}
  (Lg : Sheaf JZ (Type u) ⥤ Sheaf JY (Type u))
  (Rg : Sheaf JY (Type u) ⥤ Sheaf JZ (Type u)) (adjg : Lg ⊣ Rg)
  (Lf : Sheaf JY (Type u) ⥤ Sheaf JX (Type u))
  (Rf : Sheaf JX (Type u) ⥤ Sheaf JY (Type u)) (adjf : Lf ⊣ Rf)
  (Lh : Sheaf JZ (Type u) ⥤ Sheaf JX (Type u))
  (adjh : Lh ⊣ Rf ⋙ Rg)
  [PreservesFiniteLimits Lg] [PreservesFiniteLimits Lf] [PreservesFiniteLimits Lh]
  (IgA : InverseImage Lg AZ AY)
  (IgB : InverseImage Lg BZ BY)
  (IfA : InverseImage Lf AY AX)
  (IfB : InverseImage Lf BY BX)
  (IhA : InverseImage Lh AZ AX)
  (IhB : InverseImage Lh BZ BX)
  (hg : Lg.map ((sheafCompose JZ
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φZ) ≫
      (inverseRing IgB).hom = (inverseRing IgA).hom ≫
        (sheafCompose JY (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY)
  (hf : Lf.map ((sheafCompose JY
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY) ≫
      (inverseRing IfB).hom = (inverseRing IfA).hom ≫
        (sheafCompose JX (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)
  (hh : Lh.map ((sheafCompose JZ
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φZ) ≫
      (inverseRing IhB).hom = (inverseRing IhA).hom ≫
        (sheafCompose JX (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)
  [HasDerivedCategory.{w} (Modules AZ)] [HasDerivedCategory.{w} (Modules BZ)]
  [HasDerivedCategory.{w} (Modules AY)] [HasDerivedCategory.{w} (Modules BY)]
  [HasDerivedCategory.{w} (Modules AX)] [HasDerivedCategory.{w} (Modules BX)]
  [(inverseModules IgA).Additive]
  [PreservesFiniteLimits (inverseModules IgA)] [PreservesFiniteColimits (inverseModules IgA)]
  [(inverseModules IgB).Additive]
  [PreservesFiniteLimits (inverseModules IgB)] [PreservesFiniteColimits (inverseModules IgB)]
  [(inverseModules IfA).Additive]
  [PreservesFiniteLimits (inverseModules IfA)] [PreservesFiniteColimits (inverseModules IfA)]
  [(inverseModules IfB).Additive]
  [PreservesFiniteLimits (inverseModules IfB)] [PreservesFiniteColimits (inverseModules IfB)]
  [(inverseModules IhA).Additive]
  [PreservesFiniteLimits (inverseModules IhA)] [PreservesFiniteColimits (inverseModules IhA)]
  [(inverseModules IhB).Additive]
  [PreservesFiniteLimits (inverseModules IhB)] [PreservesFiniteColimits (inverseModules IhB)]
  [PreservesFiniteLimits (restriction φZ)] [PreservesFiniteColimits (restriction φZ)]
  [PreservesFiniteLimits (restriction φY)] [PreservesFiniteColimits (restriction φY)]
  [PreservesFiniteLimits (restriction φX)] [PreservesFiniteColimits (restriction φX)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Geometric composition of the specified scalar comparisons.
The composite topos morphism has right adjoint Rf ⋙ Rg. Its chosen inverse image
Lh is canonically identified with Lg ⋙ Lf by leftAdjointUniq for adjg.comp adjf
and adjh. Arbitrary algebraic presentations of that inverse image are compared
by cA and cB, using this specified underlying-sheaf composition identification.
Their equations fix the canonical module composition isomorphisms on underlying sheaves.
The displayed ring equations
fix the ring composition maps. The derived maps are the existing exact localization
of these same module identifications, not freely supplied comparison maps.
Source: blueprint det-prop-scalar-six-pullback (1), Stacks 0D6D
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).
Proof: the underlying equations uniquely determine cA and cB, because both sides are
inverse images of the same sheaf with the same transported operations. The ring
composition equations show that the canonical action a_h is the paste of a_g and a_f
under cA and cB. Exact localization preserves that paste. Apply clause (1) of
lem-weil-pbc-mate-pasting to the shared scalar adjunctions to get the stated equation.
No flatness of a ring map or boundedness of a complex is used. -/
theorem θ_composition
    (ringA : ((adjg.comp adjf).leftAdjointUniq adjh).hom.app
        ((sheafCompose JZ
          (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj AZ) ≫
        (inverseRing IhA).hom = Lf.map (inverseRing IgA).hom ≫ (inverseRing IfA).hom)
    (ringB : ((adjg.comp adjf).leftAdjointUniq adjh).hom.app
        ((sheafCompose JZ
          (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj BZ) ≫
        (inverseRing IhB).hom = Lf.map (inverseRing IgB).hom ≫ (inverseRing IfB).hom)
    (mZ : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φZ)
    (mY : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φY)
    (mX : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φX)
    (dZ : mZ.T ⊣ (restriction φZ).mapDerivedCategory)
    (dY : mY.T ⊣ (restriction φY).mapDerivedCategory)
    (dX : mX.T ⊣ (restriction φX).mapDerivedCategory) :
    ∃ (cA : (inverseModules IgA) ⋙ (inverseModules IfA) ≅ (inverseModules IhA))
      (cB : (inverseModules IgB) ⋙ (inverseModules IfB) ≅ (inverseModules IhB)),
    (∀ (M : Modules AZ) (U : CXᵒᵖ)
      (x : ((inverseModules IfA).obj ((inverseModules IgA).obj M)).val.obj U),
      (cA.hom.app M).val.app U x =
        (((inverseUnderlying IhA).inv.app M).hom.app U
          ((((adjg.comp adjf).leftAdjointUniq adjh).hom.app ((underlying AZ).obj M)).hom.app U
            ((Lf.map ((inverseUnderlying IgA).hom.app M)).hom.app U
              (((inverseUnderlying IfA).hom.app ((inverseModules IgA).obj M)).hom.app U
                (ULift.up x))))).down) ∧
    (∀ (M : Modules BZ) (U : CXᵒᵖ)
      (x : ((inverseModules IfB).obj ((inverseModules IgB).obj M)).val.obj U),
      (cB.hom.app M).val.app U x =
        (((inverseUnderlying IhB).inv.app M).hom.app U
          ((((adjg.comp adjf).leftAdjointUniq adjh).hom.app ((underlying BZ).obj M)).hom.app U
            ((Lf.map ((inverseUnderlying IgB).hom.app M)).hom.app U
              (((inverseUnderlying IfB).hom.app ((inverseModules IgB).obj M)).hom.app U
                (ULift.up x))))).down) ∧
    Functor.whiskerRight
        (compositionDerived (inverseModules IgA) (inverseModules IfA)
          (inverseModules IhA) cA).hom mX.T ≫
      θ_h IhA IhB hh inferInstance dZ dX ≫
      Functor.whiskerLeft mZ.T
        (compositionDerived (inverseModules IgB) (inverseModules IfB) (inverseModules IhB) cB).inv =
      (Functor.associator (inverseModules IgA).mapDerivedCategory
        (inverseModules IfA).mapDerivedCategory mX.T).hom ≫
      Functor.whiskerLeft (inverseModules IgA).mapDerivedCategory
        (θ_h IfA IfB hf inferInstance dY dX) ≫
      (Functor.associator (inverseModules IgA).mapDerivedCategory mY.T
        (inverseModules IfB).mapDerivedCategory).inv ≫
      Functor.whiskerRight (θ_h IgA IgB hg inferInstance dZ dY)
        (inverseModules IfB).mapDerivedCategory ≫
      (Functor.associator mZ.T (inverseModules IgB).mapDerivedCategory
        (inverseModules IfB).mapDerivedCategory).hom := by
  let cA := moduleComparison ((adjg.comp adjf).leftAdjointUniq adjh)
    (compositeInverseImage IgA IfA) IhA ringA
  let cB := moduleComparison ((adjg.comp adjf).leftAdjointUniq adjh)
    (compositeInverseImage IgB IfB) IhB ringB
  refine ⟨cA, cB, ?_, ?_, ?_⟩
  · intro M U x
    exact moduleComparison_hom_apply ((adjg.comp adjf).leftAdjointUniq adjh)
      (compositeInverseImage IgA IfA) IhA ringA M U x
  · intro M U x
    exact moduleComparison_hom_apply ((adjg.comp adjf).leftAdjointUniq adjh)
      (compositeInverseImage IgB IfB) IhB ringB M U x
  · have ha : ∀ M : Modules BZ,
        cA.hom.app ((restriction φZ).obj M) ≫ (a_h IhA IhB hh inferInstance).hom.app M =
          (inverseModules IfA).map ((a_h IgA IgB hg inferInstance).hom.app M) ≫
            (a_h IfA IfB hf inferInstance).hom.app ((inverseModules IgB).obj M) ≫
            (restriction φX).map (cB.hom.app M) := by
      intro M
      apply (underlying AX).map_injective
      have hcA := moduleComparison_underlying
        ((adjg.comp adjf).leftAdjointUniq adjh) (compositeInverseImage IgA IfA) IhA ringA
        ((restriction φZ).obj M)
      have hcB := moduleComparison_underlying
        ((adjg.comp adjf).leftAdjointUniq adjh) (compositeInverseImage IgB IfB) IhB ringB M
      have hact (N : Modules BY) : (underlying AX).map
          ((a_h IfA IfB hf inferInstance).hom.app N) =
          IfA.moduleUnderlying.hom.app ((restriction φY).obj N) ≫
            IfB.moduleUnderlying.inv.app N := by
        ext U x
        exact congrArg ULift.up (a_h_spec IfA IfB hf inferInstance N U x.down)
      have hactg : (underlying AY).map ((a_h IgA IgB hg inferInstance).hom.app M) =
          IgA.moduleUnderlying.hom.app ((restriction φZ).obj M) ≫
            IgB.moduleUnderlying.inv.app M := by
        ext U x
        exact congrArg ULift.up (a_h_spec IgA IgB hg inferInstance M U x.down)
      have hacth : (underlying AX).map ((a_h IhA IhB hh inferInstance).hom.app M) =
          IhA.moduleUnderlying.hom.app ((restriction φZ).obj M) ≫
            IhB.moduleUnderlying.inv.app M := by
        ext U x
        exact congrArg ULift.up (a_h_spec IhA IhB hh inferInstance M U x.down)
      simp only [Functor.map_comp]
      rw [hacth, hact]
      change _ = _ ≫ _ ≫ (underlying BX).map (cB.hom.app M)
      change (underlying AX).map (cA.hom.app ((restriction φZ).obj M)) = _ at hcA
      change (underlying BX).map (cB.hom.app M) = _ at hcB
      rw [hcA, hcB]
      dsimp only [CategoryTheory.compareMap, compositeInverseImage, Iso.app_hom, Iso.app_inv,
        Iso.symm_inv, Iso.symm_hom, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app]
      simp only [Category.id_comp, Category.comp_id, Category.assoc,
        Iso.inv_hom_id_app_assoc]
      erw [reassoc_of% (IfA.moduleUnderlying.hom.naturality
        ((a_h IgA IgB hg inferInstance).hom.app M))]
      change _ = IfA.moduleUnderlying.hom.app _ ≫
        Lf.map ((underlying AY).map ((a_h IgA IgB hg inferInstance).hom.app M)) ≫ _
      rw [hactg, Functor.map_comp]
      simp only [Category.assoc, ← Lf.map_comp_assoc, Iso.inv_hom_id_app]
      rfl
    unfold θ_h
    ext X
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    apply mate_composition_square dZ dY dX
    intro M
    unfold aD_h
    exact derived_composition_square (restriction φZ) (restriction φY) (restriction φX)
      (inverseModules IgA) (inverseModules IgB) (inverseModules IfA) (inverseModules IfB)
      (inverseModules IhA) (inverseModules IhB) cA cB
      (a_h IgA IgB hg inferInstance) (a_h IfA IfB hf inferInstance)
      (a_h IhA IhB hh inferInstance) ha M

end Composition

section Identity

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
  (IA : InverseImage (𝟭 (Sheaf J (Type u))) A A)
  (IB : InverseImage (𝟭 (Sheaf J (Type u))) B B)
  (h : (𝟭 (Sheaf J (Type u))).map ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φ) ≫
      (inverseRing IB).hom = (inverseRing IA).hom ≫
        (sheafCompose J (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φ)
  [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
  [(inverseModules IA).Additive] [(inverseModules IB).Additive]
  [PreservesFiniteLimits (inverseModules IA)] [PreservesFiniteColimits (inverseModules IA)]
  [PreservesFiniteLimits (inverseModules IB)] [PreservesFiniteColimits (inverseModules IB)]
  [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]

set_option linter.flexible false in
/-- Identity normalization with canonical underlying ring and module identifications.
The geometric inverse image is the identity functor of the sheaf topos, with its
identity adjunction. The module identifications iA and iB are fixed on underlying
sheaves; their displayed exact localizations identify θ_h with the identity of T.
Source: blueprint det-prop-scalar-six-pullback (1), Stacks 0D6D
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).
Proof: the identity underlying maps lift uniquely to iA and iB under the ring equations.
The action a_h becomes the identity of scalar restriction under these identifications.
Localizing preserves this equation, and clause (4) of lem-weil-pbc-mate-pasting identifies
its inverse mate with the identity of scalar extension. The unitors give exactly the
stated equation. -/
theorem θ_identity
    (ringA : (inverseRing IA).hom = 𝟙 _)
    (ringB : (inverseRing IB).hom = 𝟙 _)
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (d : m.T ⊣ (restriction φ).mapDerivedCategory) :
    ∃ (iA : (inverseModules IA) ≅ 𝟭 (Modules A)) (iB : (inverseModules IB) ≅ 𝟭 (Modules B)),
    (∀ (M : Modules A) (U : Cᵒᵖ) (x : ((inverseModules IA).obj M).val.obj U),
      (iA.hom.app M).val.app U x =
        (((inverseUnderlying IA).hom.app M).hom.app U (ULift.up x)).down) ∧
    (∀ (M : Modules B) (U : Cᵒᵖ) (x : ((inverseModules IB).obj M).val.obj U),
      (iB.hom.app M).val.app U x =
        (((inverseUnderlying IB).hom.app M).hom.app U (ULift.up x)).down) ∧
    Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso iA ≪≫
          Functor.mapDerivedCategoryIdIso (Modules A)).inv m.T ≫
      θ_h IA IB h inferInstance d d ≫
      Functor.whiskerLeft m.T
        (Functor.mapDerivedCategoryNatIso iB ≪≫
          Functor.mapDerivedCategoryIdIso (Modules B)).hom =
      (Functor.leftUnitor m.T).hom ≫ (Functor.rightUnitor m.T).inv := by
  let iA := moduleComparison (Iso.refl _) IA (CategoryTheory.identityPresentation A) (by
    change 𝟙 _ ≫ 𝟙 _ = _
    simpa using ringA.symm)
  let iB := moduleComparison (Iso.refl _) IB (CategoryTheory.identityPresentation B) (by
    change 𝟙 _ ≫ 𝟙 _ = _
    simpa using ringB.symm)
  have hiA (M : Modules A) (U : Cᵒᵖ)
      (x : ((inverseModules IA).obj M).val.obj U) :
      (iA.hom.app M).val.app U x =
        (((inverseUnderlying IA).hom.app M).hom.app U (ULift.up x)).down := by
    exact moduleComparison_hom_apply (Iso.refl _) IA (CategoryTheory.identityPresentation A)
      (by change 𝟙 _ ≫ 𝟙 _ = _; simpa using ringA.symm) M U x
  have hiB (M : Modules B) (U : Cᵒᵖ)
      (x : ((inverseModules IB).obj M).val.obj U) :
      (iB.hom.app M).val.app U x =
        (((inverseUnderlying IB).hom.app M).hom.app U (ULift.up x)).down := by
    exact moduleComparison_hom_apply (Iso.refl _) IB (CategoryTheory.identityPresentation B)
      (by change 𝟙 _ ≫ 𝟙 _ = _; simpa using ringB.symm) M U x
  refine ⟨iA, iB, hiA, hiB, ?_⟩
  · have ha : ∀ M : Modules B,
        (a_h IA IB h inferInstance).hom.app M ≫ (restriction φ).map (iB.hom.app M) =
          iA.hom.app ((restriction φ).obj M) := by
      intro M
      ext U x
      change (iB.hom.app M).val.app U
        (((a_h IA IB h inferInstance).hom.app M).val.app U x) = _
      rw [a_h_spec]
      erw [hiB, hiA]
      change ((IB.moduleUnderlying.hom.app M).hom.app U
        (ULift.up (((IB.moduleUnderlying.inv.app M).hom.app U
          ((IA.moduleUnderlying.hom.app ((restriction φ).obj M)).hom.app U
            (ULift.up x))).down))).down = _
      have he := congrArg (fun q ↦ (q.hom.app U
        ((IA.moduleUnderlying.hom.app ((restriction φ).obj M)).hom.app U (ULift.up x))).down)
          (IB.moduleUnderlying.inv_hom_id_app M)
      exact he
    unfold θ_h
    apply mate_identity_square d _ _ _
    intro M
    unfold aD_h
    exact derived_identity_square (inverseModules IA) (inverseModules IB)
      (restriction φ) iA iB (a_h IA IB h inferInstance) ha M

end Identity

end SheafOfModules.ScalarPullback
