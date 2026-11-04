/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Flatness under algebraic inverse image

Source: Stacks Project, Modules on Sites, Tag 05VD, the inverse-image portion of
lemma-pullback-flat, before the final change of rings.
-/

@[expose] public section

universe uC vC uD vD r m w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

noncomputable section

set_option backward.isDefEq.respectTransparency false


section Sections

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

end Sections

section Operations

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙
    uliftFunctor.{r, max r m})]
  {R : Sheaf J CommRingCat.{r}}

private abbrev ringSets (R : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{r} ⋙
    uliftFunctor.{max r m, r})).obj R

private abbrev moduleSets (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
  ((toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙
    uliftFunctor.{r, max r m})).obj M)

private def ringHom (T : Sheaf J (Type (max r m)))
    (f : ∀ U : Cᵒᵖ, T.obj.obj U → R.obj.obj U)
    (hf : ∀ {U V : Cᵒᵖ} (i : U ⟶ V) (x : T.obj.obj U),
      R.obj.map i (f U x) = f V (T.obj.map i x)) : T ⟶ ringSets R :=
  ⟨{ app U := ↾fun x ↦ ULift.up (f U x)
     naturality := by
       intro U V i
       ext x
       exact ULift.ext _ _ (hf i x).symm }⟩

private def moduleHom (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : Sheaf J (Type (max r m)))
    (f : ∀ U : Cᵒᵖ, T.obj.obj U → M.val.obj U)
    (hf : ∀ {U V : Cᵒᵖ} (i : U ⟶ V) (x : T.obj.obj U),
      M.val.map i (f U x) = f V (T.obj.map i x)) : T ⟶ moduleSets M :=
  ⟨{ app U := ↾fun x ↦ ULift.up (f U x)
     naturality := by
       intro U V i
       ext x
       exact ULift.ext _ _ (hf i x).symm }⟩

private def moduleZero (M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : Sheaf J (Type (max r m))) : T ⟶ moduleSets M :=
  moduleHom M T (fun _ _ ↦ 0) (fun _ _ ↦ map_zero _)

private def moduleAdd {M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    {T : Sheaf J (Type (max r m))} (a b : T ⟶ moduleSets M) : T ⟶ moduleSets M :=
  moduleHom M T (fun U x ↦ (a.hom.app U x).down + (b.hom.app U x).down) (by
    intro U V i x
    rw [map_add]
    congr 1
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (a.hom.naturality i)).symm
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (b.hom.naturality i)).symm)

private def moduleSMul {M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    {T : Sheaf J (Type (max r m))} (a : T ⟶ ringSets R) (s : T ⟶ moduleSets M) :
    T ⟶ moduleSets M :=
  moduleHom M T (fun U x ↦ (show R.obj.obj U from (a.hom.app U x).down) •
    (show M.val.obj U from (s.hom.app U x).down)) (by
    intro U V i x
    rw [M.val.map_smul]
    congr 1
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (a.hom.naturality i)).symm
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (s.hom.naturality i)).symm)

private def ringZero (T : Sheaf J (Type (max r m))) : T ⟶ ringSets R :=
  ringHom T (fun _ _ ↦ 0) (fun _ _ ↦ map_zero _)

private def ringAdd {T : Sheaf J (Type (max r m))} (a b : T ⟶ ringSets R) :
    T ⟶ ringSets R :=
  ringHom T (fun U x ↦ (a.hom.app U x).down + (b.hom.app U x).down) (by
    intro U V i x
    rw [map_add]
    congr 1
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (a.hom.naturality i)).symm
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (b.hom.naturality i)).symm)

private def ringMul {T : Sheaf J (Type (max r m))} (a b : T ⟶ ringSets R) :
    T ⟶ ringSets R :=
  ringHom T (fun U x ↦ (a.hom.app U x).down * (b.hom.app U x).down) (by
    intro U V i x
    rw [map_mul]
    congr 1
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (a.hom.naturality i)).symm
    · exact congrArg ULift.down (congrArg (fun k ↦ k x) (b.hom.naturality i)).symm)

end Operations

section ImageOperations

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{max r m, r})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙
    uliftFunctor.{r, max r m})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max r m} ⋙
    uliftFunctor.{r, max r m})]
  {R : Sheaf J CommRingCat.{r}} {RI : Sheaf K CommRingCat.{r}}
  {L : Sheaf J (Type (max r m)) ⥤ Sheaf K (Type (max r m))}
  (I : AlgebraicInverseImageOfUniverses L R RI)
  {M : SheafOfModules.{max r m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
  {T : Sheaf J (Type (max r m))}

end ImageOperations

end

end SheafOfModules
