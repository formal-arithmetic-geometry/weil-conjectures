/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
/-! # Normalized principal-quotient cone augmentation

Source: Stacks Project, sites-cohomology.tex, Tags 06YP, 06YS, 06YT, 06YY and 07A6.
(blueprint: def-cbc-regular-quotient-cone-basic).

The cone is Mathlib's cone, with unshifted summand second in its biproduct API.
The ordinary extension is the existing sheafified tensor, whose pure tensors have
scalar first. All computation maps below use the universal derived counit.
-/

@[expose] public section
set_option autoImplicit false

universe u v r wR wS
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

/-- The recorded module category, as a transparent abbreviation.
Source: Stacks 06YY (blueprint: def-cbc-regular-quotient-cone-basic). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)

/-- The recorded restriction functor, as a transparent abbreviation.
Source: Stacks 03D7 (blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable abbrev restriction {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    Modules S ⥤ Modules R :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

/-- Multiplication by the compatible family of local scalars defining a global section.
Source: Stacks 06YP, principal-resolution construction
(blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable def scalar (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (Modules R) ⟶ 𝟭 (Modules R) where
  app M := { val := {
    app := fun U ↦ ModuleCat.ofHom (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (t.val U))
    naturality := by
      intro U V f
      ext x
      change t.val V • M.val.map f x = M.val.map f (t.val U • x)
      rw [M.val.map_smul]
      congr 1
      exact (t.property f).symm } }
  naturality {M N} f := by
    ext U x
    change t.val U • f.val.app U x = f.val.app U (t.val U • x)
    exact ((f.val.app U).hom.map_smul (t.val U) x).symm

/-- The map of unit modules induced by the ring-sheaf map.
Source: Stacks 06YP, principal-resolution construction
(blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable def ringMap {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    unit (derivedChangeRingIndependentCoefficients J R) ⟶
      (restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) :=
  ((restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S))).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : S.obj.obj U))
      (fun {_ _} f ↦ map_one (S.obj.map f).hom))

/-- Multiplication by the global section on an unbounded cochain complex.
Source: Stacks 06YP, principal-resolution construction
(blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable def complexScalar (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (CochainComplex (Modules R) ℤ) ⟶ 𝟭 (CochainComplex (Modules R) ℤ) where
  app P := {
    f := fun n ↦ (scalar R t).app (P.X n)
    comm' := fun i j _ ↦ ((scalar R t).naturality (P.d i j)).symm }
  naturality {_P _Q} f := by
    ext n : 1
    exact (scalar R t).naturality (f.f n)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- The strict cone functor, with diagonal action on chain maps.
Source: Stacks 06YP, principal quotient construction
(blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable def cone (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ where
  obj P := CochainComplex.mappingCone ((complexScalar R t).app P)
  map {_P _Q} h := CochainComplex.mappingCone.map _ _ h h
    ((complexScalar R t).naturality h).symm
  map_id _P := CochainComplex.mappingCone.map_id _
  map_comp _f _g := CochainComplex.mappingCone.map_comp _ _ _ _ _ _ _ _ _

/-- The canonical inclusion into the unshifted summand of the cone.
Source: Stacks 06YP (blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable def inclusion (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (CochainComplex (Modules R) ℤ) ⟶ cone R t where
  app P := CochainComplex.mappingCone.inr ((complexScalar R t).app P)
  naturality {P Q} h := by
    ext n : 1
    simp [cone, CochainComplex.mappingCone.map]

end SheafOfModules.RegularQuotientCone
