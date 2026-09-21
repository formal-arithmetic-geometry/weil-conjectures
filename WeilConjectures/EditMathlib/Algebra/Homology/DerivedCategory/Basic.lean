/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # An opaque version of the derived category of an abelian category

`DerivedCategory C` is a type synonym for `HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`,
and mathlib exposes that definition: the whole file
`Mathlib/Algebra/Homology/DerivedCategory/Basic.lean` lives in an `@[expose] public section`.
As a consequence the elaborator happily unfolds `DerivedCategory C`, and with it the whole tower
`HomologicalComplexUpToQuasiIso`, `MorphismProperty.Localization'`,
`MorphismProperty.HasLocalization.D`, whenever it has to solve a unification problem it cannot
solve otherwise. This is a source of slowdowns, of confusing error messages, and of proofs that
hold by `rfl` only because of the particular way the localized category happens to be chosen.

In this file we introduce `DerivedCategory' C`, a `@[no_expose]` wrapper around
`DerivedCategory C`: definitionally the same type, but with its body invisible outside of this
module. Downstream, `DerivedCategory' C` can therefore only be manipulated through the API below,
which ports the basic API of `DerivedCategory`:

* `DerivedCategory'.Q : CochainComplex C ℤ ⥤ DerivedCategory' C` is a localization functor for
  the quasi-isomorphisms `HomologicalComplex.quasiIso C (ComplexShape.up ℤ)`;
* `DerivedCategory'.Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory' C` is a
  localization functor for `HomotopyCategory.quasiIso C (ComplexShape.up ℤ)`, equivalently for
  `(HomotopyCategory.subcategoryAcyclic C).trW`;
* `DerivedCategory'.quotientCompQhIso` relates the two;
* `DerivedCategory' C` is a triangulated category, `Q` and `Qh` are additive and essentially
  surjective, `Qh` is triangulated, and `DerivedCategory'.mem_distTriang_iff` describes the
  distinguished triangles;
* `DerivedCategory'.singleFunctors` are the single functors `C ⥤ DerivedCategory' C`.

Since the two types are definitionally equal *inside* this file, all of this is transported from
`DerivedCategory` for free; only the statements below are visible downstream.

## Implementation notes

The definition of `DerivedCategory'` sits in a nested `@[expose] section` so that the
`@[no_expose]` attribute on it is meaningful. The rest of the file is *not* exposed, which is
what allows the declarations below to be defined by transport along the (locally available)
definitional equality `DerivedCategory' C = DerivedCategory C`.

Two definitions are exceptions and carry `@[expose]`: `Qh` and, building on it, `singleFunctors`
(together with the isomorphisms relating them to `Q`). They are built *intrinsically* — `Qh` as
the functor induced by `Q` on the homotopy category, via `CategoryTheory.Quotient.lift` — so
their bodies never mention `DerivedCategory` and can be exposed even though `DerivedCategory'`
cannot. This matters downstream: it keeps
`HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh` definitionally equal to `Q`, which a
number of constructions in the mathlib files below this one rely on.

`Q` itself is irreducibly non-exposed: a functor into the opaque type `DerivedCategory' C` can
only be produced by transport. So any downstream construction that mathlib obtains by unfolding
`DerivedCategory` down to `HomologicalComplexUpToQuasiIso` has to be redone through the
universal property of `Q` (`Localization.lift`, `Localization.fac`, …).

For interoperability with the mathlib API,
`DerivedCategory'.equivDerivedCategory : DerivedCategory' C ≌ DerivedCategory C` is provided.
It is the identity equivalence, but it has to be used explicitly.
-/

public section

universe w v u

open CategoryTheory Limits Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

@[expose] section

/-- The derived category of an abelian category, as an opaque wrapper around
`DerivedCategory C`. Contrary to `DerivedCategory C`, this definition is not exposed, so that
the elaborator never unfolds it to the underlying localized category of cochain complexes. -/
@[no_expose] def DerivedCategory' : Type (max u v) := DerivedCategory C

end

noncomputable section

namespace DerivedCategory'

instance : Category.{w} (DerivedCategory' C) := inferInstanceAs (Category (DerivedCategory C))

/-- The tautological equivalence `DerivedCategory' C ≌ DerivedCategory C`. This is the identity
equivalence, but as `DerivedCategory'` is not exposed, it has to be used explicitly in order to
transport statements from one category to the other. -/
def equivDerivedCategory : DerivedCategory' C ≌ DerivedCategory C := .refl

variable {C}

/-- The localization functor `CochainComplex C ℤ ⥤ DerivedCategory' C`. -/
def Q : CochainComplex C ℤ ⥤ DerivedCategory' C := DerivedCategory.Q

set_option backward.isDefEq.respectTransparency false in
instance : (Q (C := C)).IsLocalization
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  inferInstanceAs (DerivedCategory.Q.IsLocalization _)

instance {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    IsIso (Q.map f) :=
  Localization.inverts Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _
    (inferInstanceAs (QuasiIso f))

lemma Q_map_eq_of_homotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    (Q (C := C)).map f = Q.map g :=
  HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy h

/-- The localization functor `HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory' C`.

Contrary to `Q`, this is defined *intrinsically* from `Q` (as the functor induced on the
homotopy category), rather than by transport from `DerivedCategory.Qh`. This makes it possible
to expose it, so that `HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh` is still
definitionally `Q` downstream. -/
@[expose] def Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory' C :=
  CategoryTheory.Quotient.lift _ Q (by
    rintro K L f g ⟨h⟩
    exact Q_map_eq_of_homotopy h)

variable (C) in
/-- The natural isomorphism `HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q`. -/
@[expose] def quotientCompQhIso :
    HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q :=
  CategoryTheory.Quotient.lift.isLift _ _ _

@[reassoc (attr := simp)]
lemma quotientCompQhIso_hom_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Qh.map ((HomotopyCategory.quotient _ _).map f) ≫ (quotientCompQhIso C).hom.app L =
      (quotientCompQhIso C).hom.app K ≫ Q.map f :=
  (quotientCompQhIso C).hom.naturality f

@[reassoc]
lemma quotientCompQhIso_inv_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Q.map f ≫ (quotientCompQhIso C).inv.app L =
      (quotientCompQhIso C).inv.app K ≫ Qh.map ((HomotopyCategory.quotient _ _).map f) :=
  (quotientCompQhIso C).inv.naturality f

instance : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh).IsLocalization
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  Functor.IsLocalization.of_iso _ (quotientCompQhIso C).symm

instance : (Qh (C := C)).IsLocalization (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  Functor.IsLocalization.of_comp (HomotopyCategory.quotient C (ComplexShape.up ℤ)) Qh
    (HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (homotopyEquivalences_le_quasiIso C (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso_eq_quasiIso_map_quotient C (ComplexShape.up ℤ))
instance : Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).trW := by
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

instance : Preadditive (DerivedCategory' C) :=
  Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).trW

instance : (Qh (C := C)).Additive :=
  Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic C).trW

instance : (Q (C := C)).Additive :=
  Functor.additive_of_iso (quotientCompQhIso C)

instance : HasZeroObject (DerivedCategory' C) :=
  Q.hasZeroObject_of_additive

instance : HasShift (DerivedCategory' C) ℤ :=
  HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW ℤ

instance : (Qh (C := C)).CommShift ℤ :=
  Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW ℤ

instance : (Q (C := C)).CommShift ℤ :=
  Functor.CommShift.ofIso (quotientCompQhIso C) ℤ

instance : NatTrans.CommShift (quotientCompQhIso C).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (quotientCompQhIso C) ℤ

instance (n : ℤ) : (shiftFunctor (DerivedCategory' C) n).Additive := by
  rw [Localization.functor_additive_iff Qh (HomotopyCategory.subcategoryAcyclic C).trW]
  exact Functor.additive_of_iso (Qh.commShiftIso n)

instance : Pretriangulated (DerivedCategory' C) :=
  Triangulated.Localization.pretriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

instance : (Qh (C := C)).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

instance : IsTriangulated (DerivedCategory' C) :=
  Triangulated.Localization.isTriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic C).trW

instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (Qh (C := C))).Full :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Full

instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (Qh (C := C))).Faithful :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Faithful

instance : (Qh : _ ⥤ DerivedCategory' C).EssSurj :=
  Localization.essSurj _ (HomotopyCategory.quasiIso _ _)

instance : (Q : _ ⥤ DerivedCategory' C).EssSurj :=
  Localization.essSurj _ (HomologicalComplex.quasiIso _ _)

lemma mem_distTriang_iff (T : Triangle (DerivedCategory' C)) :
    (T ∈ distTriang (DerivedCategory' C)) ↔ ∃ (X Y : CochainComplex C ℤ) (f : X ⟶ Y),
      Nonempty (T ≅ Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) := by
  constructor
  · rintro ⟨T', e, ⟨X, Y, f, ⟨e'⟩⟩⟩
    refine ⟨_, _, f, ⟨?_⟩⟩
    exact e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (quotientCompQhIso C)).app _
  · rintro ⟨X, Y, f, ⟨e⟩⟩
    refine isomorphic_distinguished _ (Qh.map_distinguished _ ?_) _
      (e ≪≫ (Functor.mapTriangleIso (quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).app _)
    exact ⟨_, _, f, ⟨Iso.refl _⟩⟩

section

open CochainComplex

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

lemma mappingCone_triangle_distinguished :
    (Q (C := C)).mapTriangle.obj (mappingCone.triangle φ) ∈ distTriang _ := by
  rw [mem_distTriang_iff]
  exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

lemma mappingCocone_triangle_distinguished :
    (Q (C := C)).mapTriangle.obj (mappingCocone.triangle φ) ∈ distTriang _ := by
  rw [rotate_distinguished_triangle]
  exact isomorphic_distinguished _ (mappingCone_triangle_distinguished φ) _
    ((Q (C := C)).mapTriangleRotateIso.app _ ≪≫
      (Q (C := C)).mapTriangle.mapIso (mappingCocone.rotateTriangleIso φ))

end

variable (C)

/-- The single functors `C ⥤ DerivedCategory' C` for all `n : ℤ` along with
their compatibilities with shifts. -/
@[expose] def singleFunctors : SingleFunctors C (DerivedCategory' C) ℤ :=
  (HomotopyCategory.singleFunctors C).postcomp Qh

/-- The single functor `C ⥤ DerivedCategory' C` which sends `X : C` to the
single cochain complex with `X` sitting in degree `n : ℤ`. -/
abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

set_option backward.defeqAttrib.useBackward true in
instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

-- The object level definitional equality underlying `singleFunctorsPostcompQhIso`.
@[simp] theorem Qh_obj_singleFunctors_obj (n : ℤ) (X : C) :
    Qh.obj (((HomotopyCategory.singleFunctors C).functor n).obj X) = (singleFunctor C n).obj X :=
  rfl

@[simp] theorem Q_obj_single_obj (n : ℤ) (X : C) :
    Q.obj ((HomologicalComplex.single C _ n).obj X) = (singleFunctor C n).obj X :=
  rfl

/-- The isomorphism `singleFunctor C n ≅ HomotopyCategory.singleFunctor C n ⋙ Qh`. -/
@[expose] def singleFunctorIsoCompQh (n : ℤ) :
    singleFunctor C n ≅ HomotopyCategory.singleFunctor C n ⋙ Qh := Iso.refl _

/-- The isomorphism
`DerivedCategory'.singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postcomp Qh` given
by the definition of `DerivedCategory'.singleFunctors`. -/
@[expose] def singleFunctorsPostcompQhIso :
    singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postcomp Qh :=
  Iso.refl _

/-- The isomorphism
`DerivedCategory'.singleFunctors C ≅ (CochainComplex.singleFunctors C).postcomp Q`. -/
@[expose] def singleFunctorsPostcompQIso :
    singleFunctors C ≅ (CochainComplex.singleFunctors C).postcomp Q :=
  (SingleFunctors.postcompFunctor C ℤ (Qh : _ ⥤ DerivedCategory' C)).mapIso
    (HomotopyCategory.singleFunctorsPostcompQuotientIso C) ≪≫
      (CochainComplex.singleFunctors C).postcompPostcompIso (HomotopyCategory.quotient _ _) Qh ≪≫
      SingleFunctors.postcompIsoOfIso
        (CochainComplex.singleFunctors C) (quotientCompQhIso C)

/-- The isomorphism `singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q`. -/
@[expose] def singleFunctorIsoCompQ (n : ℤ) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma singleFunctorsPostcompQIso_hom_hom (n : ℤ) :
    (singleFunctorsPostcompQIso C).hom.hom n = 𝟙 _ := by
  ext X
  dsimp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    quotientCompQhIso]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma singleFunctorsPostcompQIso_inv_hom (n : ℤ) :
    (singleFunctorsPostcompQIso C).inv.hom n = 𝟙 _ := by
  ext X
  simp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso]
  rfl

variable {C}

lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ QuasiIso φ :=
  HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso φ

end DerivedCategory'

end
