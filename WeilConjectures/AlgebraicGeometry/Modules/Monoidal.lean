/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# The symmetric monoidal structure on sheaves of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)`, and let
`R' := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R` be the underlying sheaf of rings.
The category `PresheafOfModules R'.obj` of presheaves of modules is symmetric monoidal, the
tensor product being computed sectionwise, and the sheafification functor
`PresheafOfModules R'.obj ⥤ SheafOfModules R'` is a localization functor which inverts a
monoidal class of morphisms. We may therefore transport the symmetric monoidal structure to
`SheafOfModules R'`: the tensor product of two sheaves of modules is the sheafification of the
presheaf tensor product.

## Main results

- `SheafOfModules.monoidalCategory`, `SheafOfModules.braidedCategory` and
  `SheafOfModules.symmetricCategory`: the symmetric monoidal structure on `SheafOfModules R'`,
  for which the sheafification functor `SheafOfModules.sheafification R` is monoidal and braided.
- `SheafOfModules.tensorUnitIso`: the tensor unit is the free sheaf of modules of rank one.
- `SheafOfModules.tensorIsoOfIsLocallyBijective`: a locally bijective morphism `P ⊗ Q ⟶ S` from
  the sectionwise tensor product of two presheaves of modules identifies the tensor product of
  the sheafifications of `P` and `Q` with the sheafification of `S`.
- `AlgebraicGeometry.Scheme.Modules.monoidalCategory`,
  `AlgebraicGeometry.Scheme.Modules.braidedCategory` and
  `AlgebraicGeometry.Scheme.Modules.symmetricCategory`: the corresponding structures on the
  category `X.Modules` of `𝒪ₓ`-modules over a scheme `X`.

-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v₁ u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- The sheafification functor from presheaves of modules over the underlying presheaf of rings
of a sheaf of commutative rings `R` to sheaves of modules over `R`. This is
`PresheafOfModules.sheafification` for the identity of the underlying presheaf of rings; it is
spelled with the domain `PresheafOfModules (R.obj ⋙ forget₂ _ _)` so that the monoidal structure
on presheaves of modules is found by instance resolution. -/
noncomputable abbrev sheafification :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u}) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) :=
  PresheafOfModules.sheafification (𝟙 _)

/-- Sheafifying the underlying presheaf of modules of a sheaf of modules `F` gives `F` back.
This is the counit of the sheafification adjunction,
`PresheafOfModules.sheafificationCounitIso`, evaluated at `F`. -/
noncomputable def sheafificationObjIso
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (sheafification R).obj
      ((SheafOfModules.forget
        ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)).obj F) ≅ F :=
  (PresheafOfModules.sheafificationCounitIso
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R).obj)).app F

/-- The monoidal category structure on the category of sheaves of modules over a sheaf of
commutative rings `R`, obtained by localizing the monoidal category structure on presheaves of
modules along the sheafification functor.

Unlike its analogue `CategoryTheory.Sheaf.monoidalCategory` for sheaves with values in a fixed
monoidal category, which is an `@[instance_reducible] def`, this is a genuine instance: instance
resolution does find it downstream, in particular for `AlgebraicGeometry.Scheme.Modules`. -/
noncomputable instance monoidalCategory :
    MonoidalCategory
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal (L := sheafification R)
    (W := J.W.inverseImage
      (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat RingCat.{u}))) (Iso.refl _)))

/-- The monoidal structure on sheaves of modules is braided. -/
noncomputable instance braidedCategory :
    BraidedCategory
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :=
  inferInstanceAs (BraidedCategory (LocalizedMonoidal (L := sheafification R)
    (W := J.W.inverseImage
      (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat RingCat.{u}))) (Iso.refl _)))

/-- The monoidal structure on sheaves of modules is symmetric. -/
noncomputable instance symmetricCategory :
    SymmetricCategory
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal (L := sheafification R)
    (W := J.W.inverseImage
      (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat RingCat.{u}))) (Iso.refl _)))

/-- The sheafification functor is monoidal. -/
noncomputable instance : (sheafification R).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory (L := sheafification R)
    (W := J.W.inverseImage
      (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat RingCat.{u})))
    (Iso.refl _)).Monoidal

/-- The sheafification functor is braided. -/
noncomputable instance : (sheafification R).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory (L := sheafification R)
    (W := J.W.inverseImage
      (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat RingCat.{u})))
    (Iso.refl _)).Braided

/-- The canonical morphism from the sheafification of the free presheaf of modules of rank one
to the free sheaf of modules of rank one. The tensor unit of `SheafOfModules R'` is the source of
this morphism by construction, see `SheafOfModules.tensorUnitIso`. -/
noncomputable def unitHom :
    (sheafification R).obj
        (PresheafOfModules.unit (R.obj ⋙ forget₂ CommRingCat RingCat.{u})) ⟶
      unit ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) :=
  (PresheafOfModules.sheafificationHomEquiv
    (P := PresheafOfModules.unit (R.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (F := unit ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (𝟙 (R.obj ⋙ forget₂ CommRingCat RingCat.{u}))).symm (𝟙 _)

instance : IsIso (unitHom R) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (P := PresheafOfModules.unit (R.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (F := unit ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (𝟙 (R.obj ⋙ forget₂ CommRingCat RingCat.{u})) (unitHom R)
  rw [show PresheafOfModules.sheafificationHomEquiv
        (P := PresheafOfModules.unit (R.obj ⋙ forget₂ CommRingCat RingCat.{u}))
        (F := unit ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
        (𝟙 (R.obj ⋙ forget₂ CommRingCat RingCat.{u})) (unitHom R) = 𝟙 _ from
      (PresheafOfModules.sheafificationHomEquiv _).apply_symm_apply _,
      CategoryTheory.Functor.map_id] at h
  have h₁ : IsIso (CategoryTheory.toSheafify J
      (PresheafOfModules.unit (R.obj ⋙ forget₂ CommRingCat RingCat.{u})).presheaf) :=
    CategoryTheory.isIso_toSheafify J
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)).isSheaf
  have h₂ : IsIso ((PresheafOfModules.toPresheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R).obj).map (unitHom R).val) := by
    rw [← IsIso.inv_eq_of_hom_inv_id h.symm]
    infer_instance
  have h₃ : IsIso (unitHom R).val := isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  have h₄ : IsIso ((forget ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)).map
    (unitHom R)) := h₃
  exact isIso_of_reflects_iso _ (forget _)

/-- The tensor unit of `SheafOfModules R'` is the free sheaf of modules of rank one. -/
noncomputable def tensorUnitIso :
    𝟙_ (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) ≅
      unit ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) :=
  asIso (unitHom R)

variable {R}

/-- **Recognising a tensor product of sheaves of modules.** Let `φ : P ⊗ Q ⟶ S` be a locally
bijective morphism out of the sectionwise tensor product of two presheaves of modules, and let
`eF`, `eG`, `eH` identify the sheafifications of `P`, `Q`, `S` with sheaves of modules `F`, `G`,
`H`. Then `φ` identifies `F ⊗ G` with `H`:

```text
                   μ                  a φ
  a P ⊗ a Q ──────────────→ a (P ⊗ Q) ─────→ a S
      │                                       │
      │ eF ⊗ eG                               │ eH
      ↓                                       ↓
    F ⊗ G ────────────────────────────────────→ H
```

Here `a` is the sheafification functor `SheafOfModules.sheafification R` and `μ` is its monoidal
structure. -/
noncomputable def tensorIsoOfIsLocallyBijective
    {P Q S : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u})}
    {F G H : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (eF : (sheafification R).obj P ≅ F) (eG : (sheafification R).obj Q ≅ G)
    (eH : (sheafification R).obj S ≅ H) (φ : P ⊗ Q ⟶ S)
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat.{u})).map φ)]
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat.{u})).map φ)] :
    F ⊗ G ≅ H :=
  have : IsIso ((sheafification R).map φ) :=
    PresheafOfModules.isIso_sheafification_map J _ φ (J.W_of_isLocallyBijective _)
  tensorIso eF.symm eG.symm ≪≫ Functor.Monoidal.μIso (sheafification R) P Q ≪≫
    asIso ((sheafification R).map φ) ≪≫ eH

/-- `SheafOfModules.tensorIsoOfIsLocallyBijective` is the isomorphism induced by `φ`: this
records the four steps of the diagram in its definition. -/
theorem tensorIsoOfIsLocallyBijective_hom
    {P Q S : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u})}
    {F G H : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (eF : (sheafification R).obj P ≅ F) (eG : (sheafification R).obj Q ≅ G)
    (eH : (sheafification R).obj S ≅ H) (φ : P ⊗ Q ⟶ S)
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat.{u})).map φ)]
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat.{u})).map φ)] :
    (tensorIsoOfIsLocallyBijective eF eG eH φ).hom =
      (tensorIso eF.symm eG.symm).hom ≫ (Functor.Monoidal.μIso (sheafification R) P Q).hom ≫
        (sheafification R).map φ ≫ eH.hom :=
  rfl

end SheafOfModules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The category of `𝒪ₓ`-modules over a scheme `X` is monoidal, the tensor product being the
sheafification of the presheaf tensor product. -/
noncomputable instance Modules.monoidalCategory : MonoidalCategory X.Modules :=
  inferInstanceAs (MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf))

/-- The tensor product of `𝒪ₓ`-modules is braided. -/
noncomputable instance Modules.braidedCategory : BraidedCategory X.Modules :=
  inferInstanceAs (BraidedCategory (SheafOfModules.{u} X.ringCatSheaf))

/-- The tensor product of `𝒪ₓ`-modules is symmetric. -/
noncomputable instance Modules.symmetricCategory : SymmetricCategory X.Modules :=
  inferInstanceAs (SymmetricCategory (SheafOfModules.{u} X.ringCatSheaf))

end AlgebraicGeometry.Scheme

