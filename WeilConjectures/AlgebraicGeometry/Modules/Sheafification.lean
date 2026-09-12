/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Monoidal

/-!
# Comparing the tensor product of sheaves of modules with the sectionwise tensor product

Let `R` be a sheaf of commutative rings on a site `(C, J)`. The tensor product of two sheaves of
modules over `R` is the sheafification of the sectionwise tensor product of the underlying
presheaves of modules, see `WeilConjectures/AlgebraicGeometry/Modules/Monoidal.lean`. There is
therefore a canonical comparison morphism from the sectionwise tensor product of the underlying
presheaves of modules of `F` and `G` to the underlying presheaf of modules of `F ⊗ G`, and it
becomes an isomorphism after sheafification, i.e. it is locally bijective.

## Main declarations

- `SheafOfModules.sheafificationObjIso`: the sheafification of the underlying presheaf of modules
  of a sheaf of modules `F` is `F` itself.
- `SheafOfModules.tensorSheafificationIso`: the tensor product of two sheaves of modules is the
  sheafification of the sectionwise tensor product of the underlying presheaves of modules.
- `SheafOfModules.tensorPresheafHom`: the comparison morphism from the sectionwise tensor
  product of the underlying presheaves of modules of `F` and `G` to the underlying presheaf of
  modules of `F ⊗ G`, together with
  `SheafOfModules.W_toPresheaf_map_tensorPresheafHom`: it becomes an isomorphism after
  sheafification, hence is locally surjective over a topological space.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

universe v₁ u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- The underlying presheaf of modules of a sheaf of modules, spelled as a presheaf of modules
over the underlying presheaf of rings of `R`, so that the monoidal structure of
`PresheafOfModules` is found by instance resolution. -/
abbrev toPresheafOfModules
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (SheafOfModules.forget _).obj F

variable (R) in
/-- The sheafification of the underlying presheaf of modules of a sheaf of modules `F` is `F`
itself; this is the counit of the sheafification adjunction. -/
noncomputable def sheafificationObjIso
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (sheafification R).obj
      ((SheafOfModules.forget
        ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)).obj F) ≅ F :=
  asIso ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R).obj)).counit.app F)

variable (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))

/-- **The tensor product of two sheaves of modules is the sheafification of the sectionwise
tensor product** of the underlying presheaves of modules. -/
noncomputable def tensorSheafificationIso :
    (sheafification R).obj (toPresheafOfModules F ⊗ toPresheafOfModules G) ≅ F ⊗ G :=
  (Functor.Monoidal.μIso (sheafification R) _ _).symm ≪≫
    tensorIso (sheafificationObjIso R F) (sheafificationObjIso R G)

/-- The canonical morphism from the sectionwise tensor product of the underlying presheaves of
modules of `F` and `G` to the underlying presheaf of modules of `F ⊗ G`. -/
noncomputable def tensorPresheafHom :
    toPresheafOfModules F ⊗ toPresheafOfModules G ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).obj
          (toPresheafOfModules (F ⊗ G)) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj))).homEquiv _ _
      (tensorSheafificationIso F G).hom

/-- The comparison morphism `SheafOfModules.tensorPresheafHom` is, by construction, the transpose
of `SheafOfModules.tensorSheafificationIso` under the sheafification adjunction: on underlying
presheaves of abelian groups it is the composite of the unit of sheafification with (the
underlying morphism of presheaves of) that isomorphism.

```
                            toSheafify
F.presheaf ⊗ G.presheaf ----------------> sheafify (F.presheaf ⊗ G.presheaf)
           \                                         |
            \  tensorPresheafHom                     |  tensorSheafificationIso
             \                                       v
              -----------------------------> (F ⊗ G).presheaf
```
-/
lemma toPresheaf_map_tensorPresheafHom :
    (PresheafOfModules.toPresheaf _).map (tensorPresheafHom F G) =
      CategoryTheory.toSheafify J (toPresheafOfModules F ⊗ toPresheafOfModules G).presheaf ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
          (tensorSheafificationIso F G).hom := rfl

/-- The comparison morphism from the sectionwise tensor product to the tensor product becomes an
isomorphism after sheafification; in particular it is locally bijective. -/
lemma W_toPresheaf_map_tensorPresheafHom :
    J.W ((PresheafOfModules.toPresheaf _).map (tensorPresheafHom F G)) := by
  have h : J.W ((SheafOfModules.forget
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      PresheafOfModules.toPresheaf _).map (tensorSheafificationIso F G).hom) :=
    J.W.of_isIso _
  rw [toPresheaf_map_tensorPresheafHom]
  exact J.W.comp_mem _ _ (J.W_toSheafify _) h

end SheafOfModules
