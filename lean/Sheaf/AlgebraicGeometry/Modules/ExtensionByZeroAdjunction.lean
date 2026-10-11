/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Extension by zero of modules on an open subscheme

Source: Stacks Project, Definition 00A4 and Lemma 00A7
(blueprint: lem-weil-pbc-module-extension-by-zero-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Extension by zero is additive, canonically left adjoint to restriction, and has the
expected stalks. Modules on `U` are represented on the localized opens site using
`overEquiv U`. The direct sum has one summand when `V ≤ U` and no summands otherwise.
The adjunction formula on each summand specifies the map induced by sheafification.
Source: Stacks Project, Definition 00A4 (1),(2),(5),(6), Lemma 00A7 (2),(3)
(blueprint: lem-weil-pbc-module-extension-by-zero-adjunction).

Proof: (1) The presheaf restrictions are those of the input on opens contained in `U`,
and zero otherwise; their functor laws and semilinearity follow sectionwise.
(2) Sheafification gives the induced morphisms, with functoriality and additivity by
uniqueness of factorization (`def-weil-presheaf-modules-sheafification`).
(3) A presheaf morphism out of this extension is exactly a morphism on `U`: extend its
components by zero outside `U`. These constructions are inverse and natural.
(4) Compose that bijection with the sheafification universal property to get the stated
adjunction, whose component formula is composition with the sheafification map.
(5) Outside `U` every neighbourhood has zero sections of the extension presheaf; inside
`U`, neighbourhoods contained in `U` are cofinal, so its stalk is the input stalk.
The identification is linear on germs and natural in the input (`def-weil-pbc-module-stalk`).
(6) Sheafification induces an isomorphism on stalks
(`lem-weil-pbc-stalk-sheafification-space`); composing gives the canonical stalk map `t` below.
Its linearity follows from semilinearity of the sheafification map on sections, and its
naturality in the input (the last clause) from naturality of the adjunction unit,
`overFunctorEquiv` and `restrictStalkNatIso`. -/
theorem module_extensionByZero_adjunction (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    L.Additive ∧
      ∃ adj : L ⊣ SheafOfModules.overFunctor R U,
        (∀ (F : SheafOfModules.{u} (R.over U)) (G : X.Modules)
          (ψ : L.obj F ⟶ G) (V : X.Opens) (h : V ⟶ U)
          (s : F.val.obj (op (Over.mk h))),
          ((adj.homEquiv F G ψ).val.app (op (Over.mk h))) s =
            (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) ψ).app (op V)
              (DirectSum.of (fun φ : V ⟶ U => F.val.obj (op (Over.mk φ))) h s)) ∧
        (∀ (F : SheafOfModules.{u} (R.over U)) (x : X), x ∉ U →
          IsZero (TopCat.Presheaf.stalk (L.obj F).val.presheaf x)) ∧
        let t : ∀ (F : SheafOfModules.{u} (R.over U)) (x : U),
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
                ((toPresheaf U.toScheme).obj ((overEquiv U).functor.obj F)) ⟶
              (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
                (U.ι x)).obj (L.obj F) := fun F x =>
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              ((toPresheaf U.toScheme).map ((overEquiv U).functor.map (adj.unit.app F) ≫
                (overFunctorEquiv U).hom.app (L.obj F))) ≫
            (restrictStalkNatIso U.ι x).hom.app (L.obj F)
        (∀ (F : SheafOfModules.{u} (R.over U)) (x : U),
          letI : Module (U.toScheme.presheaf.stalk x)
              (((overEquiv U).functor.obj F).presheaf.stalk x) :=
            inferInstanceAs (Module (U.toScheme.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk ((overEquiv U).functor.obj F).val.presheaf x))
          letI : Module (X.presheaf.stalk (U.ι x))
              ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
                (U.ι x)).obj (L.obj F)) :=
            inferInstanceAs (Module (X.presheaf.stalk (U.ι x))
            ↑(TopCat.Presheaf.stalk (L.obj F).val.presheaf (U.ι x)))
          IsIso (t F x) ∧
            ∀ (r : X.presheaf.stalk (U.ι x))
              (s : ((overEquiv U).functor.obj F).presheaf.stalk x),
              t F x ((U.ι.stalkMap x) r • s) = r • t F x s) ∧
        (∀ (F F' : SheafOfModules.{u} (R.over U)) (α : F ⟶ F') (x : U),
          t F x ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι x)).map
              ((toPresheaf X).map (L.map α)) =
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              ((toPresheaf U.toScheme).map ((overEquiv U).functor.map α)) ≫ t F' x) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
