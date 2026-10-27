/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorSection

/-! # Ordinary tensor comparison data with independent coefficient size

Source: Stacks 03EK, 03EL and 0G7E
(blueprint: def-sf-ordinary-tensor-pullback-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace WeilConjectures.SemilinearSections

/-- The usual sheafified pure tensor, at an independent coefficient size.
Source: Stacks 03EK (blueprint: def-sf-ordinary-tensor-pullback-data). -/
abbrev tensorSectionAtSize {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    (M N : Mod.{c, v, r} J R) (V : Cᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V) :
    ((SheafOfModules.monoidalCategory R).tensorObj M N).val.obj V :=
  SheafOfModules.sheafTensorSection R M N V x y

section Comparison
variable {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K]
  (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
  (phi : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{r} J K).obj S)
  (F : Mod.{c, v, r} J R ⥤ Mod.{c, v, r} K S) [F.Additive]
  (adj : F ⊣ SheafOfModules.pushforward.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map phi))

/-- The scalar-generator formula and two-variable naturality.
Source: Stacks 03EL (blueprint: def-sf-ordinary-tensor-pullback-data). -/
def OrdinaryTensorNormalized
    (e : ∀ M N : Mod.{c, v, r} J R,
      F.obj ((SheafOfModules.monoidalCategory R).tensorObj M N) ≅
        (SheafOfModules.monoidalCategory S).tensorObj (F.obj M) (F.obj N)) : Prop :=
  (∀ (M N : Mod.{c, v, r} J R) (V : C) (W : D) (p : W ⟶ U.obj V)
      (x : M.val.obj (op V)) (y : N.val.obj (op V)) (a : S.obj.obj (op W)),
    (e M N).hom.val.app (op W)
        (a • (F.obj ((SheafOfModules.monoidalCategory R).tensorObj M N)).val.map p.op
          ((adj.unit.app ((SheafOfModules.monoidalCategory R).tensorObj M N)).val.app
            (op V) (tensorSectionAtSize J R M N (op V) x y))) =
      tensorSectionAtSize K S (F.obj M) (F.obj N) (op W)
        (a • (F.obj M).val.map p.op ((adj.unit.app M).val.app (op V) x))
        ((F.obj N).val.map p.op ((adj.unit.app N).val.app (op V) y))) ∧
  ∀ (M M' N N' : Mod.{c, v, r} J R) (a : M ⟶ M') (b : N ⟶ N'),
    F.map ((SheafOfModules.monoidalCategory R).tensorHom a b) ≫ (e M' N').hom =
      (e M N).hom ≫ (SheafOfModules.monoidalCategory S).tensorHom (F.map a) (F.map b)

/-- The ordinary tensor comparison and preservation of flat-term representatives.
All remaining fields are propositions; normalization determines the ordinary isomorphisms.
Source: Stacks 03EL and 0G7E (blueprint: def-sf-ordinary-tensor-pullback-data). -/
structure OrdinaryTensorPullbackData where
  /-- The comparison on ordinary sheaf modules. -/
  ordinary : ∀ M N : Mod.{c, v, r} J R,
    F.obj ((SheafOfModules.monoidalCategory R).tensorObj M N) ≅
      (SheafOfModules.monoidalCategory S).tensorObj (F.obj M) (F.obj N)
  /-- Generator normalization and naturality. -/
  normalized : OrdinaryTensorNormalized J K U R S phi F adj ordinary
  /-- Preservation of the simultaneous flat-term K-flat representative class. -/
  flat : ∀ P : CochainComplex (Mod.{c, v, r} J R) ℤ,
    P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) →
    CochainComplex.IsKFlatIndependentCoefficients
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := S)
        (((F.mapHomologicalComplex (.up ℤ)).obj P).X n)
end Comparison
end WeilConjectures.SemilinearSections
