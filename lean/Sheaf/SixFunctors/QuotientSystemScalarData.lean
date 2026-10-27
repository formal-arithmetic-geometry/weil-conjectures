module

public import Sheaf.Paper.AugmentedDiagramProjectionMate
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Universal coefficient-system scalar models

Source: Stacks 06YY, 07A4, 07A6, 0D6D and 0D6E on the small ringed diagram sites
(blueprint: def-sfb-quotient-system-scalar-data).

This packages universal coefficient reduction and its canonical tensor/direct-image
comparisons. The predicate records the normalizations; no existence is assumed here.

## Main definitions and statements

* `Systems` and `scalar`: the existing strict module category and its free scalar functor.
* `ScalarModel`: universal derived scalar extension with its normalized restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
universe uC vC uD vD r wY wX wTY wTX wQY wQX wLY wLX
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.CochainPullback CategoryTheory.StrictReduction
namespace CategoryTheory.QuotientProjection
universe o0 v0 o1 v1 o2 v2 o3 v3 o4 v4 o5 v5 o6 v6 o7 v7 o8 v8 o9 v9

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
/-- Pointwise tensor on strict towers preserves finite colimits.
Source: Stacks 02MZ and 03EK
(blueprint: def-sfb-quotient-system-scalar-data). -/
instance towerTensorFiniteColimits (Q : ℕᵒᵖ ⥤ Modules R) :
    PreservesFiniteColimits (tensorLeft Q) where
  preservesFiniteColimits L := preservesColimitsOfShape_of_evaluation _ L (fun n ↦
    inferInstanceAs (PreservesColimitsOfShape L
      ((evaluation ℕᵒᵖ (Modules R)).obj n ⋙ tensorLeft (Q.obj n))))

/-- The free-module functor is additive, by its underlying tensor functor.
Source: Stacks 03EK (blueprint: def-sfb-quotient-system-scalar-data). -/
instance freeAdditive (Q : ℕᵒᵖ ⥤ Modules R) [MonObj Q] : (Mod.free Q).Additive where
  map_add {_ _} g h := Mod.hom_ext _ _ ((tensorLeft Q).map_add (f := g) (g := h))

/-- Strict semilinear coefficient systems, as internal modules on the diagram topos.
The action is a natural transformation, so every transition is semilinear.
Source: Stacks 0D6E on diagram sites
(blueprint: def-sfb-quotient-system-scalar-data). -/
abbrev Systems (Q : ℕᵒᵖ ⥤ Modules R) [MonObj Q] := Mod (ℕᵒᵖ ⥤ Modules R) Q

/-- Ordinary scalar extension of a constant system, using left modules.
The symmetry identifies its underlying Q ⊗ ΔM with ΔM ⊗ Q.
Source: Stacks 06YY (blueprint: def-sfb-quotient-system-scalar-data). -/
abbrev scalar (Q : ℕᵒᵖ ⥤ Modules R) [MonObj Q] := Functor.const ℕᵒᵖ ⋙ Mod.free Q

variable (Q : ℕᵒᵖ ⥤ Modules R) [MonObj Q]
  [HasDerivedCategory.{wY} (Modules R)]
  [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{wQY} (Systems Q)]

/-- The ordinary underlying scalar-extension identification, including all transitions.
Source: Stacks 06YY (blueprint: def-sfb-quotient-system-scalar-data). -/
def scalarUnderlying : scalar Q ⋙ Mod.forget Q ≅ reduction Q :=
  Functor.isoWhiskerLeft (Functor.const ℕᵒᵖ) (BraidedCategory.tensorLeftIsoTensorRight Q)

/-- Universal unbounded coefficient-valued reduction with its canonical comparison to
an ambient strict reduction model. The last equation fixes this comparison on all
flat-term K-flat representatives; it is not a choice of a lift of an ambient arrow.
Source: Stacks 06YY, 06XN and 07A4 on diagram sites
(blueprint: def-sfb-quotient-system-scalar-data). -/
structure ScalarModel (e : (Functor.const ℕᵒᵖ).obj (𝟙_ (Modules R)) ⟶ Q)
    (M : RingedModel Q e) where
  B : DerivedCategory (Modules R) ⥤ DerivedCategory (Systems Q)
  counit : DerivedCategory.Q ⋙ B ⟶
    (scalar Q).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : B.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ))
  computes : ∀ P : CochainComplex (Modules R) ℤ,
    flatRepresentatives R P → IsIso (counit.app P)
  underlying : B ⋙ (Mod.forget Q).mapDerivedCategory ≅ M.B
  normalization : ∀ P : CochainComplex (Modules R) ℤ, flatRepresentatives R P →
    underlying.hom.app (DerivedCategory.Q.obj P) ≫ M.counit.app P =
      (Mod.forget Q).mapDerivedCategory.map (counit.app P) ≫
        (Mod.forget Q).mapDerivedCategoryFactors.hom.app
          (((scalar Q).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (scalarUnderlying Q)
          (.up ℤ)).hom.app P)

end CategoryTheory.QuotientProjection
