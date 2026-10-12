module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme
/-- Generic direct image and etale cohomology preserve the finite-stalk cocone.
Source: blueprint `lem-sc-affine-generic-second`, cohomology passage.
(blueprint: lem-sc-generic-torsion-finite-stalk-colimit-cohomology)
The generic point is affine and qcqs; sections are finite products of invariants, which commute
with the filtered union. The directed-colimit theorem for etale cohomology and the natural
Ext/derived comparison then identify the displayed mapped cocones as colimits.
-/
theorem generic_torsion_cohomology_colimit
    (X : Scheme.{u}) [IsIntegral X] [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}}
    {ι : F ⟶ (Functor.const I).obj M}
    (hι : Nonempty (IsColimit (Cocone.mk M ι))) :
    ∀ q : ℕ, Nonempty (IsColimit
      (((Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField) ⋙
        Sheaf.functorH X.smallEtaleTopology q).mapCocone (Cocone.mk M ι))) := by
  sorry
end AlgebraicGeometry.Scheme
