module
public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedCore
import Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedQCoh
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
/-- Existence of the restricted representing cocone. The construction is obtained by
restricting the adjunction-representing objects and transporting their maps across the
canonical open restriction comparisons described in the parent node.
Source: Stacks Project, Tags 079W and 08FE; perfect.tex, Tag 09RE.
(blueprint: lem-pc-perfect-hom-open-restricted-data-exists). -/
theorem perfect_hom_open_restricted_data_exists
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens)
    (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) :
    Nonempty (PerfectHomPushPullData R c (B.ι ≫ s)
      ((schemeMVDerivedRestriction Y B).obj Q) (F ⋙ schemeMVDerivedRestriction Y B)
      ((schemeMVDerivedRestriction Y B).mapCocone d)) := by
  obtain ⟨hqF, hqD⟩ := perfect_hom_open_restricted_qcoh R c s B Q F d h
  exact perfect_hom_open_restricted_core_exists R c s B Q F d h hqF hqD
end
end AlgebraicGeometry
