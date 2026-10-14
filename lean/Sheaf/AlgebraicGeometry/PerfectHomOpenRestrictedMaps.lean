module
public import Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedEquivFields
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
/-- Assemble the transition and cocone compatibility fields from restricted Hom
naturality. Source: Stacks Project, Tags 079W and 08FE; perfect.tex, Tag 09RE.
(blueprint: new-perfect-hom-open-restricted-maps). -/
theorem perfect_hom_open_restricted_maps_exists
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d)
    (hStage : ∀ j : Set.Ici i, schemeDerivedQCohProperty B.toScheme
      ((F ⋙ schemeMVDerivedRestriction Y B).obj j))
    (hLimit : schemeDerivedQCohProperty B.toScheme
      ((schemeMVDerivedRestriction Y B).obj d.pt))
    (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d) :
    Nonempty (PerfectHomPushPullData R c (B.ι ≫ s)
      ((schemeMVDerivedRestriction Y B).obj Q)
      (F ⋙ schemeMVDerivedRestriction Y B)
      ((schemeMVDerivedRestriction Y B).mapCocone d)) := by sorry
end
end AlgebraicGeometry
