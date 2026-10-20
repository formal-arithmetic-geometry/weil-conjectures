module
public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
/-- Construction after supplying the quasi-coherence fields.
Source: Stacks Project, Tags 079W and 08FE; perfect.tex, Tag 09RE.
Proof: construct the restricted stage and limit representing objects from the
adjunctions for open restriction, transport their Hom equivalences through the
canonical pullback comparison maps, and define the transition and cocone maps
by evaluation at identity morphisms. Naturality and the cocone laws follow from
the corresponding comparison identities; the two supplied quasi-coherence
fields provide the required QCoh fields. This construction is left as the
named theorem represented by this node.
(blueprint: new-perfect-hom-open-restricted-core). -/
theorem perfect_hom_open_restricted_core_exists
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d)
    (hStage : ∀ j : Set.Ici i, schemeDerivedQCohProperty B.toScheme
      ((F ⋙ schemeMVDerivedRestriction Y B).obj j))
    (hLimit : schemeDerivedQCohProperty B.toScheme
      ((schemeMVDerivedRestriction Y B).obj d.pt)) :
    Nonempty (PerfectHomPushPullData R c (B.ι ≫ s)
      ((schemeMVDerivedRestriction Y B).obj Q)
      (F ⋙ schemeMVDerivedRestriction Y B)
      ((schemeMVDerivedRestriction Y B).mapCocone d)) := by
  obtain ⟨e⟩ := perfect_hom_open_restricted_equiv_fields_exists R c s B Q F d h
  exact perfect_hom_open_restricted_maps_exists R c s B Q F d h hStage hLimit e
end
end AlgebraicGeometry
