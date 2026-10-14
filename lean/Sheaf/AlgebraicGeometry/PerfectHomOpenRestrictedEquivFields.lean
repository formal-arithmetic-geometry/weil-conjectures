module
public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
/-- The Hom equivalence and testing-object naturality fields needed before the
transition and cocone maps are assembled. Source: Stacks Project, Tags 079W and
08FE; perfect.tex, Tag 09RE. (blueprint: new-perfect-hom-open-restricted-equiv-fields). -/
structure PerfectHomOpenRestrictedEquivFields
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F) where
  stageEquiv : ∀ (j : Set.Ici i) (M : schemeDerivedCategory B.toScheme),
    (M ⟶ (F ⋙ schemeMVDerivedRestriction Y B).obj j) ≃
      ((derivedPullback (pullback.fst (B.ι ≫ s)
        (Spec.map (R.map (homOfLE j.property))))).obj M ⟶
       (derivedPullback (pullback.fst (B.ι ≫ s)
        (Spec.map (R.map (homOfLE j.property))))).obj
          ((schemeMVDerivedRestriction Y B).obj Q))
  limitEquiv : ∀ (M : schemeDerivedCategory B.toScheme),
    (M ⟶ (schemeMVDerivedRestriction Y B).obj d.pt) ≃
      ((derivedPullback (pullback.fst (B.ι ≫ s) (Spec.map (c.ι.app i)))).obj M ⟶
       (derivedPullback (pullback.fst (B.ι ≫ s) (Spec.map (c.ι.app i)))).obj
         ((schemeMVDerivedRestriction Y B).obj Q))
  stageNatural : ∀ (j : Set.Ici i) (M N : schemeDerivedCategory B.toScheme)
    (g : M ⟶ N) (f : N ⟶ (F ⋙ schemeMVDerivedRestriction Y B).obj j),
    stageEquiv j M (g ≫ f) =
      (derivedPullback (pullback.fst (B.ι ≫ s) (Spec.map (R.map (homOfLE j.property))))).map g ≫
        stageEquiv j N f
  limitNatural : ∀ (M N : schemeDerivedCategory B.toScheme)
    (g : M ⟶ N) (f : N ⟶ (schemeMVDerivedRestriction Y B).obj d.pt),
    limitEquiv M (g ≫ f) =
      (derivedPullback (pullback.fst (B.ι ≫ s) (Spec.map (c.ι.app i)))).map g ≫ limitEquiv N f

/-- Existence of the restricted Hom equivalence fields. The proof transports the
original adjunction equivalences across the open restriction comparison and checks
naturality by the adjunction triangles. Source: Stacks Project, Tags 079W and 08FE.
(blueprint: new-perfect-hom-open-restricted-equiv-fields). -/
theorem perfect_hom_open_restricted_equiv_fields_exists
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) :
    Nonempty (PerfectHomOpenRestrictedEquivFields R c s B Q F d) := by sorry
end
end AlgebraicGeometry
