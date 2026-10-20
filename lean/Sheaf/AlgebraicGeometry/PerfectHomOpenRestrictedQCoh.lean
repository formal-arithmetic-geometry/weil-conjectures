module

public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

/-- Exact open restriction preserves quasi-coherence of the restricted stages and apex.
Source: Stacks Project, Tag 08DW.
Proof: apply `schemeDerivedQCoh_openRestriction_iff` to each stage and to the
apex. For every cohomological degree, the corresponding cohomology sheaf of the
given QCoh object restricts to a quasi-coherent over-module by
`SheafOfModules.isQuasicoherent_over`.
(blueprint: new-perfect-hom-open-restricted-qcoh). -/
theorem perfect_hom_open_restricted_qcoh
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) :
    (∀ j : Set.Ici i, schemeDerivedQCohProperty B.toScheme
      ((F ⋙ schemeMVDerivedRestriction Y B).obj j)) ∧
    schemeDerivedQCohProperty B.toScheme
      ((schemeMVDerivedRestriction Y B).obj d.pt) := by
  constructor
  · intro j n
    apply (schemeDerivedQCoh_openRestriction_iff Y B (F.obj j)).2
    intro n'
    have hn := h.stageQCoh j n'
    exact SheafOfModules.isQuasicoherent_over
      ((DerivedCategory.homologyFunctor _ n').obj (F.obj j)) B
  · intro n
    apply (schemeDerivedQCoh_openRestriction_iff Y B d.pt).2
    intro n'
    have hn := h.limitQCoh n'
    exact SheafOfModules.isQuasicoherent_over
      ((DerivedCategory.homologyFunctor _ n').obj d.pt) B

end
end AlgebraicGeometry
