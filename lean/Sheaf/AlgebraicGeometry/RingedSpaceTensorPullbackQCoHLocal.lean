module

public import Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry.RingedSpace

/-- Local quasi-coherence of tensor pullback.
Source: Stacks Project, Modules, Tag 01BG, Lemma 17.10.4.
The proof chooses affine-style presentation neighbourhoods and transports them through
inverse image and extension of scalars; this is the local step of the standard proof.
(blueprint: lem-pc-ringed-space-tensor-pullback-qcoh-local) -/
theorem tensorModulePullback_isQuasicoherent_local
    {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (G : SheafOfModules.{u} (moduleRings Y)) (hG : G.IsQuasicoherent) (x : X) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      ((SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf G)).over U).IsQuasicoherent := by
  sorry

end AlgebraicGeometry.RingedSpace
