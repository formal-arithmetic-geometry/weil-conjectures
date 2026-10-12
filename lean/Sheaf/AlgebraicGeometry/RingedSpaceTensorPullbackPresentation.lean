module

public import Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry.RingedSpace

/-- Tensor pullback transports a global presentation over an open subset.
Source: Stacks Project, Modules, Tag 01BG, Lemma 17.10.4, global presentation step.
(blueprint: lem-pc-ringed-space-tensor-pullback-presentation-over)

Proof: Put U = g⁻¹(V) and restrict g to the morphism of ringed spaces U → V.
Restriction commutes with inverse image and with sheafified extension of scalars:
on an open W contained in U, the inverse-image presheaf is computed using opens
of Y containing g(W), and those contained in V form a cofinal subposet. The
structure maps and tensor products on these opens agree; sheafification commutes
with restriction. Thus the displayed module over U identifies with the tensor
pullback of G over V along this restricted morphism. Its inverse-image and
extension-of-scalars functors are left adjoints, so preserve coproducts and
cokernels. The pullback of the unit module is the unit module: the tensor map
b ⊗ a ↦ b g-sharp(a) has inverse b ↦ b ⊗ 1. Consequently each free module in the
presentation p pulls back to the free module with the same indexing set. Apply
the composite functor to the cokernel presentation furnished by p. Preservation
of its cokernel gives an exact free presentation of the pulled-back module.
Mathlib's Presentation.map packages this construction, and Presentation.ofIsIso
transports it through the restriction comparison above. No choices of a cover
or of a neighbourhood of a point occur in this statement. -/
theorem tensorModulePullback_presentation_over
    {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (G : SheafOfModules.{u} (moduleRings Y)) (V : TopologicalSpace.Opens Y)
    (p : (G.over V).Presentation) :
    Nonempty
      (((SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf G)).over
          ((TopologicalSpace.Opens.map g.hom.base).obj V)).Presentation) := by
  sorry

end AlgebraicGeometry.RingedSpace
