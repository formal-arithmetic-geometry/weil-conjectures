module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFormalModulesCokernelClosure
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.RingTheory.AdicCompletionNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The affine restriction of the coimage-image comparison is epic.
Source: Stacks Project, Lemma 087X, affine calculation of Coim=Im.
(blueprint: lem-weil-pbc-coherent-formal-coimage-image-affine-epi).

Proof: On an affine open, the coherent formal module equivalence identifies the
comparison with the map from a module modulo its kernel onto its image. The first
isomorphism theorem makes this map surjective; restriction and associated sheaf
preserve that surjectivity. The conclusion is invariant under the unique
isomorphisms between supplied kernel and cokernel structures. -/
theorem coherentFormalModules_coimageImage_isEpi_restrict_affine
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    [HasKernels (CoherentFormalModule X I)]
    [HasCokernels (CoherentFormalModule X I)] (U : X.affineOpens)
    {F G : CoherentFormalModule X I} (α : F ⟶ G) (n : ℕ) :
    Epi ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).map
      ((Abelian.coimageImageComparison α).hom.app (op n))) := by
  sorry

end AlgebraicGeometry
