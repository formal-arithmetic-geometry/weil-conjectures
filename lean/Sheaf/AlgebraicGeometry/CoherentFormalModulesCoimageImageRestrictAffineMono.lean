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

/-- The affine restriction of the coimage-image comparison is monic.
Source: Stacks Project, Lemma 087X, affine calculation of Coim=Im.
(blueprint: lem-weil-pbc-coherent-formal-coimage-image-affine-mono).

Proof: On an affine open, the coherent formal module equivalence identifies the
comparison with the map from a module modulo its kernel to its image. The first
isomorphism theorem makes this map injective; restriction and associated sheaf
preserve that injectivity. The argument is independent of the chosen kernel and
cokernel structures because their universal comparison isomorphisms conjugate
the map. -/
theorem coherentFormalModules_coimageImage_isMono_restrict_affine
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    [HasKernels (CoherentFormalModule X I)]
    [HasCokernels (CoherentFormalModule X I)] (U : X.affineOpens)
    {F G : CoherentFormalModule X I} (α : F ⟶ G) (n : ℕ) :
    Mono ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).map
      ((Abelian.coimageImageComparison α).hom.app (op n))) := by
  sorry

end AlgebraicGeometry
