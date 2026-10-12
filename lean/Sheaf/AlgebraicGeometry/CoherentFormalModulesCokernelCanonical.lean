module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical ambient cokernel of a map between coherent formal modules is coherent.
Source: Stacks Project, Lemma 087X, termwise cokernel construction
(blueprint: lem-weil-pbc-coherent-formal-cokernel-canonical).

Proof: evaluate the ambient cokernel cofork termwise. Coherence of each term follows
from coherent kernel/cokernel closure. The quotient description on affine sections,
together with the transition quotient isomorphisms and ideal-product formulas, proves
annihilation and the adic transition condition. -/
theorem coherentFormalModules_canonicalCokernel_isCoherent
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    {F G : ℕᵒᵖ ⥤ X.Modules}
    (hF : IsCoherentFormalModule I F) (hG : IsCoherentFormalModule I G)
    (α : F ⟶ G) :
    IsCoherentFormalModule I (cokernel α) := by
  sorry

end AlgebraicGeometry
