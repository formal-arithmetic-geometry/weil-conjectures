module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.Paper.PQFCohomology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Ideal H¹ vanishing annihilates H¹ of the kernel of a map from a finite free module
to the structure sheaf.

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
last two paragraphs (blueprint: lem-pqf-finite-free-kernel-h1-vanishing).

Proof: Enumerate the finite index type. The kernel F is quasi-coherent, since both
finite free modules and the structure sheaf are quasi-coherent and kernels of maps
of quasi-coherent modules on schemes are quasi-coherent. Intersect F with the first
j summands to obtain F_j. The kernel of projection from F_j onto its last coordinate
is F_{j-1}; its image is a quasi-coherent ideal subsheaf of the structure sheaf.
Thus F_j/F_{j-1} is such an ideal sheaf. Starting with F_0 = 0, use the exact segment
H¹(F_{j-1}) → H¹(F_j) → H¹(F_j/F_{j-1}). The two outer groups vanish by induction and
the ideal hypothesis, so the middle group vanishes. At the last index this gives
H¹(F) = 0. The empty index type gives the zero kernel directly. This argument does
not require the original map to be an epimorphism. -/
theorem finite_free_kernel_h1_zero (X : Scheme.{u})
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules))
    {I : Type u} [Finite I]
    (p : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj (kernel p)) := by
  sorry

end AlgebraicGeometry
