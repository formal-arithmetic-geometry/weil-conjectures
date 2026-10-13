/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
/-! Kernel half of reduction torsion. -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Kernel part of the reduction torsion bound.
Source: Stacks Project, Remark 0888, final commutative algebra argument.
Proof: restrict to an affine open Spec A. Exact sections on quasi-coherent modules
identify the original and reduced kernels and cokernels with their A-module versions,
and identify ideal products and powers with multiplication by K(U)^t. Put J=I(U)^(n+1).
For f,g in K(U)^t and y in H(U), the cokernel hypothesis gives a lift x with a(x)=fy.
Define h(y)=gx. Two lifts differ in ker(a), so the kernel hypothesis makes h well-defined;
choosing lifts of sums and scalar multiples proves A-linearity. The identities
ah=fg and ha=fg follow respectively from a(x)=fy and the same kernel hypothesis.
Linearity sends JH(U) into JF(U), so h descends modulo J. If a reduced class is in the
kernel, ha=fg shows fg kills it. Such products generate K(U)^(2t); hence that ideal
kills the reduced kernel. The quotient projections identify the reduced map with
formalModuleQuotientMap. Ideal-product vanishing on an affine cover implies vanishing
of the sheaf, yielding the global IsZero statement, uniformly in n.
(blueprint: lem-weil-pbc-coherent-map-reduction-torsion-kernel) -/
theorem coherentMap_reduction_torsion_kernel
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (F H : CoherentModules X) (a : F ⟶ H) (t : ℕ) (ht : 1 ≤ t)
    (hker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (kernel a.hom)))
    (hcoker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (cokernel a.hom))) :
    ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι (2 * t)).2
      (kernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) := by sorry
end AlgebraicGeometry
