module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- The affine formal quotient projection has kernel I^m M.
Source: Stacks Project, Tags 01I8, 01IC and 087W, affine module correspondence.
(blueprint: lem-weil-pbc-formal-module-quotient-affine-projection-ker).

Proof: Write F for the associated sheaf of M and U for the whole spectrum.
The ideal-times affine-sections theorem gives quasi-coherence of the positive
power K and identifies the range of its inclusion with J(U)^m. The product K F
is the image of the multiplication K tensor F to F. The affine tensor comparison
sends a pure tensor to the scalar multiple of its second factor by the image of
its first factor. Tensor induction shows that this multiplication has range
J(U)^m times all sections of F; conversely every generator of that submodule is
such a pure tensor image. The affine image theorem identifies this range with
the range of the product inclusion. Quasi-coherence of the tensor product, its
cokernel and its kernel gives quasi-coherence of K F. The affine cokernel-image
theorem applied to its inclusion says that the kernel of the quotient projection
is this range. The assumption hJ identifies J(U) with I mapped along the inverse
of GammaSpecIso; mapping commutes with ideal powers. The tilde unit identifies
M with the sections of F after restricting scalars along that same isomorphism.
Its linearity transports each generator r times x of I^m M to the corresponding
generator of J(U)^m F(U), and its inverse transports generators back. Thus the
inverse image of the sectionwise kernel is exactly I^m M. This is the asserted
kernel of p. For I=0 the kernel is zero, for I=top it is all of M, and M=0 is
immediate; no finiteness or completeness condition is used. -/
theorem formalModuleQuotient_affine_projection_kernel
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (M : ModuleCat.{u} A) (m : ℕ) (hm : 0 < m) :
    let p := (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app M ≫
      (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        (formalModuleQuotientπ J m ((tilde.functor (CommRingCat.of A)).obj M))
    LinearMap.ker p.hom = I ^ m • (⊤ : Submodule A M) := by
  sorry

end AlgebraicGeometry
