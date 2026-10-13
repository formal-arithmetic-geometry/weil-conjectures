module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- The kernel ideal of the relative restriction map is square-zero.
Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-square-zero-relative-section-kernel-ideal)

Proof: On affine charts the kernel is the quotient ideal `I/J`; its product is
zero because `I * I ≤ J`. Pulling back to affine charts of an etale object
preserves this product inclusion, and the sheaf condition glues the resulting
ideal inclusion. -/
theorem relativeSectionKernel_ker_mul_le_bot (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) (hII : I * I ≤ J)
    (V : J.subscheme.Etaleᵒᵖ) :
    RingHom.ker ((etaleStructurePresheafToPullback
      (IdealSheafData.inclusion hJI)).app V).hom *
        RingHom.ker ((etaleStructurePresheafToPullback
          (IdealSheafData.inclusion hJI)).app V).hom ≤ ⊥ := by
  sorry

end AlgebraicGeometry.Scheme
