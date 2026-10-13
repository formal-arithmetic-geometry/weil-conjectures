/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalData

/-! # Scalar action on normalized additive étale Čech edges
Source: Stacks Project, Tags 03P2 and 01EQ. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Augmentation-normalized edges intertwine multiplication with scalar action.
Source: Stacks Project, Tag 03P2, the coefficient edge, and Tag 01EQ,
functoriality of the augmented injective Čech double complex in coefficients.
(blueprint: lem-pbc-etale-additive-cech-normalized-scalar)

Proof: Lift μ(r) to an augmentation-preserving endomorphism of a resolution.
On the coefficient Čech complex its action is coordinatewise multiplication by
the restriction of r, by hμ. The unit module restrictions are structural-ring
maps, so this is exactly the scalar endomorphism of cechOver after restriction
along X.toSpecGamma; GammaSpecIso.inv_hom_id identifies that scalar map with the
identity. Both augmentations commute with the lifted endomorphism. The extMk
formula identifies the global-resolution homology endomorphism with
Sheaf.H.map(μ(r)). Choose a cycle representing a(x) and a global-resolution cycle
representing x. Since both augmentations are quasi-isomorphisms, first choose
an ordinary class with beta image equal to the alpha image of x. Normalization
identifies that class with a(x). Thus every representative of a(x) has this same
total homology image. Apply the lifted endomorphism to these cycles and to that equality.
The normalization law ha then gives a(H(μ(r))(x)) as the class of r times the
original coefficient cycle, which is r • a(x). This works for n=0 by gluing and
for r=0, r=1 and empty intersections by the same section formulas. An empty
cover forces all groups zero. No inverse-image comparison is used. -/
theorem etaleAdditiveCech_normalized_scalar
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤)
    (μ : Γ(X, ⊤) → (X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf))
    (hμ : ∀ r (W : X.Etaleᵒᵖ) (x : X.etaleAdditiveSheaf.obj.obj W),
      (μ r).hom.app W x =
        ULift.up ((show Γ(W.unop.left, ⊤) from x.down) *
          (show Γ(W.unop.left, ⊤) from W.unop.hom.appTop r)))
    (n : ℕ)
    (a : Sheaf.H X.etaleAdditiveSheaf n ≃+
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n)
    (ha : IsEtaleAdditiveCechNormalized U n a) :
    ∀ r x, a (Sheaf.H.map (μ r) n x) = r • a x := by sorry

end AlgebraicGeometry.Scheme.Modules
