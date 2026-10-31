/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.CondensedTensorInductionData

/-! # Extension of the balanced tensor formula
Source: direct-image stability, paragraph (3), induction proof step 6.
(blueprint: lem-sfb-condensed-tensor-extension).
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace Profinite.CondensedAction
variable {R : Profinite.CondensedRing.{u}} [IsCommMonObj R.X]
  {P : ProfiniteGrp.{u}} {H : ClosedSubgroup P}

/-- The extension map on pure tensors exists. This is strictly the extension step of
reciprocity; it does not assert uniqueness, inverse identities, additivity or naturality.
Source: induction proof step 6 (blueprint: lem-sfb-condensed-tensor-extension).

Proof: define the map on finite sums by sending a[p] tensor m to a times p f(m).
The additive and scalar relations vanish by linearity, while the balancing relation
vanishes by H-equivariance, `(ph)f(m)=p f(hm)`. Restrictions and left multiplication
make the map a natural P-equivariant presheaf map. Ordinary module sheafification
extends it uniquely. Transport the extension across D.comparison and the fully
faithful internal section-module equivalence. To check equivariance for an
arbitrary sheaf section x, cover by local preimages of x along the ordinary
sheafification unit and restrict the group section as well. Naturality of the
action and the map, D.induced_action and presheaf equivariance prove the identity
on this cover. Separatedness of the target sheaf proves it globally. The unit
identity gives the displayed formula. This argument includes the empty test
object and zero module and uses no coset section.
-/
theorem tensorInductionExtension_exists (B : TensorInductionPresheaf R P H)
    (D : TensorInductionSheafData B) (M : ActionModule R H.toSubgroup)
    (N : ActionModule R P)
    (f : M ⟶ (inflate (inductionSubgroupInclusion P H)).obj N) :
    ∃ F : D.functor.obj M ⟶ N,
      ∀ (S : Profinite.{u}) (p : C(S, P)) (m : sectionModule R M.module S),
        ((F.val.hom.hom.app (op S)).hom)
            (B.sheafTensor D.functor D.comparison M S p m) =
          N.act S p ((f.val.hom.hom.app (op S)).hom m) := by
  sorry

end Profinite.CondensedAction
