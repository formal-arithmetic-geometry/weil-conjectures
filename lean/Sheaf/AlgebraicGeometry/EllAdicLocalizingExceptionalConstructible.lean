/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward
import Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded
import Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology

/-! # Constructibility of the localizing exceptional inverse image

Source: blueprint `sk-thm-existence` (4), `det-existence-restriction.proof.md`.
(blueprint: lem-sfb-adic-localizing-exceptional-constructible)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- Any right adjoint to the proper localizing pushforward sends bounded constructible
objects to bounded constructible objects. Its adjunction fixes the functor up to the
unique compatible isomorphism.

Source: blueprint `sk-thm-existence` (4), `det-existence-restriction.proof.md`, and
`sk-cor-existence-ii-restriction.proof.md` (2).
(blueprint: lem-sfb-adic-localizing-exceptional-constructible)

Proof: first use Noetherianity of the schemes and their locally closed strata to
compare the library's local finite presentations with the source's adic constructible
objects. For E and Qlbar use `exists_finiteFree_cover_of_condensedField_lfp` and
`condensedQbar_lfp_locally_free`; for OE use `integral_lfp_local_torsion_charts` and
`integral_lfp_locallyFree_resolution`. This step is needed because arbitrary local
presentation matrices need not be constant on a non-Noetherian scheme.
For E and Qlbar use the geometric restriction theorem `sk-thm-restriction`;
for OE use `sk-thm-int-restriction`. These compute the exceptional inverse image for
smooth projections using the diagonal class and trace on P1, and for closed immersions
using the localization triangle and the finiteness of the complementary open direct
image. A local factorization into a closed immersion and a smooth projection gives
boundedness and constructibility on affine charts. Choose finite affine covers,
using quasi-compactness, so the local cohomological bounds have a common finite bound.
The localization identifications agree on overlaps by their adjunctions and glue;
constructibility is local on these charts. This gives the result for a general morphism.
In the integral case perform
the compatible torsion-level construction and pass to the adic limit. Uniqueness of
right adjoints identifies those functors with the right adjoint supplied here, and
bounded constructibility is invariant under isomorphism. Thus its value on each bounded
constructible target object is bounded constructible in the ambient source category.
-/
theorem ellAdic_localizing_rightAdjoint_obj_boundedConstructible
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    boundedConstructible (condensedRingObj Λ Z.left)
      ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj) := by
  rw [mem_boundedConstructible_iff]
  exact ⟨ellAdic_localizing_rightAdjoint_obj_isBounded Λ ℓ g hΛ G adj K,
    ellAdic_localizing_rightAdjoint_obj_homology_constructible Λ ℓ g hΛ G adj K⟩

end AlgebraicGeometry.ProEtale.CondensedRing
