/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Topologies 04HR and Étale Cohomology 03Q1(2).

Proof: the natural cartesian squares identify `F`, after affine inclusion, with ordinary
small étale base change along `f`. Pullback uniqueness gives the object isomorphisms;
naturality of `p` and uniqueness give their naturality on arrows. Restriction from each
small étale site to its full affine subcategory is an equivalence on Type u sheaves
(04HR). Under these equivalences, precomposition along `F` is ordinary direct image:
on an affine object A both evaluate a sheaf on A ×_S T, and the restriction maps agree.
Conjugate the ordinary étale inverse-image/direct-image adjunction by the restriction
equivalences. The resulting left adjoint is adjoint to the displayed continuous
pushforward. Étale inverse image preserves finite limits by 03Q1(2), and equivalences
and their quasi-inverses preserve all limits, hence this left adjoint preserves finite
limits. The argument uses sheaves in the stated universe throughout and does not require
an enlargement of the coefficient universe or a choice of system coherence data.
(blueprint: lem-weil-pbc-affine-etale-cartesian-sheaf-adjunction). -/
theorem affineEtale_cartesian_sheafAdjunction
    {S T : Scheme.{u}} (f : T ⟶ S) [IsAffineHom f]
    (F : S.FullAffineEtale ⥤ T.FullAffineEtale)
    (p : F ⋙ fullAffineEtaleInclusion T ⋙ Etale.forget T ⋙ Over.forget T ⟶
      fullAffineEtaleInclusion S ⋙ Etale.forget S ⋙ Over.forget S)
    (hp : ∀ A : S.FullAffineEtale,
      IsPullback (p.app A) (F.obj A).obj.hom A.obj.hom f)
    [F.IsContinuous (fullAffineEtaleTopology S) (fullAffineEtaleTopology T)] :
    ∃ L : Sheaf (fullAffineEtaleTopology S) (Type u) ⥤
        Sheaf (fullAffineEtaleTopology T) (Type u),
      Nonempty (L ⊣ F.sheafPushforwardContinuous (Type u)
        (fullAffineEtaleTopology S) (fullAffineEtaleTopology T)) ∧
      PreservesFiniteLimits L := by sorry

end AlgebraicGeometry.Scheme
