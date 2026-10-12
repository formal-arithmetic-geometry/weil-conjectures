module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom


@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Vanishing of derived additive cohomology above degree one.
Source: blueprint `lem-sc-artin-schreier-dimension`, step 2; Stacks 03P2 and 02UZ.
(blueprint: lem-sc-artin-schreier-additive-derived-vanishing)

Proof: The given isomorphism identifies G with the universe lift of the additive
etale structure sheaf. Compare derived global sections on a sheaf in degree zero
with ordinary sheaf cohomology, by injective resolutions (lem-sp-kinjective-computes).
To compare with the smaller-universe sheaf, use finite affine etale hypercovers:
quasi-compactness gives finite refinements in each degree needed to compute q.
Universe lift identifies their cochains, cocycles and coboundaries sectionwise,
since it preserves finite products and is exact. This does not assume
that universe lift preserves injective sheaves. By
lem-sc-ga-cohomology, ordinary additive etale cohomology agrees with Zariski
structure-sheaf cohomology and vanishes in degrees at least two: the curve is
Noetherian of dimension one, so use cohomology above dimension (Stacks 02UZ).
Transport zero across these comparisons and the given sheaf isomorphism. -/
theorem isZero_etaleCohomology_additive_of_two_le
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : G ≅ (sheafCompose C.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C)))
    (q : ℕ) (hq : 2 ≤ q) :
    IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} C (q : ℤ)).obj
      ((DerivedCategory.singleFunctor (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        G)) := by
  sorry

end AlgebraicGeometry
