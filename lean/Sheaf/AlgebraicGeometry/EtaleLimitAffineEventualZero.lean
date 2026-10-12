/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.CategoryTheory.CohomologyColimitSitesEventualVanishing
import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.CategoryTheory.ColimitSites
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # EtaleLimitAffineEventualZero

Source: Stacks Project, Tags 09YQ, 0EYL, 04HR and 09YP.
(blueprint: lem-weil-pbc-etale-limit-affine-eventual-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The kernel half of affine-stage cohomology continuity.

Source: Stacks Project, Theorem 09YQ, via Lemmas 0EYL, 04HR and 09YP,
and the dimension-shifting argument of 0739.
(blueprint: lem-weil-pbc-etale-limit-affine-eventual-zero).

Proof: use `exists_affineEtaleSite_colimit` to obtain the strictified affine
sites. Restriction to the affine site is a sheaf equivalence by 04HR. The right
adjoints evaluate on the same cartesian base changes, so uniqueness of left
adjoints gives unit-compatible inverse-image comparisons. Their composite
units agree, giving the coherence needed to transport the coefficient system,
G, L and its coprojections. Equivalences preserve the coefficient colimit.
Pass to the cofinal tail above a stage. Its identity affine etale object is
final, and its base changes are the final objects at later stages and the
limit. Object cohomology at these final objects is global cohomology. Transport
along the restriction and strictification equivalences preserves Ext and the
adjunction-unit pullback maps, naturally in the coefficients. Universe lifts
to the coefficient universe preserve these equivalences and colimits.

Use the finite-stage kernel half of the connecting-ladder argument (09YP,
0739). Degree zero is detection of zero in the filtered colimit of sections.
In successor degree the stage long exact sequence lifts the class to the
preceding cohomology of the cokernel system. Its limit image comes from the
injective system because the original limit class is zero. Descend this
injective-system class using existence in the preceding degree. At a common
later stage, the difference of the two preceding-degree classes is zero by
inductive detection of zero. The stage connecting map then kills the original
class. This uses existence and detection only in a smaller degree.

Apply `cohomology_colimit_sites_eventual_vanishing` at this
final object. The unit-compatible comparisons identify its legs with the
cohomology maps displayed here. Cofinality of the tail gives the assertion on I.

Edge cases: the index is nonempty; an empty scheme has zero cohomology; degree
zero is the section assertion. For a singleton system the assertion is
injectivity of that identification, with the identity transition.
-/
theorem etale_limit_affine_eventual_zero
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (i : I) (x : Sheaf.H (F i) p)
    (hx : Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p
      (cohomologyMap (c.π.app (op i)) (F i) p x) = 0) :
    ∃ (j : I) (f : i ⟶ j),
      Sheaf.H.map (φ f) p (cohomologyMap (D.map f.op) (F i) p x) = 0 := by sorry

end AlgebraicGeometry.Etale
