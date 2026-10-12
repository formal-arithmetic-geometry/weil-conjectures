/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # The degree-zero affine continuity kernel

Source: Stacks Project, Tags 09YQ, 09YP, 09YN and 0739.
(blueprint: lem-weil-pbc-etale-limit-affine-degree-zero-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Detection of zero for degree-zero affine-stage cohomology.

Source: Stacks Project, Tag 09YP, degree-zero case, using Sites Tag 09YN;
affine étale reduction in Tags 09YQ, 0EYL and 04HR.
(blueprint: lem-weil-pbc-etale-limit-affine-degree-zero-kernel).

Proof: Restrict to the cofinal upper tail of i. Present the affine étale sites
by the strictified colimit of 0EYL. Restriction from the small étale site is
an equivalence by 04HR. Both direct images evaluate on the same cartesian
base changes of affine objects. The resulting right-adjoint comparison induces
an inverse-image comparison compatible with adjunction units. Uniqueness of
this comparison gives its identity and composition coherence. Transport F, φ,
G and the colimit cocone L through these equivalences; equivalences preserve
colimits. The identity object of the affine scheme at i and its base changes
are terminal. The section comparison of 09YN at this object identifies the
limit sections with the filtered colimit of the stage sections. Degree-zero
Ext is sections via H.equiv₀; the cohomology pullback formula is the adjunction
unit, so the specified maps are exactly these section comparison maps.
A representative whose limit section is zero equals the zero representative
in this filtered colimit. Finite-stage detection of equality therefore gives
a later stage at which its transition is zero. The tail inclusion supplies the
arrow i → j in the original index category.

Edge cases: zero coefficients and the empty affine scheme have zero sections;
for a singleton index both comparisons are equivalences. No higher-degree
continuity or negative cohomology is used.
-/
theorem etale_limit_affine_degree_zero_kernel
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
    (L : Cocone G) (hL : IsColimit L)
    (i : I) (x : Sheaf.H (F i) 0)
    (hx : Sheaf.H.map ((eG i).inv ≫ L.ι.app i) 0
      (cohomologyMap (c.π.app (op i)) (F i) 0 x) = 0) :
    ∃ (j : I) (f : i ⟶ j),
      Sheaf.H.map (φ f) 0 (cohomologyMap (D.map f.op) (F i) 0 x) = 0 := by sorry


end AlgebraicGeometry.Etale
