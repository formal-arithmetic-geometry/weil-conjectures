/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Sheaf.AlgebraicGeometry.StageCohomologyComparison
public import Mathlib.CategoryTheory.Limits.Final
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.EtaleMayerVietoris
import Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback
import Sheaf.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Native restricted cohomology rows

Source: Stacks Project, Tags 09YQ and 0A50.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The degree-zero restriction row on a cofinal tail.

Source: Stacks Project, Tag 09YQ, coherent-system construction, and Tag 0A50,
initial injectivity and naturality of restriction.
(blueprint: lem-weil-pbc-etale-limit-binary-zero-restriction-row).

Proof: Take J to be the directed tail above i₀ and t its final inclusion. Transfer
U and V to opens of D(i₀) along e and pull these opens back at every stage of J.
Their union is the whole stage: e lands in U ∪ V. At the limit their inverse images
are precisely WU and WV. Restrict the coefficient system using upperStarComp;
the supplied identity and composition equations give the restricted coherence.
Inverse image is a left adjoint, so the restrictions of L are sheaf colimits.
The restricted scheme cones are limits by isLimitOpensCone. Their transitions
and projections are affine. Compactness pulls back along affine maps, and open
subschemes of quasi-separated stages are quasi-separated. Thus each restricted
system meets the system certificate constructor, with initial stage isomorphic
to U.toScheme or V.toScheme. Apply the canonical cohomology diagram construction
in degree zero to each restricted system. Define K₄ as their product diagram and
r as the pair of actual restrictions, conjugated by eH. Pullback and coefficient
naturality prove r natural. Initial Mayer--Vietoris injectivity proves every r.app j
injective. Finite-product preservation for filtered colimits identifies its colimit
with the product of the two restricted colimits. Assemble their system certificates
using prod, then transport by that identification using iso and comp, obtaining v₄.
The canonical cocone equations and hB prove the stated equality on every stage leg.
This constructs only the restriction row; no left zero terms or colimit square is
asserted. Empty and coincident opens still cover, so injectivity remains valid. -/
theorem etale_limit_binary_zero_restriction_row
    (X : Scheme.{u}) (U V : X.Opens)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
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
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) 0))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) 0) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt 0))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) 0))
    (i₀ : I) (e : D.obj (op i₀) ≅ (U ⊔ V).toScheme) :
    let WU := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ U
    let WV := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ V
    let B₄ := AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WU.ι).obj L.pt) 0 ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WV.ι).obj L.pt) 0)
    let r' : B.pt ⟶ B₄ := AddCommGrpCat.ofHom
      (((cohomologyMap WU.ι L.pt 0).prod (cohomologyMap WV.ι L.pt 0)).comp eB.hom.hom)
    ∃ (J : Type u) (order : Preorder J),
      letI := order
      ∃ (directed : IsDirected J (· ≤ ·)) (nonempty : Nonempty J),
      letI := directed
      letI := nonempty
      ∃ (t : J ⥤ I) (ht : t.Final),
      ∃ (K₄ : J ⥤ AddCommGrpCat.{u + 1}) (r : t ⋙ H ⟶ K₄)
        (v₄ : colimit K₄ ⟶ B₄),
        (∀ j, Function.Injective (r.app j)) ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) v₄ ∧
        (∀ j, r.app j ≫ colimit.ι K₄ j ≫ v₄ = B.ι.app (t.obj j) ≫ r') := by sorry

end AlgebraicGeometry.Etale
