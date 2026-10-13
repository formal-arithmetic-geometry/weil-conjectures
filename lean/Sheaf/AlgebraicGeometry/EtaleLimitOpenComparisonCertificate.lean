/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone
public import Sheaf.AlgebraicGeometry.StageCohomologyComparison
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Geometric certificate for the canonical open comparison

Source: Stacks Project, Tag 09YQ, restriction of coherent systems.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The canonical cocone on inverse-image opens has a stage-comparison certificate.

Source: Stacks Project, Tag 09YQ, coherent-system construction; the open-limit
construction in Mathlib.AlgebraicGeometry.AffineTransitionLimit.
(blueprint: lem-weil-pbc-etale-limit-open-comparison-certificate).

Proof: Restrict the inverse diagram to the directed tail above i₀ and to the
inverse images of W. The opens cone is limiting by `isLimitOpensCone`, after
identifying the tail opposite with Over(op i₀). Its transitions are affine
restrictions of the given affine maps. At the least tail index its object is
isomorphic to W.toScheme: the identity transition, the given e, and W ≤ O
identify its open with W. Compactness of W makes this least stage compact;
affine preimages of quasi-compact opens are quasi-compact. Every other stage
is an open in a quasi-separated scheme, hence quasi-separated. Pull the given
coefficient system back to these stages with `openSquareCoefficient`. The
canonical inverse-image coherences give the identity, composition and G-map
equations. The tail inclusion is final (directedness gives an upper bound for
any index and i₀), so L reindexed to the tail is still a colimit. Inverse image
along the limit open is a left adjoint and preserves this colimit. Composition
identifications make it the colimit of the pulled-back restricted coefficients.
The specified hK and hι are precisely the arrow and cocone formulas for this
system, after transporting the object identifications eK. Apply the `system`
constructor of StageCohomologyComparison at the least index, and transport
through the canonical open-limit/coefficient isomorphisms with its `iso` and
`comp` constructors. This certifies the supplied colimit.desc, without asserting
that it is an isomorphism. Empty W, zero coefficients, and singleton diagrams
satisfy the same construction; no injectivity or continuity is assumed. -/
theorem etale_limit_open_comparison_certificate
    (X : Scheme.{u}) (O W : X.Opens) (hW : IsCompact (W : Set X)) (hWO : W ≤ O)
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
    (i₀ : I) (e : D.obj (op i₀) ≅ O.toScheme)
    (allowed : Scheme.{u} → Prop) (hallowed : allowed W.toScheme)
    (K : Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
    (eK : ∀ j : Set.Ici i₀, K.obj j ≅ AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        (tailStageOpen D (e.hom ≫ O.ι) W j).ι).obj (F j.val)) 0))
    (hK : ∀ (j k : Set.Ici i₀) (f : j ⟶ k), K.map f =
      (eK j).hom ≫ tailOpenCohomologyMap D (e.hom ≫ O.ι) W F φ f ≫ (eK k).inv)
    (ι : K ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ (e.hom ≫ O.ι)) ⁻¹ᵁ W).ι).obj L.pt) 0)))
    (hι : ∀ j, ι.app j =
      (eK j).hom ≫ tailOpenCohomologyLeg D c (e.hom ≫ O.ι) W F G eG L j) :
    StageCohomologyComparison allowed (colimit.desc K (Cocone.mk _ ι)) := by
  sorry

end AlgebraicGeometry.Etale
