/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCohomologyStageContinuity

/-! # Continuity when one stage is affine

Source: Stacks Project, Tag 09YQ (theorem-colimit), cofinal-tail reduction.
(blueprint: lem-weil-pbc-etale-limit-cohomology-affine-stage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Affine-stage continuity applies when just one chosen stage is affine.

Source: Stacks Project, Tag 09YQ (theorem-colimit); cofinal-tail reduction in
step 1 of lem-weil-pbc-etale-limit-cohomology-qcqs-gluing.
(blueprint: lem-weil-pbc-etale-limit-cohomology-affine-stage).

Proof: restrict to the directed tail above the chosen stage. Its inclusion is final,
and its opposite is initial. Every later stage is affine over the chosen affine
scheme. Whiskering preserves the scheme limit and the two colimit universal
properties. Restrict every supplied identification and coherence equation along
the inclusion, apply affine continuity, and reflect the colimit by finality.
Empty affine schemes and degree zero use exactly the same argument. -/
theorem etale_limit_cohomology_affine_stage
    (haffine : ∀ {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (D : Jᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Jᵒᵖ, CompactSpace (D.obj i)] [∀ i : Jᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Jᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Jᵒᵖ, IsAffine (D.obj i)]
    (F : ∀ i : J, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : J} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : J, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : J) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : J ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : J, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : J) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (H : J ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : J, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : J) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : J, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p)),
      Nonempty (IsColimit B))
    (S : Scheme.{u}) [IsAffine S] : EtaleCohomologyStageContinuity S  := by sorry

end AlgebraicGeometry.Etale
