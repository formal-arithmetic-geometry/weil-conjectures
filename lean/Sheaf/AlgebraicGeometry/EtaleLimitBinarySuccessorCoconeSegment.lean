/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Exact.Basic
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
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Native restricted cohomology rows

Source: Stacks Project, Tags 09YQ and 0A50.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The positive-degree Mayer--Vietoris segment before descent of its squares.

Source: Stacks Project, Tag 09YQ, coherent-system construction, and Tag 0A50,
long exact sequence and coefficient naturality; pullback naturality of its construction.
(blueprint: lem-weil-pbc-etale-limit-binary-successor-cocone-segment).

Proof: Pass to the directed tail J above i₀ with final inclusion t. Transfer U,V
along e to the union stage and pull them back to each later stage and the limit.
These opens cover each stage. Restrict all coefficients and transition maps;
upperStarComp and the original coherence laws give coherent restricted systems.
The restricted cones are limits by isLimitOpensCone, with affine transitions.
Affine inverse images preserve compactness. Quasi-separatedness passes to open
subschemes, and the intersection is compact because D(i₀) is quasi-separated.
Inverse image preserves the sheaf colimit by its left adjoint property. Construct
canonical cohomology diagrams of the two opens and their intersection in degrees
q and q+1. Their specified initial stages are isomorphic to U, V and U ∩ V.
Take K₁ to be the degree-q product, K₂ the degree-q intersection, K₄ the degree-(q+1)
product, and the middle diagram to be t ⋙ H. Apply the functorial Mayer--Vietoris
sequence before evaluating on coefficients, so that its difference and boundary
maps are chosen simultaneously. Coefficient naturality and pullback naturality
make a,b,r natural. Exactness of the sequence gives both stage pairs and the bottom
pair. Its canonical comparison cocones give C₁,C₂ and v₄. The system certificate
constructor certifies the single factors; prod and iso/comp transport certify their
products and the specified cocones. Naturality of the sequence proves the three
stage-leg squares. For the middle square use hB to identify its actual leg with
pullback followed by the coefficient colimit leg. No equality on an entire colimit
is asserted here: those equalities require colimit.hom_ext and finality separately.
Zero factors for empty opens and diagonal/difference maps for coincident opens
satisfy the same naturality and exactness statements. -/
theorem etale_limit_binary_successor_cocone_segment
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
    (L : Cocone G) (hL : IsColimit L) (q : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) (q + 1)))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) (q + 1)) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt (q + 1)))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (q + 1)))
    (i₀ : I) (e : D.obj (op i₀) ≅ (U ⊔ V).toScheme) :
    let WU := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ U
    let WV := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ V
    let B₄ := AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WU.ι).obj L.pt) (q + 1) ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WV.ι).obj L.pt) (q + 1))
    let r' : B.pt ⟶ B₄ := AddCommGrpCat.ofHom
      (((cohomologyMap WU.ι L.pt (q + 1)).prod
        (cohomologyMap WV.ι L.pt (q + 1))).comp eB.hom.hom)
    ∃ (J : Type u) (order : Preorder J),
      letI := order
      ∃ (directed : IsDirected J (· ≤ ·)) (nonempty : Nonempty J),
      letI := directed
      letI := nonempty
      ∃ (t : J ⥤ I) (ht : t.Final),
      ∃ (K₁ K₂ K₄ : J ⥤ AddCommGrpCat.{u + 1})
        (a : K₁ ⟶ K₂) (b : K₂ ⟶ t ⋙ H) (r : t ⋙ H ⟶ K₄)
        (C₁ : Cocone K₁) (C₂ : Cocone K₂)
        (a' : C₁.pt ⟶ C₂.pt) (b' : C₂.pt ⟶ B.pt)
        (v₄ : colimit K₄ ⟶ B₄),
        (∀ j, Function.Exact (a.app j) (b.app j)) ∧
        (∀ j, Function.Exact (b.app j) (r.app j)) ∧ Function.Exact a' b' ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) (colimit.desc K₁ C₁) ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) (colimit.desc K₂ C₂) ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) v₄ ∧
        (∀ j, a.app j ≫ C₂.ι.app j = C₁.ι.app j ≫ a') ∧
        (∀ j, b.app j ≫ B.ι.app (t.obj j) = C₂.ι.app j ≫ b') ∧
        (∀ j, r.app j ≫ colimit.ι K₄ j ≫ v₄ = B.ι.app (t.obj j) ≫ r') := by sorry

end AlgebraicGeometry.Etale
