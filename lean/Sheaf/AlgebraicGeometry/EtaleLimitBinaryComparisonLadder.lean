/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCohomologyStageContinuity
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Exact.Basic

/-! # Exact comparison ladder for binary continuity

Source: Stacks Project, Tags 09YQ and 0A50.
(blueprint: lem-weil-pbc-etale-limit-binary-comparison-ladder).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The geometric and exactness part of binary continuity, before the group chase.

Source: Stacks Project, Tag 09YQ (theorem-colimit), finite-open-cover reduction,
and Tag 0A50 (lemma-mayer-vietoris).
(blueprint: lem-weil-pbc-etale-limit-binary-comparison-ladder).

Proof: Pass to the directed cofinal tail above i₀. Transfer U and V along the
stage isomorphism and pull them back to each later stage and the limit. These
restricted diagrams are limits with affine transitions. Their stages are qcqs:
affine inverse images preserve compactness of opens, and opens inherit
quasi-separatedness. The intersection at i₀ is compact because that stage is
quasi-separated; ambient X need not be quasi-separated. Restrict F and its
transitions by inverse image. Composition isomorphisms give the coherence laws,
and inverse image preserves L because it is a left adjoint. Apply hCU, hCV and
hCI to obtain colimit comparisons for each restricted system in every degree.
Transport cohomology maps and cocone legs through eG, eH and eB by pullback
functoriality and naturality in coefficients.

For p=q+1 let A₁,A₂,A₄ be the filtered colimits of the stage groups
H^q(U) × H^q(V), H^q(U∩V), and H^p(U) × H^p(V), respectively. Let B₁,B₂,B₄
be the corresponding limit groups. The maps a,b,r and a',b',r' are the
Mayer--Vietoris difference, boundary and restriction maps. Filtered colimits
preserve exactness and finite products, so the two required top pairs and the
first bottom pair are exact. Naturality of Mayer--Vietoris in pullback and in
coefficients gives all three commuting squares, with colimit.desc H B as the
middle comparison. Continuity on U,V,U∩V makes v₁ surjective and v₂,v₄ injective
(in fact all three are isomorphisms). Finality identifies the tail colimits
with those of the original diagram.

For p=0 take A₁,A₂,B₁,B₂ to be the zero group and all incident maps zero.
Use the degree-zero product groups for A₄,B₄ and their restriction maps for
r,r'. The initial Mayer--Vietoris restriction is injective at every stage;
filtered exactness makes r injective. Thus Exact b r holds, while the two
other exact pairs and the first two squares are automatic. Continuity on U,V
gives injectivity of v₄ and the last square is restriction naturality.

Empty opens give zero factors and the same sequences. Coincident opens use
standard diagonal restrictions and difference maps. No middle injectivity or
finite-stage vanishing is assumed or concluded here. The last bottom term and
its restriction map are the actual cohomology groups and pullback maps on the
inverse-image opens; they cannot be replaced by an arbitrary test group. -/
theorem etale_limit_binary_comparison_ladder
    (X : Scheme.{u}) (U V : X.Opens)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hCU : EtaleCohomologyStageContinuity U.toScheme)
    (hCV : EtaleCohomologyStageContinuity V.toScheme)
    (hCI : EtaleCohomologyStageContinuity (U ⊓ V).toScheme)
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
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p))
    (i₀ : I) (e : D.obj (op i₀) ≅ (U ⊔ V).toScheme) :
    let WU := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ U
    let WV := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ V
    let B₄ := AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WU.ι).obj L.pt) p ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WV.ι).obj L.pt) p)
    let r' : B.pt ⟶ B₄ := AddCommGrpCat.ofHom
      (((cohomologyMap WU.ι L.pt p).prod (cohomologyMap WV.ι L.pt p)).comp eB.hom.hom)
    ∃ (A₁ A₂ A₄ B₁ B₂ : AddCommGrpCat.{u + 1})
      (a : A₁ ⟶ A₂) (b : A₂ ⟶ colimit H) (r : colimit H ⟶ A₄)
      (a' : B₁ ⟶ B₂) (b' : B₂ ⟶ B.pt)
      (v₁ : A₁ ⟶ B₁) (v₂ : A₂ ⟶ B₂) (v₄ : A₄ ⟶ B₄),
      Function.Exact a b ∧ Function.Exact b r ∧ Function.Exact a' b' ∧
      Function.Surjective v₁ ∧ Function.Injective v₂ ∧ Function.Injective v₄ ∧
      (∀ x, v₂ (a x) = a' (v₁ x)) ∧
      (∀ x, (colimit.desc H B) (b x) = b' (v₂ x)) ∧
      (∀ x, v₄ (r x) = r' ((colimit.desc H B) x)) := by sorry

end AlgebraicGeometry.Etale
