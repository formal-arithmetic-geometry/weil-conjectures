/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleReindexTransitionCoherence

/-! # Restricting the étale cohomology comparison diagrams

Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-reindex-comparison-coherence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Whisker the coefficient diagram on the limit scheme, transporting its vertex type. -/
def reindexEtaleDiagram
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I)
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    : J ⥤ Sheaf (c.whisker t.op).pt.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Eq.ndrec (motive := fun X : Scheme.{u} =>
    J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (t ⋙ G)
    (rfl : c.pt = (c.whisker t.op).pt)

/-- The restricted coefficient cocone has exactly the original vertex and selected legs. -/
def reindexEtaleCocone
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I)
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (L : Cocone G)
    : Cocone (reindexEtaleDiagram t D c G) :=
  Eq.mp (by rfl) (L.whisker t)

/-- Restriction of the supplied pullback identifications. -/
def reindexEtalePullbackIso
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I)
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    : ∀ j : J, (reindexEtaleDiagram t D c G).obj j ≅
      (upperStar AddCommGrpCat.{u + 1} ((c.whisker t.op).π.app (op j))).obj
        (reindexEtaleCoefficients t D F j) :=
  fun j => Eq.mp (by rfl) (eG (t.obj j))

/-- Restriction of the supplied cohomology identifications. -/
def reindexEtaleCohomologyIso
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I)
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (p : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    : ∀ j : J, (t ⋙ H).obj j ≅
      AddCommGrpCat.of (Sheaf.H (reindexEtaleCoefficients t D F j) p) :=
  fun j => Eq.mp (by rfl) (eH (t.obj j))

/-- Restriction of the cohomology cocone's vertex identification. -/
def reindexEtaleVertexIso
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I)
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (L : Cocone G)
    (p : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (B : Cocone H)
    (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    : (B.whisker t).pt ≅
      AddCommGrpCat.of (Sheaf.H (reindexEtaleCocone t D c G L).pt p) :=
  Eq.mp (by rfl) eB

/-- Restriction preserves all three supplied comparison equations.

Source: Stacks Project, Tag 09YQ (theorem-colimit), the comparison-diagram restriction
step in lem-weil-pbc-etale-limit-cohomology-affine-stage.
(blueprint: lem-weil-pbc-etale-reindex-comparison-coherence).

Proof: the restricted sheaf and cohomology diagrams are obtained by whiskering with t.
Their maps at f are G.map(t.map f) and H.map(t.map f). The scheme cone has leg at j
equal to c.π.app(op(t.obj j)); the two cocones have legs L.ι.app(t.obj j) and
B.ι.app(t.obj j), with their original vertices. Each displayed reindexing constructor
uses only a reflexive equality transport, so cancelling these transports identifies
the first equation with hG at t(i), t(j), t(f), the second with hH at those indices,
and the third with hB at t(i). The cone naturality proof in upperStarComp has the same
endpoints as the original cone naturality proof, hence agrees by proof irrelevance.
No affine continuity or colimit property is used. This also proves the statement for
empty indexing categories, empty schemes, and degree zero. -/
theorem reindex_etale_comparison_coherence
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I)
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    (p : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H)
    (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p))
    :
    (∀ (i j : J) (f : i ⟶ j), (reindexEtaleDiagram t D c G).map f =
      ((reindexEtalePullbackIso t D c F G eG) i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} ((c.whisker t.op).π.app (op j)) ((t.op ⋙ D).map f.op)
          ((c.whisker t.op).π.app (op i)) ((c.whisker t.op).w f.op).symm).hom.app
        ((reindexEtaleCoefficients t D F) i) ≫
        (upperStar AddCommGrpCat.{u + 1} ((c.whisker t.op).π.app (op j))).map
        ((reindexEtaleTransitions t D F φ) f) ≫ ((reindexEtalePullbackIso t D c F G eG) j).inv) ∧
    (∀ (i j : J) (f : i ⟶ j), (t ⋙ H).map f =
      ((reindexEtaleCohomologyIso t D F p H eH) i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap
        ((t.op ⋙ D).map f.op) ((reindexEtaleCoefficients t D F) i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((reindexEtaleTransitions t D F φ) f) p) ≫
        ((reindexEtaleCohomologyIso t D F p H eH) j).inv) ∧
    (∀ i : J, (B.whisker t).ι.app i ≫ (reindexEtaleVertexIso t D c G L p H B eB).hom =
      ((reindexEtaleCohomologyIso t D F p H eH) i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap
        ((c.whisker t.op).π.app (op i)) ((reindexEtaleCoefficients t D F) i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (((reindexEtalePullbackIso t D c F G eG) i).inv ≫
        (reindexEtaleCocone t D c G L).ι.app i) p))  := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j f
    exact hG (t.obj i) (t.obj j) (t.map f)
  · intro i j f
    exact hH (t.obj i) (t.obj j) (t.map f)
  · intro i
    exact hB (t.obj i)

end AlgebraicGeometry.Etale
