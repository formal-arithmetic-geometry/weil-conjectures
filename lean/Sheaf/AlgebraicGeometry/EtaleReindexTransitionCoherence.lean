/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Restricting coherent étale coefficient systems

Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-reindex-transition-coherence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Restrict the coefficient family along a functor of preorders. The equality transport
is explicit to keep scheme-indexed sheaf types from normalizing their site constructions. -/
def reindexEtaleCoefficients
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I)
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    : ∀ j : J, Sheaf ((t.op ⋙ D).obj (op j)).smallEtaleTopology
        AddCommGrpCat.{u + 1} :=
  fun j => Eq.ndrec (motive := fun X : Scheme.{u} =>
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (F (t.obj j))
    (rfl : D.obj (op (t.obj j)) = (t.op ⋙ D).obj (op j))

/-- Restrict transition morphisms, using the same explicit equality transports. -/
def reindexEtaleTransitions
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I)
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    : ∀ {i j : J} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} ((t.op ⋙ D).map f.op)).obj
        (reindexEtaleCoefficients t D F i) ⟶ reindexEtaleCoefficients t D F j :=
  fun f => Eq.mp (by rfl) (φ (t.map f))

/-- Restriction preserves the identity and composition laws for coefficient transitions.

Source: Stacks Project, Tag 09YQ (theorem-colimit), the cofinal restriction step in
lem-weil-pbc-etale-limit-cohomology-affine-stage.
(blueprint: lem-weil-pbc-etale-reindex-transition-coherence).

Proof: at a restricted index j, the coefficient is F(t(j)); the displayed transports
are along reflexive scheme equalities and cancel. The restricted transition along f
is the original transition along t(f). For the identity law use t.map_id and the
original identity law at t(j). For composition use t.map_comp and the original law
at t(i), t(j), t(k). The maps in the scheme diagram are those of t.op followed by D.
Their functoriality equations agree with the original equations by proof irrelevance,
so the upperStar identity and composition identifications are the same. No cofinality,
affineness, nonemptiness, or cohomological degree is needed for these two laws. -/
theorem reindex_etale_transition_coherence
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I)
    (D : Iᵒᵖ ⥤ Scheme.{u})
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
    :
    (∀ i : J, (reindexEtaleTransitions t D F φ) (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) ((t.op ⋙ D).map_id (op i)))).hom.app
        ((reindexEtaleCoefficients t D F) i) ≫ (upperStarId AddCommGrpCat.{u + 1} ((t.op ⋙
        D).obj (op i))).hom.app ((reindexEtaleCoefficients t D F) i)) ∧
    (∀ (i j k : J) (f : i ⟶ j) (g : j ⟶ k),
      (reindexEtaleTransitions t D F φ) (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} ((t.op ⋙ D).map g.op) ((t.op ⋙ D).map f.op)
          ((t.op ⋙ D).map (f ≫ g).op) ((t.op ⋙ D).map_comp g.op f.op)).hom.app
        ((reindexEtaleCoefficients t D F) i) ≫
        (upperStar AddCommGrpCat.{u + 1} ((t.op ⋙ D).map g.op)).map ((reindexEtaleTransitions
        t D F φ) f) ≫ (reindexEtaleTransitions t D F φ) g)  := by
  constructor
  · intro i
    exact hidentity (t.obj i)
  · intro i j k f g
    exact hcomposition (t.obj i) (t.obj j) (t.obj k) (t.map f) (t.map g)

end AlgebraicGeometry.Etale
