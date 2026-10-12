/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Pulling a coefficient system to a cone

Source: Stacks Project, Tags 0EXZ and 04JC.
(blueprint: lem-weil-pbc-etale-system-cone-functor).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Pulling a compatible coefficient system to an arbitrary cone gives a functor.
Source: Stacks Project, Tag 0EXZ, transport of a system along compatible inverse
images; the canonical inverse-image comparisons are those of Sites, Tag 03CB.
(blueprint: lem-weil-pbc-etale-system-cone-functor).

Proof: Set G.obj i to inverse image of F i along c.pi at i. Set G.map f to the
composition comparison for c.pi at j and D.map f.op, followed by inverse image
of φ f. Take eG i to be the identity isomorphism. For identity arrows, substitute
hidentity and D.map_id: naturality of the identity comparison and its unit law
cancel the two unit comparisons, leaving the identity. For f followed by g,
substitute hcomposition and apply naturality of the composition comparison to
φ f. Its associativity equation identifies the two nested comparisons; the
cone equation and D.map_comp identify their composite scheme maps. This gives
the functor composition law. The transition equation is the definition of map,
with identity comparison isomorphisms inserted on its two ends. -/
theorem etale_system_cone_functor
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
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
    ∃ (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i)),
    ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv := by sorry

end AlgebraicGeometry.Etale
