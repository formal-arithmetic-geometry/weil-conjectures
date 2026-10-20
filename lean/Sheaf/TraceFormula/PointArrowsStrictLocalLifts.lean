/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Sites.Limits

import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension

/-!
# Point arrows and geometric lifts into strict localizations

Source: Stacks Project, Tag 0GJ2, section on specializations, for the germ construction;
the converse and equivariance are the agent-supplied prorepresentability argument recorded
in the DAG (blueprint: lem-trf-point-arrows-strict-local-lifts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The geometric morphism defined by a geometric point of the small etale site.
Its inverse image is the geometric stalk and its direct image is the canonical skyscraper.
Source: Stacks Project, Tag 0GJ2 (blueprint: lem-trf-point-arrows-strict-local-lifts). -/
noncomputable def etaleGeometricPointMorphism
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    GeometricMorphism (Type (u + 1)) (Sheaf S.smallEtaleTopology (Type (u + 1))) where
  inverse := (pointSmallEtale s).sheafFiber
  direct := (pointSmallEtale s).skyscraperSheafFunctor
  adj := (pointSmallEtale s).skyscraperSheafAdjunction
  leftExact :=
    haveI : AB5OfSize.{u, u} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} (Type (u + 1))
    inferInstance

/-- A chosen small affine pointed neighbourhood, viewed in the full neighbourhood category.
This is precisely the representative functor of the strict-localization definition.
Source: Stacks Project, Tag 0GJ2 (blueprint: lem-trf-point-arrows-strict-local-lifts). -/
noncomputable def strictLocalLiftRepresentative
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    (pointSmallEtale s).fiber.Elements :=
  (Functor.Elements.precomp (AffineEtale.Spec S) (pointSmallEtale s).fiber).obj
    ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j)

/-- The canonical projection to a representative affine neighbourhood: the spectrum of the
ring-colimit injection, followed by the canonical identification with the neighbourhood.
Source: Stacks Project, Tag 0GJ2 (blueprint: lem-trf-point-arrows-strict-local-lifts). -/
noncomputable def strictLocalLiftProjection
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
    strictHenselizationScheme s ⟶ (strictLocalLiftRepresentative s j).1.left :=
  (strictHenselizationCone s).π.app (op (op j)) ≫
    Spec.map (ΓSpecIso
      (((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left.unop)).inv

/-- Geometric lifts into the strict localization classify all arrows of etale topos points.
The equivalence is characterized by its mate on every represented germ. The formula is
written after any pointed affine representative refinement `f` of `U`, so it includes
nonaffine `U`. The final clause specifies both the germ action of the field automorphism
and equivariance for the very same equivalence and point automorphism.
Source: Stacks Project, Tag 0GJ2, germ formula; the converse and equivariance are the
agent-supplied argument (blueprint: lem-trf-point-arrows-strict-local-lifts).

Proof (the six DAG steps):
1. For an etale `U`, representable stalks are its geometric lifts
   (lem-galois-stalk-representable). Sheafification preserves these stalks
   (lem-weil-pbc-sets-sheafification-geometric-stalk). Thus a lift `u` determines the
   identity germ `e_u` of the sheafified representable, naturally in `U`.
2. The small affine limit projections extend to all pointed neighbourhoods using affine
   refinements (lemma-weil-pbc-affine-neighbourhood-cofinal). Cofilteredness and
   equalization (lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered) make the extension
   independent of the refinement and compatible with every pointed map, over `S`.
3. A lift `a` therefore sends `[U,u,z]` to `[U,c_u a,z]`. The colimit universal property
   gives a stalk map natural in the sheaf. Adjunction mates give the point arrow.
4. Conversely, apply a point arrow's mate to each `e_u`. The representable-stalk
   bijection recovers compatible geometric lifts into the affine neighbourhoods.
   The defining inverse-limit property gives a unique `a` over `S`.
5. Starting with `a` recovers its projections, hence `a`. Starting with an arrow, Yoneda
   (lem-galois-yoneda-hom-bijection) and the sheafification universal property test its
   mate on every germ via the map from the sheafified representable associated to `z`.
   Its mate is precisely that of the arrow constructed in step 3. Mates are bijective,
   so the two constructions are inverse, and the germ formula characterizes them.
6. Precompose every geometric lift by `Spec tau`. This respects pointed refinements,
   gives a natural stalk automorphism, and has inverse obtained from `tau.symm`.
   Take its mate to obtain `r_tau`. On germs the changed-lift map is the composite of
   the original germ map with this stalk automorphism. Mates reverse composition,
   giving the stated equivariance. Only `Spec tau ≫ t = t` is used. -/
theorem point_arrows_strict_local_lifts
    {S : Scheme.{u}} {Ωt Ωs : Type u}
    [Field Ωt] [IsAlgClosed Ωt] [Field Ωs] [IsAlgClosed Ωs]
    (t : Spec (.of Ωt) ⟶ S) (s : Spec (.of Ωs) ⟶ S) :
    ∃ Θ : {a : Spec (.of Ωt) ⟶ strictHenselizationScheme s //
        a ≫ strictHenselizationStructuralMap s = t} ≃
        ((etaleGeometricPointMorphism t).direct ⟶ (etaleGeometricPointMorphism s).direct),
      (∀ (a : {a : Spec (.of Ωt) ⟶ strictHenselizationScheme s //
          a ≫ strictHenselizationStructuralMap s = t})
        (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (U : S.Etale)
        (u : (pointSmallEtale s).fiber.obj U)
        (j : SmallModel.{u} (strictHenselizationNeighbourhoods s))
        (f : (strictLocalLiftRepresentative s j).1 ⟶ U),
        (pointSmallEtale s).fiber.map f (strictLocalLiftRepresentative s j).2 = u →
        ∀ z : F.obj.obj (op U), ∃ v : (pointSmallEtale t).fiber.obj U,
          v.left = a.val ≫ strictLocalLiftProjection s j ≫ f.left ∧
          (GeometricMorphism.inverseMate (Θ a)).app F (pointedEtaleGerm F s U u z) =
            pointedEtaleGerm F t U v z) ∧
      (∀ τ : Ωt ≃+* Ωt, Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ t = t →
        ∃ r : Aut (etaleGeometricPointMorphism t).direct,
          (∀ (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (U : S.Etale)
            (v : (pointSmallEtale t).fiber.obj U) (z : F.obj.obj (op U)),
            ∃ v' : (pointSmallEtale t).fiber.obj U,
              v'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ v.left ∧
              (GeometricMorphism.inverseMate r.hom).app F (pointedEtaleGerm F t U v z) =
                pointedEtaleGerm F t U v' z) ∧
          ∀ a : {a : Spec (.of Ωt) ⟶ strictHenselizationScheme s //
              a ≫ strictHenselizationStructuralMap s = t},
            ∃ a' : {a : Spec (.of Ωt) ⟶ strictHenselizationScheme s //
                a ≫ strictHenselizationStructuralMap s = t},
              a'.val = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ a.val ∧
              Θ a' = r.hom ≫ Θ a) := by
  sorry

end AlgebraicGeometry.Scheme
