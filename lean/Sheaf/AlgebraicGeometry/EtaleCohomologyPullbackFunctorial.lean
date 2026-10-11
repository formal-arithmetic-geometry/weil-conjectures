import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Functoriality of pullback on étale cohomology

Source: literature/stacks-project/cohomology.tex, Section Tag 01F7 (blueprint:
lem-weil-pbc-cohomology-pullback-functorial)
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The pullback on étale cohomology is independent of resolutions and functorial.
(blueprint: lem-weil-pbc-cohomology-pullback-functorial)
-/
theorem cohomologyPullbackFunctorial {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (∀ {G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (φ : F ⟶ G) (x : Sheaf.H F q),
      cohomologyMap (u ≫ v) G q (Sheaf.H.map φ q x) =
        Sheaf.H.map (((u ≫ v)^*[AddCommGrpCat.{u + 1}]).map φ) q
          (cohomologyMap (u ≫ v) F q x)) ∧
    (∀ (x : Sheaf.H F q),
      cohomologyMap u ((v)^*[AddCommGrpCat.{u + 1}].obj F) q
          (cohomologyMap v F q x) =
        Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} u v).hom.app F) q
          (cohomologyMap (u ≫ v) F q x)) ∧
    (∀ (x : Sheaf.H F q),
      Sheaf.H.map ((upperStarId AddCommGrpCat.{u + 1} Z).hom.app F) q
        (cohomologyMap (𝟙 Z) F q x) = x) := by
  sorry

end AlgebraicGeometry.Etale
