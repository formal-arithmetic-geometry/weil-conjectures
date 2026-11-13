/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

import WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonBijective
import WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonNaturality

/-!
# Comparing free-representable derived Hom with cyclic cohomology

Source: Stacks Project, Tag 03Q8, and the free-representable interpretation of sections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Free-representable derived Hom computes cohomology on the fibre product, and geometric
restriction to zero forces the corresponding presheaf restriction to zero.

Source: Stacks Project, Tag 03Q8, the restricted cohomology presheaf; the free-sheaf
adjunction argument in
`WeilConjectures/SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/FreeSheaf.lean`. -/
theorem exists_cyclicDerivedHom_cohomology_comparison {X Y : Scheme.{u}}
    (h : Y ⟶ X) (e q : ℕ) :
    let P := (uliftYoneda.{u + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj (Y.constantZMod e))⟦(q : ℤ)⟧)
    ∀ W : X.Etale,
      ∃ E : P.obj (op W) ≃+ Sheaf.H ((pullback h W.hom).constantZMod e) q,
        ∀ (V : X.Etale) (v : V ⟶ W) (ξ : P.obj (op W)),
          cohomologyMap
            (pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp)
              (by simp)) _ q (E ξ) = 0 → P.map v.op ξ = 0 := by
  dsimp only
  intro W
  have hbij (V : X.Etale) : Function.Bijective (cyclicRepresentableCohomologyMap h e q V) := by
    let i := (Sheaf.functorH _ q).mapIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
        (pullback.fst h V.hom)).app (AddCommGrpCat.of (ULift (ZMod e))))
    exact i.addCommGroupIsoToAddEquiv.bijective.comp
      (abelianRepresentableCohomologyMap_bijective h (Y.constantZMod e) q V)
  let E := AddEquiv.ofBijective (cyclicRepresentableCohomologyMap h e q W) (hbij W)
  refine ⟨E, ?_⟩
  intro V v ξ hz
  apply (hbij V).injective
  rw [map_zero]
  have hn := cyclicRepresentableCohomologyMap_naturality h e q W V v ξ
  change cohomologyMap _ _ q (cyclicRepresentableCohomologyMap h e q W ξ) = 0 at hz
  dsimp only at hn
  rw [hz, map_zero] at hn
  exact hn.symm

end AlgebraicGeometry.Etale
