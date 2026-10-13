module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/--
The morphism-level coherence underlying the raw pullback comparison.  It is obtained by
expanding the derived adjunction comparison, the transition map, and the shift comparison;
naturality of the adjunction unit and the triangle identity identify the two composites.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-transition-to-hom-core).
-/
theorem higherDirectImageRawTransition_toHom_core
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale) :
    (higherDirectImagePresheafToHom Λ h' q K').app (op U) ∘
        (higherDirectImageRawTrianglePullback Λ a h h' w q K K' v U) =
      (higherDirectImagePresheafToHom Λ h q K).app (op U) ≫
        (Functor.whiskerLeft (freeSheaf Λ S).op (preadditiveYoneda.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map
            (lowerStarPlusTransition Λ a h h' w K ≫
              R+((h')_*[ModuleCat.{u + 1} Λ]).map v)))).app (op U) := by
  sorry

end AlgebraicGeometry.Etale
