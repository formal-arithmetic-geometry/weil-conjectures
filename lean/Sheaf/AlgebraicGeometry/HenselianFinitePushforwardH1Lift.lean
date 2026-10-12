module
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
/-! # Finite pushforward H¹ lifting over a henselian local ring

Source: Stacks Project, Lemma 0A5H, finite-pushforward lifting argument.
(blueprint: lem-weil-pbc-henselian-finite-pushforward-h1-lift) -/
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
/-- Finite pushforward classes on the closed fibre are carried, after a morphism to a
module sheaf, to the restriction of a class on the total space.

Proof steps (Stacks Project, Lemma 0A5H):
1. Use permanence of finite morphisms and finite exchange to identify the finite
   pushforward after passage to the residue fibre.
2. Pull back the constructible constant sheaf and apply finite pushforward
   cohomology, followed by edge-map base change, to compare the degree-one
   classes on the total space and on the closed fibre.
3. Apply finite étale lifting over the henselian local ring and the H¹ torsor
   comparison to obtain a class `z` on the total finite pushforward whose
   restriction represents `x`.
4. Identify constant-module sheaves with their underlying abelian sheaves and
   use cohomology pullback functoriality.  The inverse-image module exactness
   comparison supplies the canonical map appearing in the conclusion.
5. Naturality of the cohomology map induced by `ψ` then gives the displayed
   equality between the restricted image of `x` and the restriction of
   `H¹(ψ)(z)`.

Source: Stacks Project, Lemma 0A5H, finite-pushforward lifting argument.
(blueprint: lem-weil-pbc-henselian-finite-pushforward-h1-lift)
-/
theorem finite_pushforward_H_one_lift_of_henselianLocalRing
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (i : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (sq : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V : Scheme.{u}} (h : V ⟶ Y) [IsFinite h] [LocallyOfFinitePresentation h]
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (ψ : (h)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf V.smallEtaleTopology _).obj M) ⟶ J)
    (x : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj
        ((h)_*[ModuleCat.{u + 1} Λ].obj
          ((constantSheaf V.smallEtaleTopology _).obj M)))) 1) :
    ∃ z : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((h)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf V.smallEtaleTopology _).obj M))) 1,
      Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).map ((i)^*[ModuleCat.{u + 1} Λ].map ψ)) 1 x =
        Sheaf.H.map
          (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv _ _).symm
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
              AddCommGrpCat.{u + 1})).map
                ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app J))) 1
          (cohomologyMap i _ 1
            (Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
              AddCommGrpCat.{u + 1})).map ψ) 1 z)) := by
  sorry

end AlgebraicGeometry.Etale
