/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverPullback
public import WeilConjectures.ConstructibleSheaf.EllMonodromy
public import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Pullback of complexes with finite `ℓ`-group monodromy

The pullback `f^* E` along any morphism of schemes `f : V ⟶ U` of a complex `E` with finite
`ℓ`-group monodromy has finite `ℓ`-group monodromy
(`AlgebraicGeometry.Etale.HasFiniteEllMonodromy.upperStar'`): homology commutes with the exact
functor `f^*`, so boundedness and finite local constancy are preserved, and the base change
`P ×_U V` of a Galois cover `P ⟶ U` trivializing the homology sheaves of `E` is a Galois cover
with the same group trivializing the homology sheaves of `f^* E`, since `(P ×_U V ⟶ V)^* f^*` is
`(P ×_U V ⟶ P)^* (P ⟶ U)^*` and pullbacks of constant sheaves are constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The pullback of a complex with finite `ℓ`-group monodromy has finite `ℓ`-group monodromy. -/
lemma HasFiniteEllMonodromy.upperStar' {ℓ : ℕ} {U V : Scheme.{u}} (f : V ⟶ U)
    {E : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE : HasFiniteEllMonodromy ℓ E) :
    HasFiniteEllMonodromy ℓ (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) := by
  obtain ⟨⟨a, b, hab⟩, hfl, G, _, _, hG, c, hc⟩ := hE
  let e (n : ℤ) :
      ((f)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.homologyFunctor _ n).obj E) ≅
      (DerivedCategory.homologyFunctor _ n).obj
        (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) :=
    (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app E
  refine ⟨⟨a, b, fun n hn ↦
    (((f)^*[ModuleCat.{u + 1} Λ]).map_isZero (hab n hn)).of_iso (e n).symm⟩, fun n ↦ ?_,
    G, inferInstance, inferInstance, hG, c.pullback f, fun n ↦ ?_⟩
  · have := hfl n
    have := Scheme.IsFiniteLocallyConstantSheaf.upperStar f
      ((DerivedCategory.homologyFunctor _ n).obj E)
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso (e n)
  · set H := (DerivedCategory.homologyFunctor _ n).obj E
    have := hc n
    have := Sheaf.IsConstant.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst c.π f)
      ((c.π)^*[ModuleCat.{u + 1} Λ].obj H)
    let i : ((pullback.fst c.π f)^*[ModuleCat.{u + 1} Λ]).obj
        ((c.π)^*[ModuleCat.{u + 1} Λ].obj H) ≅
        ((pullback.snd c.π f)^*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.homologyFunctor _ n).obj
            (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E)) :=
      ((upperStarComp _ (pullback.fst c.π f) c.π).app H).symm ≪≫
        eqToIso (congrArg (fun m ↦ ((m)^*[ModuleCat.{u + 1} Λ]).obj H) pullback.condition) ≪≫
        (upperStarComp _ (pullback.snd c.π f) f).app H ≪≫
        ((pullback.snd c.π f)^*[ModuleCat.{u + 1} Λ]).mapIso (e n)
    exact Sheaf.isConstant_congr (Limits.pullback c.π f).smallEtaleTopology i

end AlgebraicGeometry.Etale
