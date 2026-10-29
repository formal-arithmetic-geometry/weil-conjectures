/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap

/-!
# The projective-line adjunction

Let `S` be a scheme on which the exponent of the finite coefficient ring `Λ` is invertible and
`q : ℙ¹_S ⟶ S` the projective line. The decomposition `Rq_* Λ(1)[2] ≅ Λ_S(1)[2] ⊕ Λ_S`
(`AlgebraicGeometry.Etale.isIso_projectiveLineDecompositionMap`, blueprint
`thm-amb-p1-decomposition`) defines the trace `t_q : Rq_! Λ(1)[2] ⟶ Λ_S`
(`AlgebraicGeometry.Etale.projectiveLineLowerShriekTrace`, blueprint `def-amb-p1-trace`), and
with it the morphisms

`ε_K : Rq_!(q^* K(1)[2]) ≅ Rq_!(Λ(1)[2] ⊗ᴸ Lq^* K) ≅ Rq_! Λ(1)[2] ⊗ᴸ K ⟶ Λ_S ⊗ᴸ K ≅ K`

(`AlgebraicGeometry.Etale.projectiveLineCounit`), the inverse of the projection map followed by
the trace. Blueprint `det-sp-p1-adjunction` (subsection `sk-prop-geo-p1-adjunction`) shows,
through the cycle class of the diagonal and the triangle identities, that `ε` is the counit of
an adjunction `Rq_! ⊣ Lq^*(1)[2]` on the whole derived categories. This is recorded here, for the
subsection `sk-prop-geo-p1-adjunction` to prove it; its compatibility with base change is
`WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunctionBaseChange`.

## Main definitions

- `AlgebraicGeometry.Etale.projectiveLineLowerShriekTrace`
- `AlgebraicGeometry.Etale.projectiveLineTwistShiftIso`
- `AlgebraicGeometry.Etale.projectiveLineCounit`

## Main statements

- `AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`

## Implementation notes

The blueprint works with `Rq_*`; for the proper `q` it is `Rq_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`), and the projection
formula of `Rq_*` is the one of `Rq_!` through this identification
(`AlgebraicGeometry.Etale.projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar`).
The identification `q^* K(1)[2] ≅ Λ(1)[2] ⊗ᴸ Lq^* K` is the commutation of the derived tensor
product with shifts followed by the braiding; the statement that `ε` is a counit does not depend
on this choice, since a natural automorphism of the right adjoint changes the counit of an
adjunction into the counit of another one. Likewise, the sign of the trace
(`AlgebraicGeometry.Etale.projectiveLineTrace` is `-t_q`) does not matter: negating unit and
counit of an adjunction of additive functors gives an adjunction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- Braid étale sheaves through `Etale.sheafBraidedCategory`, as the generic definitions of the
-- derived tensor product do.
attribute [local instance 20000] Etale.sheafBraidedCategory

/-- The *trace counit* `Rf_!(G K) ≅ Rf_!(T ⊗ᴸ Lf^* K) ≅ Rf_! T ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K` of a morphism
`t : Rf_! T ⟶ Λ_Y`, for a functor `G` with identifications `γ_K : G K ≅ T ⊗ᴸ Lf^* K`: the
inverse of the projection map (`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`)
followed by `t` tensored with `K` and the left unitor. For the projective line, `T = Λ(1)[2]`,
`G = Lq^*(1)[2]` and `t` is the trace (`AlgebraicGeometry.Etale.projectiveLineCounit`). -/
noncomputable def lowerShriekTraceCounit {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (t : (R(f)_![ModuleCat.{u + 1} Λ]).obj T ⟶ 𝟙_ _)
    {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : ∀ K, G.obj K ≅ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj T).obj
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(f)_![ModuleCat.{u + 1} Λ]).obj (G.obj K) ⟶ K :=
  haveI := isIso_projectionMap_of_finite Λ f
  (R(f)_![ModuleCat.{u + 1} Λ]).map (γ K).hom ≫
    inv (((projectionMap (ModuleCat.{u + 1} Λ) f).app T).app K) ≫ t ▷ K ≫ (λ_ K).hom

section Counit

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] (S : Scheme.{u})
  [HasInvertibleExponent Λ S]

/-- Blueprint `def-amb-p1-trace`: the trace of the projective line `q : ℙ¹_S ⟶ S` on the
compactly supported direct image, `t_q : Rq_! Λ(1)[2] ⟶ Λ_S`: the trace
`AlgebraicGeometry.Etale.projectiveLineTrace` of `Rq_*`, the projection onto the summand `Λ_S`
of the decomposition `Rq_* Λ(1)[2] ≅ Λ_S(1)[2] ⊕ Λ_S`, read through `Rq_! ≅ Rq_*`. -/
noncomputable def projectiveLineLowerShriekTrace :
    (R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ⟶ 𝟙_ _ :=
  (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ)
      (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).hom.app _ ≫
    projectiveLineTrace Λ S (isIso_projectiveLineDecompositionMap Λ S)

/-- The identification `q^* K(1)[2] ≅ Λ(1)[2] ⊗ᴸ Lq^* K` on the projective line, for `K` on `S`:
the shift is moved into the second factor of `Lq^* K ⊗ᴸ Λ(1)`, and the factors are exchanged by
the braiding of the derived tensor product (`AlgebraicGeometry.Etale.derivedTensorBraiding`), so
that the identification is compatible with pullback. -/
noncomputable def projectiveLineTwistShiftIso
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1).obj
        ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) ℙ(Option (ULift.{u} (Fin 1)); S)).obj
        ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧)).obj
        ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (((derivedTensor (ModuleCat.{u + 1} Λ) ℙ(Option (ULift.{u} (Fin 1)); S)).obj
      ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K)).commShiftIso
      (2 : ℤ)).symm.app _ ≪≫
    ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) ℙ(Option (ULift.{u} (Fin 1)); S)).app _).app _

/-- The candidate counit `ε_K : Rq_!(q^* K(1)[2]) ⟶ K` of the projective-line adjunction
(blueprint `def-amb-p1-trace`): the identification `q^* K(1)[2] ≅ Λ(1)[2] ⊗ᴸ Lq^* K`
(`AlgebraicGeometry.Etale.projectiveLineTwistShiftIso`), the inverse of the projection map
`Rq_! Λ(1)[2] ⊗ᴸ K ⟶ Rq_!(Λ(1)[2] ⊗ᴸ Lq^* K)`, the trace
`AlgebraicGeometry.Etale.projectiveLineLowerShriekTrace` tensored with `K`, and the left
unitor. -/
noncomputable def projectiveLineCounit
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1).obj
          ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K)) ⟶ K :=
  lowerShriekTraceCounit Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
    ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧)
    (projectiveLineLowerShriekTrace Λ S)
    (G := L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
      twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)
    (projectiveLineTwistShiftIso Λ S) K

/-- Compatibility required from `sk-prop-geo-p1-adjunction` (to be proved there):
blueprint `det-sp-p1-adjunction` (with `thm-amb-p1-adjunction`).

**The projective-line adjunction.** For a scheme `S` on which the exponent of `Λ` is invertible
and `q : ℙ¹_S ⟶ S`, the morphisms `ε_K : Rq_!(q^* K(1)[2]) ⟶ K` built from the trace
(`AlgebraicGeometry.Etale.projectiveLineCounit`) are the counit of an adjunction
`Rq_! ⊣ Lq^*(1)[2]` on the whole derived categories. In the blueprint the unit is built from the
cycle class of the diagonal, and the triangle identities follow from the two diagonal integrals
`lem-amb-p1-diagonal-integrals`. -/
theorem exists_projectiveLineAdjunction :
    ∃ adj : R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
        L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
          twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1,
      ∀ K, adj.counit.app K = projectiveLineCounit Λ S K :=
  sorry

end Counit

end Etale

end AlgebraicGeometry
