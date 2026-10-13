/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Open transport of the normalized tensor comparison

Source: Stacks Project, perfect.tex, Tag 0DJ9 first paragraph and equation-bc
preceding Tag 0DJ8; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-normalized-transport).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange

/-- Transport the tensor comparison into derived pullback under open restriction.
This statement concerns the source complex and the pullback counit only; it has no
coefficient morphism and no target representative.

Proof: identify the four stalk rings by the open-immersion stalk isomorphisms.
Their structure maps agree by stalkMap_comp and the two restriction squares.
Exact open restriction and exact stalks, applied to e and a, identify the source
complexes in the derived categories of these rings. Transport derived extension
of scalars through these exact equivalences. Uniqueness with its pinned counit
identifies the base-derived tensor cohomology models. The cohomologyIso_smul
identities lift the comparison to the tensor algebra; extending to the fourth
stalk ring and forgetting scalars gives l. Exact restriction and the additive
restriction-stalk natural isomorphism induce the natural isomorphism ν on derived
stalk cohomology. On the K-flat representatives the derived pullback counit is
invertible. The model comparison_eq and localized_eq equations identify the two
comparisonIntoPullback maps with the same universal counit after ring transport.
The factorization identity for leftDerivedUnique in singleComplexOpenPullbackIso
identifies the intervening pullback comparison with θ, giving the displayed
square. Empty opens have no z; neither flatness over the base nor boundedness is
used. This proves compatibility before postcomposition with any coefficient.

Source: Stacks Project, perfect.tex, Tag 0DJ9 first paragraph and equation-bc
preceding Tag 0DJ8; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-normalized-transport). -/
theorem exists_singleComplexOpen_normalized_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (Q : CochainComplex
      (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace)) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (a : DerivedCategory.Q.obj Q ≅
      (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K)
    (hP : P.IsKFlat) (hQ : Q.IsKFlat)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let H := comparisonStalkCohomology X' z.val i
    let R := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    ∃ (ν : R ⋙ H₀ ⋙ F₀ ≅ H ⋙ F)
      (l : F₀.obj ((Arrow.mk (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ z Q hcQ i)).left) ≅
        F.obj ((Arrow.mk (comparisonIntoPullback f f' g g' sq z.val P hcP i)).left)),
      F₀.map (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
          (g.resLE V V' hV') j sq₀ z Q hcQ i ≫
        H₀.map ((derivedPullback j).map a.hom ≫ θ)) ≫
          ν.hom.app ((derivedPullback g').obj K) =
      l.hom ≫ F.map (comparisonIntoPullback f f' g g' sq z.val P hcP i ≫
        H.map ((derivedPullback g').map e.hom)) := by sorry

end AlgebraicGeometry
