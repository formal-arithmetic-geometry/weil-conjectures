/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.EtaleKFlatSupportData
public import Sheaf.AlgebraicGeometry.FlatSupportChainDiagram

/-!
# K-flat comparison of actual ordinary etale support sequences

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality, expanded by the agent-written
support diagram; Stacks Tags 03DB, 03ER, 06YU, 07A4, 0FPI, 0152 and 014A
(blueprint: lem-pur-etale-kflat-support-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] HomologicalComplex.monoidalCategoryStruct CategoryTheory.catToReflQuiver
universe u uC vC uD vD w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.KFlatSupportComparison


attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] Sheaf.monoidalCategory

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
  {Z P U : Scheme.{u}}


/-- Coefficient normalization of the canonical open quotient map.
Source: Stacks Tags 0FPI, 07A4, 0GL6; the projection-normalization argument of
lem-pur-etale-kflat-support-comparison
(blueprint: lem-pur-etale-kflat-support-projection).

Proof: apply computes_coefficient_projection from the K-flat open projection model.
Its ordinary map is the same total adjunct as OpenSupport.rightMap: transpose each
and use the ordinary adjunction triangle identity, or compare their total summands.
Use the canonical left-derived/exact-derived pullback comparison on both coefficient
categories. Naturality of the K-flat tensor model identifies its source normalization
with sourceThirdModel. The derived-functor unit and counit identify its target
normalization with targetThirdModel, with replacementIso using the inverse localized
augmentation. Expand scalarOpenIso and restrictionOpenIso. Cancel the intervening
left-derived pullback comparison isomorphisms. The model's scalar-mate formula is
then exactly restrictedProjection. All its bounds are the five stated bounds, and
pullback preserves them by exactness. The argument uses only A-linear complexes and
never requires a strict B-action or injectivity after restriction of scalars. -/
theorem support_comparison_projection [Finite A] [Finite B]
    (φ : A →+* B) (i : Z ⟶ P) [IsClosedImmersion i]
    (j : U ⟶ P) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory.Plus (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hTL : ∃ n : ℤ, ((scalarExtension φ P).obj L.obj).IsGE n)
    (_hRTL : ∃ n : ℤ, ((R(lowerStar (ModuleCat.{u + 1} B) j)).obj
      ((D(upperStar (ModuleCat.{u + 1} B) j)).obj
        ((scalarExtension φ P).obj L.obj))).IsGE n)
    (_hRL : ∃ n : ℤ, ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
      ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L.obj)).IsGE n)
    (_hTRL : ∃ n : ℤ, ((scalarExtension φ P).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L.obj))).IsGE n)
    (I : Complex A P) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)]
    (e : (localize A P).obj I ≅ L.obj)
    (Q : Complex A P)
    (π : Q ⟶ (CochainComplex.singleFunctor
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (scalarCoefficientSheaf φ P))
    [QuasiIso π] (hQ : (HomologicalComplex.quasiIso
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).kFlat Q)
    (_hQf : ∀ n : ℤ, ObjectProperty.flat (Q.X n))
    (F : Complex A P ⥤ Complex A P) (η : 𝟭 _ ⟶ F)
    [∀ K : Complex A P, (F.obj K).IsKInjective]
    [∀ (K : Complex A P) (n : ℤ), Injective ((F.obj K).X n)]
    [∀ K : Complex A P, QuasiIso (η.app K)]
    (hI : CochainComplex.IsKInjective ((pullComplex A j).obj I))
    (hJ : CochainComplex.IsKInjective ((pullComplex A j).obj (F.obj (Q ⊗ I))))
    :
    let N := Q ⊗ I
    let J := F.obj N
    let a := η.app N
    let v := OpenSupport.rightMap
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      Q I J a
    (localize A P).map v ≫
          (targetThirdModel φ j J L.obj
            (replacementIso a (tensorModel φ Q π hQ I L.obj e)) hJ).hom =
        (sourceThirdModel φ j Q π hQ I L.obj e hI).hom ≫ restrictedProjection φ j L.obj := by
  sorry


end AlgebraicGeometry.Etale.KFlatSupportComparison
