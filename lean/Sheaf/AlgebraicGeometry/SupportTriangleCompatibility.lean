/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.SupportTriangleConstruction
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# The three meanings for the specified support cone

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`def-pur-triangle-meaning` (blueprint: def-pur-triangle-meaning).

These predicates refer to the actual module functors, cone, and quotient map.
Triangle maps have all three specified components; uniqueness then expresses the
identity and composition laws. Base change specifies the map on the short exact
sequence, and all three components of the derived triangle isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Notational abbreviation for the existing category of constant-coefficient complexes.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
abbrev SupportComplex (X : Scheme.{u}) :=
  CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ

/-- A bounded below complex with injective terms; the lower bound is not fixed.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
def IsSupportInjectiveModel {X : Scheme.{u}} (I : SupportComplex Λ X) : Prop :=
  (∃ n : ℤ, I.IsStrictlyGE n) ∧ ∀ n : ℤ, Injective (I.X n)

/-- The termwise support map induced by a chain map, with no new choice.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
noncomputable def supportAMap {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion s] [IsOpenImmersion j]
    (hPair : IsCompl (Set.range s) (Set.range j))
    {I J : SupportComplex Λ X} (f : I ⟶ J) :
    supportedSectionsComplex Λ s j hPair I ⟶ supportedSectionsComplex Λ s j hPair J :=
  ((finiteClosedUpperShriek Λ s j ⋙ lowerStar (ModuleCat.{u + 1} Λ) s).mapHomologicalComplex
    (ComplexShape.up ℤ)).map f

/-- The termwise open-quotient map induced by a chain map.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
noncomputable def supportCMap {X U : Scheme.{u}} (j : U ⟶ X)
    {I J : SupportComplex Λ X} (f : I ⟶ J) :
    supportCComplex Λ j I ⟶ supportCComplex Λ j J :=
  ((upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
    (ComplexShape.up ℤ)).map f

variable {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
  (hPair : IsCompl (Set.range s) (Set.range j))

/-- A derived map of injective models gives the specified map of triangles.
Uniqueness, with the functor laws for the three component functors, includes identities
and composition. Source: blueprint def-pur-triangle-meaning
(blueprint: def-pur-triangle-meaning). -/
def SupportTriangleFunctoriality : Prop :=
  ∀ (I J : SupportComplex Λ X),
    IsSupportInjectiveModel Λ I → IsSupportInjectiveModel Λ J →
    ∀ (hqI : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I)))
      (hqJ : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair J)))
      (f : I ⟶ J),
      ∃! t : supportModelTriangle Λ s j hPair I hqI ⟶
          supportModelTriangle Λ s j hPair J hqJ,
        t.hom₁ = DerivedCategory.Q.map (supportAMap Λ s j hPair f) ∧
        t.hom₂ = DerivedCategory.Q.map f ∧
        t.hom₃ = DerivedCategory.Q.map (supportCMap Λ j f)

/-- Independence of the representing map and invertibility of the comparison between
injective models. The identity comparison therefore gives resolution independence;
uniqueness in functoriality gives its cocycle law.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
def SupportTriangleCanonicality : Prop :=
  ∀ (I J : SupportComplex Λ X),
    IsSupportInjectiveModel Λ I → IsSupportInjectiveModel Λ J →
    (∀ (f g : I ⟶ J), DerivedCategory.Q.map f = DerivedCategory.Q.map g →
      DerivedCategory.Q.map (supportAMap Λ s j hPair f) =
        DerivedCategory.Q.map (supportAMap Λ s j hPair g) ∧
      DerivedCategory.Q.map (supportCMap Λ j f) =
        DerivedCategory.Q.map (supportCMap Λ j g)) ∧
    (∀ (f : I ⟶ J), IsIso (DerivedCategory.Q.map f) →
      IsIso (DerivedCategory.Q.map (supportAMap Λ s j hPair f)) ∧
      IsIso (DerivedCategory.Q.map (supportCMap Λ j f)))

/-- The natural transformation comparing the open quotient functors in a commutative
square: pushforward base change followed by the inverse-image composition comparison.
Source: blueprint def-pur-triangle-meaning; Stacks Tag 09BN
(blueprint: def-pur-triangle-meaning). -/
noncomputable def supportOpenBaseChange
    {X' U' : Scheme.{u}} (v : X' ⟶ X) (vU : U' ⟶ U) (j' : U' ⟶ X')
    [Etale v] [Etale vU] (sq : vU ≫ j = j' ≫ v) :
    (upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j) ⋙
        upperStar (ModuleCat.{u + 1} Λ) v ⟶
      upperStar (ModuleCat.{u + 1} Λ) v ⋙
        (upperStar (ModuleCat.{u + 1} Λ) j' ⋙ lowerStar (ModuleCat.{u + 1} Λ) j') :=
  Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) j)
      (baseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq.symm)) ≫
    Functor.whiskerRight (((upperStarComp (ModuleCat.{u + 1} Λ) vU j).symm ≪≫
      upperStarCongr (ModuleCat.{u + 1} Λ) sq ≪≫
      upperStarComp (ModuleCat.{u + 1} Λ) j' v).hom)
      (lowerStar (ModuleCat.{u + 1} Λ) j')

/-- The canonical quotient comparison for a commutative open square and etale vertical
maps: pushforward base change followed by the inverse-image composition comparison.
Source: blueprint def-pur-triangle-meaning; Stacks Tag 09BN
(blueprint: def-pur-triangle-meaning). -/
noncomputable def supportOpenBaseChangeApp
    {X' U' : Scheme.{u}} (v : X' ⟶ X) (vU : U' ⟶ U) (j' : U' ⟶ X')
    [Etale v] [Etale vU] (sq : vU ≫ j = j' ≫ v)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) v).obj
        ((upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j).obj M) ⟶
      (upperStar (ModuleCat.{u + 1} Λ) j' ⋙ lowerStar (ModuleCat.{u + 1} Λ) j').obj
        ((upperStar (ModuleCat.{u + 1} Λ) v).obj M) :=
  (supportOpenBaseChange Λ j v vU j' sq).app M

-- Keep the existing instance binders of this public theorem for compatibility.
set_option linter.unusedSectionVars false in
/-- Naturality of the specified quotient comparison, used only to construct its chain map.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning).
Proof: expand the composite. Naturality of the base-change mate and of the
inverse-image composition isomorphism gives the square; reassociate the two composites. -/
theorem supportOpenBaseChangeApp_naturality
    {X' U' : Scheme.{u}} (v : X' ⟶ X) (vU : U' ⟶ U) (j' : U' ⟶ X')
    [Etale v] [Etale vU] (sq : vU ≫ j = j' ≫ v)
    {M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (f : M ⟶ N) :
    (upperStar (ModuleCat.{u + 1} Λ) v).map
        ((upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j).map f) ≫
      supportOpenBaseChangeApp Λ j v vU j' sq N =
    supportOpenBaseChangeApp Λ j v vU j' sq M ≫
      (upperStar (ModuleCat.{u + 1} Λ) j' ⋙ lowerStar (ModuleCat.{u + 1} Λ) j').map
        ((upperStar (ModuleCat.{u + 1} Λ) v).map f) := by
  exact (supportOpenBaseChange Λ j v vU j' sq).naturality f

/-- The same canonical quotient comparison on complexes, degree by degree.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
noncomputable def supportOpenBaseChangeComplex
    {X' U' : Scheme.{u}} (v : X' ⟶ X) (vU : U' ⟶ U) (j' : U' ⟶ X')
    [Etale v] [Etale vU] (sq : vU ≫ j = j' ≫ v) (I : SupportComplex Λ X) :
    ((upperStar (ModuleCat.{u + 1} Λ) v).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (supportCComplex Λ j I) ⟶
    supportCComplex Λ j' (((upperStar (ModuleCat.{u + 1} Λ) v).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) where
  f n := supportOpenBaseChangeApp Λ j v vU j' sq (I.X n)
  comm' n m _ := (supportOpenBaseChangeApp_naturality Λ j v vU j' sq (I.d n m)).symm

/-- Apply the recorded inverse image degree by degree to a complex.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
noncomputable def supportPullbackComplex {X' : Scheme.{u}} (v : X' ⟶ X)
    (I : SupportComplex Λ X) : SupportComplex Λ X' :=
  ((upperStar (ModuleCat.{u + 1} Λ) v).mapHomologicalComplex (ComplexShape.up ℤ)).obj I

/-- Etale pullback identifies the specified short exact sequences and the full triangles.
The middle component is the canonical localization comparison, the third is the
fibre-product base-change mate, and the first is induced on their kernels. Requiring
an isomorphism of triangles includes the signed boundary square.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
def SupportTriangleEtaleBaseChange : Prop :=
  ∀ {X' Z' U' : Scheme.{u}} (v : X' ⟶ X) (vZ : Z' ⟶ Z) (vU : U' ⟶ U)
    (s' : Z' ⟶ X') (j' : U' ⟶ X'),
    ∀ [Etale v] [Etale vU] [IsClosedImmersion s'] [IsOpenImmersion j'] [QuasiCompact j'],
    ∀ (hPair' : IsCompl (Set.range s') (Set.range j'))
      (_hs : IsPullback vZ s' s v) (hj : IsPullback vU j' j v)
      (I : SupportComplex Λ X), IsSupportInjectiveModel Λ I →
    ∀ (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I))),
    IsSupportInjectiveModel Λ (supportPullbackComplex Λ v I) ∧
      ∃ (hq' : IsIso (DerivedCategory.Q.map
          (supportConeQuotient Λ s' j' hPair' (supportPullbackComplex Λ v I))))
        (e : (supportModelSequence Λ s j hPair I).map
            ((upperStar (ModuleCat.{u + 1} Λ) v).mapHomologicalComplex (ComplexShape.up ℤ)) ≅
          supportModelSequence Λ s' j' hPair' (supportPullbackComplex Λ v I))
        (t : (upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategory.mapTriangle.obj
            (supportModelTriangle Λ s j hPair I hq) ≅
          supportModelTriangle Λ s' j' hPair' (supportPullbackComplex Λ v I) hq'),
        e.hom.τ₂ = 𝟙 (supportPullbackComplex Λ v I) ∧
        e.hom.τ₃ = supportOpenBaseChangeComplex Λ j v vU j' hj.w I ∧
        t.hom.hom₁ = (upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryFactors.hom.app
            (supportedSectionsComplex Λ s j hPair I) ≫
          DerivedCategory.Q.map e.hom.τ₁ ∧
        t.hom.hom₂ = (upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryFactors.hom.app I ∧
        t.hom.hom₃ = (upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategoryFactors.hom.app
            (supportCComplex Λ j I) ≫
          DerivedCategory.Q.map e.hom.τ₃

/-- The conjunction of the three concrete meanings, on the canonical support cone.
Source: blueprint def-pur-triangle-meaning (blueprint: def-pur-triangle-meaning). -/
def supportTriangleMeaning : Prop :=
  SupportTriangleCanonicality Λ s j hPair ∧ SupportTriangleFunctoriality Λ s j hPair ∧
    SupportTriangleEtaleBaseChange Λ s j hPair

end AlgebraicGeometry.ProEtale
