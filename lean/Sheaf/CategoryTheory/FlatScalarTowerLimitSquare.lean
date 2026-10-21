/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.CategoryTheory.FlatRingedDiagramRestriction
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.CategoryTheory.ExactAdjointTowerModels
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.KInjectiveExactSquareComparison
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Flat scalars and the normalized direct-image/strict-limit square

Source: blueprint main-20261015, proper base change, completed exchange coherence,
second paragraph; scalar supplement using Stacks Tags 0A07, 08BJ, 070I, 070Y and 070K
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square).

The auxiliary structures merely bundle the universal units and their normalization
identities. Ordinary scalar-limit maps are fixed by `limit.post`, which sends a
compatible family to the same family. Positive tower level n+1 is indexed by n : ℕ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w uA uB uA' uB' vA vB vA' vB'

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ExactAdjointTowerModels

namespace CategoryTheory.FlatScalarTowerLimit

section Normalizations

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']

/-- The ordinary and derived scalar comparison, retaining both exact-localization
factors and the equation with universal right-derived units on K-injectives.
Source: Stacks Tags 070I, 070Y and 070K, scalar supplement to completed exchange coherence
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
structure ScalarComparison
    (F' : A' ⥤ B') (F : A ⥤ B) (r : A' ⥤ A) (s : B' ⥤ B)
    [F'.Additive] [F.Additive] [r.Additive] [s.Additive]
    (rD : DerivedCategory A' ⥤ DerivedCategory A)
    (sD : DerivedCategory B' ⥤ DerivedCategory B)
    (qr : DerivedCategory.Q ⋙ rD ≅ r.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qs : DerivedCategory.Q ⋙ sD ≅ s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (M' : DerivedModel (F'.mapHomologicalComplex (.up ℤ)))
    (M : DerivedModel (F.mapHomologicalComplex (.up ℤ))) where
  ordinary : F' ⋙ s ≅ r ⋙ F
  derived : M'.functor ⋙ sD ≅ rD ⋙ M.functor
  normalized : ∀ I : CochainComplex A' ℤ, I.IsKInjective →
    sD.map (M'.unit.app I) ≫ derived.hom.app (DerivedCategory.Q.obj I) ≫
        M.functor.map (qr.hom.app I) =
      qs.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app I) ≫
        M.unit.app ((r.mapHomologicalComplex (.up ℤ)).obj I)

/-- The additive structure of ordinary limit, supplied by Mathlib's limit-preservation
criterion, so additivity is not an extra hypothesis of the scalar square.
Source: Stacks Tag 02MZ (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev limitAdditive {E : Type uA} [Category.{vA} E] [Abelian E]
    [HasLimitsOfShape ℕᵒᵖ E] :
    (lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [instance] limitAdditive

variable [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

/-- The canonical direct-image/limit comparison, with its ordinary projection
characterization and common-composite universal-unit normalization.
Source: Stacks Tag 0A07, as specified by ringedTowerPushforwardLimitComparison
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
structure PushforwardComparison
    (F : A ⥤ B) [F.Additive]
    (MF : DerivedModel (F.mapHomologicalComplex (.up ℤ)))
    (MT : DerivedModel (tower F))
    (LA : DerivedModel ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)))
    (LB : DerivedModel ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ))) where
  ordinary : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
    (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⋙ lim
  projections : ∀ T : ℕᵒᵖ ⥤ A, ordinary.hom.app T = limit.post T F
  derived : LA.functor ⋙ MF.functor ≅ MT.functor ⋙ LB.functor
  normalized : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    MF.unit.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        MF.functor.map (LA.unit.app I) ≫ derived.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app I) ≫
        LB.unit.app ((tower F).obj I) ≫ LB.functor.map (MT.unit.app I)

end Normalizations

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}

/-- The RU module category, exactly the recorded ringed-site module category.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev modulesRU (x : FlatRingedDiagramInput K H) := ringedSiteModules.{u}
  ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.RU)

/-- The SU module category, exactly the recorded ringed-site module category.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev modulesSU (x : FlatRingedDiagramInput K H) := ringedSiteModules.{u}
  ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.SU)

/-- The RV module category, exactly the recorded ringed-site module category.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev modulesRV (x : FlatRingedDiagramInput K H) := ringedSiteModules.{u}
  ((sheafCompose K (forget₂ CommRingCat RingCat)).obj x.RV)

/-- The SV module category, exactly the recorded ringed-site module category.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev modulesSV (x : FlatRingedDiagramInput K H) := ringedSiteModules.{u}
  ((sheafCompose K (forget₂ CommRingCat RingCat)).obj x.SV)

/-- Actual restriction of scalars at U, using Mathlib's construction.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev scalarU (x : FlatRingedDiagramInput K H) : modulesSU x ⥤ modulesRU x :=
  SheafOfModules.restrictScalars.{u}
    ((sheafCompose H (forget₂ CommRingCat RingCat)).map x.aU)

/-- Actual restriction of scalars at V, using Mathlib's construction.
Source: Stacks Tag 03CV (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev scalarV (x : FlatRingedDiagramInput K H) : modulesSV x ⥤ modulesRV x :=
  SheafOfModules.restrictScalars.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).map x.aV)

/-- Flat scalar restriction commutes with derived strict inverse limit, and the
normalized direct-image/limit square commutes as an equality on every derived tower.
`χ` and `d` are the specified flat comparisons, normalized by their ordinary identity
and universal units. `κR` and `κS` are the specified comparisons of Tag 0A07.
The output supplies the ordinary family-identity and the derived normalized comparison
at both U and V. No finite reduction, completeness, or exact-products condition occurs.

Source: blueprint main-20261015, completed exchange coherence proof, second paragraph;
scalar supplement using Stacks Tags 0A07 and 08BJ
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square).

Proof plan (the eight steps of the DAG node):
1. On ordinary module towers, restrict the action on each compatible family. Gluing
   is componentwise, so the same-family map is an isomorphism. Its projections are
   exactly limit.post. Use lem-weil-pbc-flat-ringed-diagram-restriction for exactness,
   preservation of K-injectives, and the specified scalar/direct-image comparison.
2. Use lem-weil-pbc-diagram-site-realization and prop-pur-kinjective-resolutions-exist
   for enough K-injectives in the four tower categories and four module categories.
   Transport preserves acyclicity and homotopies. Use lem-weil-pbc-kinjective-total-derived
   and lem-weil-pbc-ringed-strict-tower-homotopy-limit for universal units and computation.
3. Apply lem-weil-pbc-kinjective-exact-square-comparison to ordinary inverse limit and
   restriction at U and V, retaining the unique same-family comparison and both units.
   This gives the output scalar comparisons with exactly the displayed normalization.
4. By lem-trf-geometric-inverse-image-exact, transported inverse image is exact.
   Its adjunction and lem-weil-pbc-right-adjoint-preserves-kinjective show that direct
   image preserves K-injectives, also on towers. The exact constant tower functor is
   left adjoint to ordinary limit, so limit also preserves K-injectives.
5. The n-th projections of the two ordinary square composites agree by naturality
   of the specified scalar/direct-image comparison at the projection of the tower.
   Limit projections determine the map, giving the ordinary square degreewise.
6. Read the unit normalizations of κR, κS from
   lem-weil-ringed-tower-pushforward-limit-comparison and those of χ,d from
   lem-weil-pbc-flat-ringed-diagram-restriction. All units needed on the common
   K-injective model are invertible by steps 2 and 4.
7. Precompose the desired derived square with the source composite unit on a
   K-injective tower. Substitute the three normalization equations; naturality moves
   comparisons past units. Both sides reduce to the target composite unit after Q
   of the corresponding side of step 5. Cancel the source unit to obtain the square.
8. Every derived tower is isomorphic to QI for a K-injective I. Naturality of every
   comparison transports step 7 along that isomorphism to all objects and morphisms.
-/
theorem flatScalarTowerLimitSquare
    (x : FlatRingedDiagramInput K H)
    [HasDerivedCategory.{w} (modulesRU x)]
    [HasDerivedCategory.{w} (modulesSU x)]
    [HasDerivedCategory.{w} (modulesRV x)]
    [HasDerivedCategory.{w} (modulesSV x)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ modulesRU x)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ modulesSU x)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ modulesRV x)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ modulesSV x)]
    (FR : DerivedModel (x.R.morphism.modules.mapHomologicalComplex (.up ℤ)))
    (TR : DerivedModel (tower x.R.morphism.modules))
    (FS : DerivedModel (x.S.morphism.modules.mapHomologicalComplex (.up ℤ)))
    (TS : DerivedModel (tower x.S.morphism.modules))
    (LRU : DerivedModel
      ((lim : (ℕᵒᵖ ⥤ modulesRU x) ⥤ modulesRU x).mapHomologicalComplex (.up ℤ)))
    (LSU : DerivedModel
      ((lim : (ℕᵒᵖ ⥤ modulesSU x) ⥤ modulesSU x).mapHomologicalComplex (.up ℤ)))
    (LRV : DerivedModel
      ((lim : (ℕᵒᵖ ⥤ modulesRV x) ⥤ modulesRV x).mapHomologicalComplex (.up ℤ)))
    (LSV : DerivedModel
      ((lim : (ℕᵒᵖ ⥤ modulesSV x) ⥤ modulesSV x).mapHomologicalComplex (.up ℤ)))
    (rU : DerivedCategory (modulesSU x) ⥤ DerivedCategory (modulesRU x))
    (rtU : DerivedCategory (ℕᵒᵖ ⥤ modulesSU x) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ modulesRU x))
    (qU : DerivedCategory.Q ⋙ rU ≅
      (scalarU x).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qtU : DerivedCategory.Q ⋙ rtU ≅ tower (scalarU x) ⋙ DerivedCategory.Q)
    (rV : DerivedCategory (modulesSV x) ⥤ DerivedCategory (modulesRV x))
    (rtV : DerivedCategory (ℕᵒᵖ ⥤ modulesSV x) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ modulesRV x))
    (qV : DerivedCategory.Q ⋙ rV ≅
      (scalarV x).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qtV : DerivedCategory.Q ⋙ rtV ≅ tower (scalarV x) ⋙ DerivedCategory.Q)
    (χ : ScalarComparison x.S.morphism.modules x.R.morphism.modules
      (scalarU x) (scalarV x) rU rV qU qV FS FR)
    (ordinaryχ : ∀ N : modulesSU x,
      (SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).map
          (χ.ordinary.hom.app N) ≫
        x.R.morphism.underlying.hom.app ((scalarU x).obj N) =
      x.S.morphism.underlying.hom.app N ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((SheafOfModules.toSheaf _ ⋙ sheafCompose H (forget AddCommGrpCat)).obj N))
            x.sameDirect.symm))
    (d : ScalarComparison
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj x.S.morphism.modules)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj x.R.morphism.modules)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarU x))
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarV x)) rtU rtV qtU qtV TS TR)
    (ordinaryd : ∀ (T : ℕᵒᵖ ⥤ modulesSU x) (n : ℕᵒᵖ),
      (d.ordinary.hom.app T).app n = χ.ordinary.hom.app (T.obj n))
    (κR : PushforwardComparison x.R.morphism.modules FR TR LRU LRV)
    (κS : PushforwardComparison x.S.morphism.modules FS TS LSU LSV) :
    ∃ (lambdaU : ScalarComparison
        (lim : (ℕᵒᵖ ⥤ modulesSU x) ⥤ modulesSU x)
        (lim : (ℕᵒᵖ ⥤ modulesRU x) ⥤ modulesRU x)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarU x)) (scalarU x) rtU rU qtU qU LSU LRU)
      (lambdaV : ScalarComparison
        (lim : (ℕᵒᵖ ⥤ modulesSV x) ⥤ modulesSV x)
        (lim : (ℕᵒᵖ ⥤ modulesRV x) ⥤ modulesRV x)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarV x)) (scalarV x) rtV rV qtV qV LSV LRV),
      (∀ T : ℕᵒᵖ ⥤ modulesSU x, lambdaU.ordinary.hom.app T = limit.post T (scalarU x)) ∧
      (∀ T : ℕᵒᵖ ⥤ modulesSV x, lambdaV.ordinary.hom.app T = limit.post T (scalarV x)) ∧
      ∀ Z : DerivedCategory (ℕᵒᵖ ⥤ modulesSU x),
        rV.map (κS.derived.hom.app Z) ≫ lambdaV.derived.hom.app (TS.functor.obj Z) ≫
            LRV.functor.map (d.derived.hom.app Z) =
          χ.derived.hom.app (LSU.functor.obj Z) ≫
            FR.functor.map (lambdaU.derived.hom.app Z) ≫ κR.derived.hom.app (rtU.obj Z) := by
  sorry

end CategoryTheory.FlatScalarTowerLimit
