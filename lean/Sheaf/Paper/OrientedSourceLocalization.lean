/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.Paper.OrientedConstructibleSheaf
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.CategoryTheory.Sites.OrientedProductSliceLocalization
import Sheaf.Paper.OrientedProductPointsConservative
import Mathlib.Topology.Constructible
import Sheaf.CategoryTheory.Sites.ToposComplementFactorization
import Sheaf.CategoryTheory.Sites.ToposComplementModuleStalks
import Sheaf.Paper.OrientedConstructibleSheafVanishing
import Sheaf.TraceFormula.EtaleClosedComplementSets

/-!
# Open and closed source localization on the vanishing topos

Source: Orgogozo, Modifications et cycles proches sur une base générale, §§8, 9.3;
ILO XI §§1.4, 1.10(b); Stacks 08LW, 08LY, 0152
(blueprint: lem-trf-oriented-source-localization).

The module operations use the recorded oriented-product presentation of constant-ring
modules. Its identity second scheme map presents the vanishing topos. Both inverse images
are the recorded canonical restriction, with the identity composite normalized by equality.
The extension functors are characterized by their adjunctions to these inverse images.

## Main definitions

* `Modules`, `sourcePull`, `sourceMap`: the recorded module presentation and source maps.
* `Operations`: the four exact functors and their two adjunctions, as conclusion data.
* `counitComplex`, `unitComplex`, `complexSequence`: the degreewise localization sequence.

## Main statements

* `sourceLocalization`: complementary source subtopoi, constructibility, and localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedSourceLocalization

/-- Constant-coefficient modules on the recorded oriented presentation of `V_f`.
Source: ILO XI §1.7; Lu--Zheng, definition following Theorem 4.27
(blueprint: lem-trf-oriented-source-localization). -/
abbrev Modules {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type v) [CommRing Λ] :=
  OrientedConstructibleSheaf.Modules f (𝟙 S) Λ

/-- Mathlib's concrete additive sheafification at the containing site universe.
The explicit instance avoids the unrelated successor-universe Grothendieck-category
instance; it makes no restriction on the independent scheme and coefficient sizes.
Source: Stacks 03CY (blueprint: lem-trf-oriented-source-localization). -/
instance additiveSheafification {X S : Scheme.{u}} (f : X ⟶ S) :
    HasSheafify (OrientedConstructibleSheaf.productTopology.{u, v} f (𝟙 S))
      AddCommGrpCat.{max (u + 1) v} :=
  instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover.{
    max (u + 1) v, max (u + 1) v + 1, max (u + 1) v, max (u + 1) v,
    max (u + 1) v} _ _

/-- The inherited abelian structure, with all sheafification universes explicit.
Source: Stacks 03CY (blueprint: lem-trf-oriented-source-localization). -/
instance modulesAbelian {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type v) [CommRing Λ] :
    Abelian (Modules f Λ) :=
  @SheafOfModules.instAbelian.{max (u + 1) v, max (u + 1) v,
    max (u + 1) v, max (u + 1) v} _ _ _ _
    (additiveSheafification.{u, v} f) inferInstance

/-- The standard localization of the actual constant-ring module category.
Source: Stacks 0152 (blueprint: lem-trf-oriented-source-localization). -/
instance hasDerived {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type v) [CommRing Λ] :
    HasDerivedCategory.{max (u + 1) v + 1} (Modules f Λ) :=
  HasDerivedCategory.standard.{max (u + 1) v, max (u + 1) v + 1} (Modules f Λ)

/-- Canonical source restriction, using the dependency's actual site inverse image.
The equality transport only removes the composite of the two identity base maps.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-source-localization). -/
def sourcePull {T X S : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ X)
    (Λ : Type v) [CommRing Λ] : Modules f Λ ⥤ Modules (h ≫ f) Λ :=
  OrientedConstructibleSheaf.stratumRestriction f (𝟙 S) h (𝟙 S) Λ ⋙
    (Pi.eqToEquivalence
      (fun b : S ⟶ S ↦ OrientedConstructibleSheaf.Modules (h ≫ f) b Λ)
      (Category.id_comp (𝟙 S))).functor

/-- The canonical geometric source map, obtained from the recorded commutative square.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-source-localization). -/
def sourceMap {T X S : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ X) :=
  squareMorphism.{u, v} f (h ≫ f) h (𝟙 S) (Category.comp_id (h ≫ f)).symm

/-- The four source module operations and their exactness witnesses. The inverse images
are fixed by equality to `sourcePull`; the extensions are specified as their adjoints.
These fields are data of the conclusion, not hypotheses of the localization theorem.
Source: Orgogozo §9.3; Stacks 03DI, 08M3
(blueprint: lem-trf-oriented-source-localization). -/
structure Operations {U Z X S : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X) (i : Z ⟶ X)
    (Λ : Type v) [CommRing Λ] where
  openPull : Modules f Λ ⥤ Modules (j ≫ f) Λ
  closedPull : Modules f Λ ⥤ Modules (i ≫ f) Λ
  openExtension : Modules (j ≫ f) Λ ⥤ Modules f Λ
  closedImage : Modules (i ≫ f) Λ ⥤ Modules f Λ
  openPull_eq : openPull = sourcePull f j Λ
  closedPull_eq : closedPull = sourcePull f i Λ
  openAdjunction : openExtension ⊣ openPull
  closedAdjunction : closedPull ⊣ closedImage
  openPull_additive : openPull.Additive
  closedPull_additive : closedPull.Additive
  openExtension_additive : openExtension.Additive
  closedImage_additive : closedImage.Additive
  openPull_limits : PreservesFiniteLimits openPull
  openPull_colimits : PreservesFiniteColimits openPull
  closedPull_limits : PreservesFiniteLimits closedPull
  closedPull_colimits : PreservesFiniteColimits closedPull
  openExtension_limits : PreservesFiniteLimits openExtension
  openExtension_colimits : PreservesFiniteColimits openExtension
  closedImage_limits : PreservesFiniteLimits closedImage
  closedImage_colimits : PreservesFiniteColimits closedImage

attribute [instance] Operations.openPull_additive Operations.closedPull_additive
  Operations.openExtension_additive Operations.closedImage_additive
  Operations.openPull_limits Operations.openPull_colimits
  Operations.closedPull_limits Operations.closedPull_colimits
  Operations.openExtension_limits Operations.openExtension_colimits
  Operations.closedImage_limits Operations.closedImage_colimits

/-- The degreewise open counit, with the identity-complex identification made explicit.
Source: Stacks 0152 (blueprint: lem-trf-oriented-source-localization). -/
def counitComplex {U Z X S : Scheme.{u}} {f : X ⟶ S} {j : U ⟶ X} {i : Z ⟶ X}
    {Λ : Type v} [CommRing Λ] (r : Operations f j i Λ) :=
  NatTrans.mapHomologicalComplex r.openAdjunction.counit (ComplexShape.up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso (Modules f Λ) (ComplexShape.up ℤ)).hom

/-- The degreewise closed unit, using the same adjunction as the sheaf sequence.
Source: Stacks 0152 (blueprint: lem-trf-oriented-source-localization). -/
def unitComplex {U Z X S : Scheme.{u}} {f : X ⟶ S} {j : U ⟶ X} {i : Z ⟶ X}
    {Λ : Type v} [CommRing Λ] (r : Operations f j i Λ) :=
  (Functor.mapHomologicalComplexIdIso (Modules f Λ) (ComplexShape.up ℤ)).inv ≫
    NatTrans.mapHomologicalComplex r.closedAdjunction.unit (ComplexShape.up ℤ)

/-- The actual degreewise localization sequence, with its proof of zero composite.
Source: Stacks 0152 (blueprint: lem-trf-oriented-source-localization). -/
def complexSequence {U Z X S : Scheme.{u}} {f : X ⟶ S} {j : U ⟶ X} {i : Z ⟶ X}
    {Λ : Type v} [CommRing Λ] (r : Operations f j i Λ)
    (h : ∀ K : CochainComplex (Modules f Λ) ℤ,
      (counitComplex r).app K ≫ (unitComplex r).app K = 0)
    (K : CochainComplex (Modules f Λ) ℤ) :
    ShortComplex (CochainComplex (Modules f Λ) ℤ) :=
  ShortComplex.mk ((counitComplex r).app K) ((unitComplex r).app K) (h K)

/-- Open/closed source recollement, all four constructibility assertions, the natural
short exact sheaf sequence, and its natural unbounded derived localization triangle.
Source: Orgogozo §§8, 9.3; ILO XI §§1.4, 1.10(b); Stacks 08LW, 08LY, 0152
(blueprint: lem-trf-oriented-source-localization).
Proof: pull the open represented subterminal back by the first projection. The oriented
slice-localization lemma identifies its slice with `V_(fj)`. The closed étale complement
and the oriented universal property identify its complementary closed topos with `V_(fi)`:
a triple factors through it exactly when its first projection factors through `Z`.
The topos-complement module-stalk lemma gives the two adjunctions. At each oriented point
the extension stalks are the original stalk on the corresponding part and zero on the
other part. Exact stalks and conservative oriented points prove exactness of all four
functors. The counit/unit sequence has stalks either `F --id--> F --> 0` or
`0 --> F --id--> F`, hence is short exact, naturally in `F`. Extension commutes with
restriction to inverse-image complementary parts, by the support characterization and
the restriction identities. Since finite presentation over a Noetherian base makes `X`
Noetherian, intersect constructible strata with `U` and `Z` for inverse images; for either
extension append the complementary stratum with zero value. These finite refinements
prove all four constructibility assertions, including empty strata and zero modules.
Finally apply the sheaf sequence degreewise. Exact-functor derived factorization and
the canonical short-exact-complex triangle (0152) give the natural distinguished triangle
on unbounded derived categories. Its first two maps descend the very same counit/unit;
the connecting map is the canonical short-exact-complex boundary. -/
theorem sourceLocalization {U Z X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [CompactSpace S]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (complement : Set.range i.base = (Set.range j.base)ᶜ)
    (Λ : Type v) [CommRing Λ] [Finite Λ] :
    (∃ (V : VanishingTopos.{u, v} f), IsSubterminal V ∧
      ∃ e : VanishingTopos.{u, v} (j ≫ f) ≌ Over V,
        Nonempty ((sourceMap.{u, v} f j).inverse ⋙ e.functor ≅ Over.star V) ∧
        (sourceMap.{u, v} f i).direct.Full ∧
        (sourceMap.{u, v} f i).direct.Faithful ∧
        ∀ A : VanishingTopos.{u, v} f,
          (sourceMap.{u, v} f i).direct.essImage A ↔
            IsIso (prod.fst : V ⨯ A ⟶ V)) ∧
    ∃ r : Operations f j i Λ,
      (∀ F : Modules f Λ, OrientedConstructibleSheaf.IsConstructible f (𝟙 S) Λ F →
        OrientedConstructibleSheaf.IsConstructible (j ≫ f) (𝟙 S) Λ
          (r.openPull.obj F)) ∧
      (∀ F : Modules f Λ, OrientedConstructibleSheaf.IsConstructible f (𝟙 S) Λ F →
        OrientedConstructibleSheaf.IsConstructible (i ≫ f) (𝟙 S) Λ
          (r.closedPull.obj F)) ∧
      (∀ G : Modules (j ≫ f) Λ,
        OrientedConstructibleSheaf.IsConstructible (j ≫ f) (𝟙 S) Λ G →
        OrientedConstructibleSheaf.IsConstructible f (𝟙 S) Λ (r.openExtension.obj G)) ∧
      (∀ H : Modules (i ≫ f) Λ,
        OrientedConstructibleSheaf.IsConstructible (i ≫ f) (𝟙 S) Λ H →
        OrientedConstructibleSheaf.IsConstructible f (𝟙 S) Λ (r.closedImage.obj H)) ∧
      (∀ F : Modules f Λ,
        ∃ h : r.openAdjunction.counit.app F ≫ r.closedAdjunction.unit.app F = 0,
          (ShortComplex.mk (r.openAdjunction.counit.app F)
            (r.closedAdjunction.unit.app F) h).ShortExact) ∧
      ∃ (h : ∀ K : CochainComplex (Modules f Λ) ℤ,
          (counitComplex r).app K ≫ (unitComplex r).app K = 0)
        (hSES : ∀ K : CochainComplex (Modules f Λ) ℤ,
          (complexSequence r h K).ShortExact),
      ∃ (ε : (r.openPull ⋙ r.openExtension).mapDerivedCategory ⟶
          𝟭 (DerivedCategory (Modules f Λ)))
        (η : 𝟭 (DerivedCategory (Modules f Λ)) ⟶
          (r.closedPull ⋙ r.closedImage).mapDerivedCategory)
        (δ : (r.closedPull ⋙ r.closedImage).mapDerivedCategory ⟶
          (r.openPull ⋙ r.openExtension).mapDerivedCategory ⋙
            shiftFunctor (DerivedCategory (Modules f Λ)) (1 : ℤ)),
        (∀ K : CochainComplex (Modules f Λ) ℤ,
          ε.app (DerivedCategory.Q.obj K) =
            (r.openPull ⋙ r.openExtension).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.Q.map ((counitComplex r).app K)) ∧
        (∀ K : CochainComplex (Modules f Λ) ℤ,
          η.app (DerivedCategory.Q.obj K) =
            DerivedCategory.Q.map ((unitComplex r).app K) ≫
              (r.closedPull ⋙ r.closedImage).mapDerivedCategoryFactors.inv.app K) ∧
        (∀ K : CochainComplex (Modules f Λ) ℤ,
          δ.app (DerivedCategory.Q.obj K) =
            (r.closedPull ⋙ r.closedImage).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.triangleOfSESδ (hSES K) ≫
              (shiftFunctor (DerivedCategory (Modules f Λ)) (1 : ℤ)).map
                ((r.openPull ⋙ r.openExtension).mapDerivedCategoryFactors.inv.app K)) ∧
        (∀ K : DerivedCategory (Modules f Λ),
          Triangle.mk (ε.app K) (η.app K) (δ.app K) ∈
            distTriang (DerivedCategory (Modules f Λ))) := by
  sorry

end AlgebraicGeometry.OrientedSourceLocalization
