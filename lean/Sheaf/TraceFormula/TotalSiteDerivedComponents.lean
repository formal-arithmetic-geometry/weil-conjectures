/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.TraceFormula.TotalSiteComponentRestriction
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.Pullback
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Derived images and units on components of total simplicial sites

Source: Stacks Project, `spaces-simplicial.tex`, Tags 09WF, 09WG, 09WH, 0D96 and 0D97
(blueprint: lem-trf-total-site-derived-components).

The component categories and both total categories below are actual abelian sheaf
categories on small sites. Their compatible-system presentations are the existing
`TotalSiteSystemData`. The commutation isomorphisms have explicit unit and cocycle laws.
`pSite`, `qSite` and `hSite` retain the site-induced origin of the structural and
component inverse/direct images; the pullback on sets is left exact, as required
for a morphism of sites. The induced total adjunction is characterized by its
inverse-image transitions and its
component units. Its derived direct-image comparison is the existing canonical base-change
map, and its inverse-image comparison is obtained by localizing the component isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Coherent component geometric morphisms on abelian sheaves. The additive and colimit
fields record the structures of the induced abelian inverse and direct images; inverse
images are left exact by `GeometricMorphism.leftExact` and preserve colimits by adjunction.
The last two fields are precisely the unit and composition laws for the commutation
isomorphisms. Source: Stacks Project, Tag 0D96, case A, with coherent identifications of
iterated pullbacks (blueprint: lem-trf-total-site-derived-components). -/
structure TotalSiteMorphismData
    (A B : SimplexCategoryᵒᵖ → Type v)
    [∀ i, Category.{w} (A i)] [∀ i, Category.{w} (B i)]
    [∀ i, Preadditive (A i)] [∀ i, Preadditive (B i)]
    (p : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) → A i ⥤ A j)
    (q : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) → B i ⥤ B j)
    (pId : ∀ i, p (𝟙 i) ≅ 𝟭 (A i)) (qId : ∀ i, q (𝟙 i) ≅ 𝟭 (B i))
    (pComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      p (g ≫ f) ≅ p f ⋙ p g)
    (qComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      q (g ≫ f) ≅ q f ⋙ q g) where
  component : ∀ i, GeometricMorphism (A i) (B i)
  inverse_additive : ∀ i, (component i).inverse.Additive
  direct_additive : ∀ i, (component i).direct.Additive
  inverse_colimits : ∀ i, PreservesFiniteColimits (component i).inverse
  commute : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
    (component i).inverse ⋙ p f ≅ q f ⋙ (component j).inverse
  commute_id : ∀ (i : SimplexCategoryᵒᵖ) (X : B i),
    (commute (𝟙 i)).hom.app X ≫ (component i).inverse.map ((qId i).hom.app X) =
      (pId i).hom.app ((component i).inverse.obj X)
  commute_comp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j) (X : B i),
    (pComp f g).hom.app ((component i).inverse.obj X) ≫
        (p g).map ((commute f).hom.app X) ≫ (commute g).hom.app ((q f).obj X) =
      (commute (g ≫ f)).hom.app X ≫ (component k).inverse.map ((qComp f g).hom.app X)

attribute [instance] TotalSiteMorphismData.inverse_additive
  TotalSiteMorphismData.direct_additive TotalSiteMorphismData.inverse_colimits

/-- The induced total adjunction, exact conservative restrictions, canonical derived
component comparisons, and compatibility of the derived units.
Source: Stacks Project, Tags 09WF, 09WG, 09WH, 0D96 and 0D97
(blueprint: lem-trf-total-site-derived-components).

Proof (postponed):
1. Use `lem-trf-total-site-component-restriction` and the fully faithful essentially
surjective presentations `S` and `T`. Evaluation is exact and jointly conservative.
2. Apply the component inverse images to a compatible family, using `M.commute` and
its two coherence laws for the transitions. The component direct images have the mate
transitions, obtained by applying the inverse commutation isomorphism, the component
counit, and the original transition. Taking component adjoints identifies all compatible
maps in both directions. Triangle identities give the total adjunction and its component
unit equation. Exactness is detected by the exact conservative restrictions.
3. Abelian sheaves on each small site have enough injectives, by
`lem-weil-pbc-site-sheaves-enough-injectives`; they are Grothendieck (also the constant
integer-ring case of `lem-weil-pbc-ring-sheaves-grothendieck`). Choose a bounded-below
injective representative using `lem-weil-pbc-dplus-injective-representative`. Restriction
preserves injectives by step 1, so the canonical base-change map of the underived direct
comparison is an isomorphism on this representative and hence everywhere. Independence
and naturality follow from `lem-sp-kinjective-computes`.
4. The total inverse image is exact by its component description. Apply it termwise and
localize. The inverse comparison is exactly `mapDerivedCategoryPlusNatIso` composed with
the two functor-composition comparisons.
5. Represent the derived unit by the ordinary unit followed by a bounded-below injective
resolution of the inverse image. Restrict this chain map. Step 2 identifies its first
arrow with the component unit; step 1 makes the restricted resolution injective. Steps
3 and 4 identify its target by precisely the canonical comparisons in the statement.
This gives the displayed equality of actual derived units, independent of choices by
`lem-sp-kinjective-computes`. -/
theorem totalSiteDerivedComponents
    (C D : SimplexCategoryᵒᵖ → Type u)
    [∀ i, SmallCategory (C i)] [∀ i, SmallCategory (D i)]
    (J : ∀ i, GrothendieckTopology (C i)) (K : ∀ i, GrothendieckTopology (D i))
    (p : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) →
      Sheaf (J i) AddCommGrpCat.{u} ⥤ Sheaf (J j) AddCommGrpCat.{u})
    (q : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) →
      Sheaf (K i) AddCommGrpCat.{u} ⥤ Sheaf (K j) AddCommGrpCat.{u})
    (pId : ∀ i, p (𝟙 i) ≅ 𝟭 (Sheaf (J i) AddCommGrpCat.{u}))
    (qId : ∀ i, q (𝟙 i) ≅ 𝟭 (Sheaf (K i) AddCommGrpCat.{u}))
    (pComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      p (g ≫ f) ≅ p f ⋙ p g)
    (qComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      q (g ≫ f) ≅ q f ⋙ q g)
    (CT DT : Type u) [SmallCategory CT] [SmallCategory DT]
    (JT : GrothendieckTopology CT) (KT : GrothendieckTopology DT)
    (S : TotalSiteSystemData (fun i ↦ Sheaf (J i) AddCommGrpCat.{u}) p pId pComp
      (Sheaf JT AddCommGrpCat.{u}))
    (T : TotalSiteSystemData (fun i ↦ Sheaf (K i) AddCommGrpCat.{u}) q qId qComp
      (Sheaf KT AddCommGrpCat.{u}))
    (M : TotalSiteMorphismData (fun i ↦ Sheaf (J i) AddCommGrpCat.{u})
      (fun i ↦ Sheaf (K i) AddCommGrpCat.{u}) p q pId qId pComp qComp)
    (pSite : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
      ∃ (s : C i ⥤ C j) (_ : s.IsContinuous (J i) (J j)),
        PreservesFiniteLimits (s.sheafPullback (Type u) (J i) (J j)) ∧
          Nonempty (p f ≅ s.sheafPullback AddCommGrpCat.{u} (J i) (J j)))
    (qSite : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
      ∃ (s : D i ⥤ D j) (_ : s.IsContinuous (K i) (K j)),
        PreservesFiniteLimits (s.sheafPullback (Type u) (K i) (K j)) ∧
          Nonempty (q f ≅ s.sheafPullback AddCommGrpCat.{u} (K i) (K j)))
    (hSite : ∀ i : SimplexCategoryᵒᵖ,
      ∃ (s : D i ⥤ C i) (_ : s.IsContinuous (K i) (J i)),
        PreservesFiniteLimits (s.sheafPullback (Type u) (K i) (J i)) ∧
          Nonempty ((M.component i).direct ≅
            s.sheafPushforwardContinuous AddCommGrpCat.{u} (K i) (J i))) :
    (∀ {X Y : Sheaf JT AddCommGrpCat.{u}} (f : X ⟶ Y),
      (∀ i, IsIso ((S.component i).map f)) → IsIso f) ∧
    (∀ {X Y : Sheaf KT AddCommGrpCat.{u}} (f : X ⟶ Y),
      (∀ i, IsIso ((T.component i).map f)) → IsIso f) ∧
    ∃ (H : GeometricMorphism (Sheaf JT AddCommGrpCat.{u}) (Sheaf KT AddCommGrpCat.{u}))
      (_ : H.inverse.Additive) (_ : H.direct.Additive)
      (_ : PreservesFiniteLimits H.inverse) (_ : PreservesFiniteColimits H.inverse),
    ∃ (_ : ∀ i, PreservesFiniteLimits (S.component i))
      (_ : ∀ i, PreservesFiniteColimits (S.component i))
      (_ : ∀ i, PreservesFiniteLimits (T.component i))
      (_ : ∀ i, PreservesFiniteColimits (T.component i))
      (_ : ∀ i, PreservesFiniteLimits (M.component i).inverse)
      (a : ∀ i, H.inverse ⋙ S.component i ≅ T.component i ⋙ (M.component i).inverse)
      (b : ∀ i, H.direct ⋙ T.component i ≅ S.component i ⋙ (M.component i).direct),
      (∀ (X : Sheaf KT AddCommGrpCat.{u}) (i j : SimplexCategoryᵒᵖ) (f : j ⟶ i),
        (p f).map ((a i).hom.app X) ≫ (M.commute f).hom.app ((T.component i).obj X) ≫
          (M.component j).inverse.map (T.transition X i j f) =
            S.transition (H.inverse.obj X) i j f ≫ (a j).hom.app X) ∧
      (∀ (i : SimplexCategoryᵒᵖ) (X : Sheaf KT AddCommGrpCat.{u}),
        (T.component i).map (H.adj.unit.app X) ≫ (b i).hom.app (H.inverse.obj X) ≫
          (M.component i).direct.map ((a i).hom.app X) =
            (M.component i).adj.unit.app ((T.component i).obj X)) ∧
      (∀ i, IsIso (Functor.rightDerivedFunctorPlusBaseChange (b i).hom)) ∧
      (∀ (i : SimplexCategoryᵒᵖ) (X : DerivedCategory.Plus (Sheaf KT AddCommGrpCat.{u})),
        (T.component i).mapDerivedCategoryPlus.map (H.adj.derivedPlus.unit.app X) ≫
          (Functor.rightDerivedFunctorPlusBaseChange (b i).hom).app
            (H.inverse.mapDerivedCategoryPlus.obj X) ≫
          (M.component i).direct.rightDerivedFunctorPlus.map
            (((Functor.mapDerivedCategoryPlusCompIso H.inverse (S.component i)).symm ≪≫
              Functor.mapDerivedCategoryPlusNatIso (a i) ≪≫
              Functor.mapDerivedCategoryPlusCompIso (T.component i)
                (M.component i).inverse).hom.app X) =
            (M.component i).adj.derivedPlus.unit.app
              ((T.component i).mapDerivedCategoryPlus.obj X)) := by
  sorry

end CategoryTheory
