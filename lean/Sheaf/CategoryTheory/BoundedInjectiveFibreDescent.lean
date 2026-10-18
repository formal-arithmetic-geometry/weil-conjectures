/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Descent of bounded injective fibre comparisons

Source: Stacks Project, Derived Categories, Tag 05TK,
`lemma-resolution-functor-quasi-inverse`, and the adjacent resolution-functor discussion.
The comparison, shift and pasting calculations are the eight steps of
(blueprint: lem-amb-bounded-injective-fibre-descent).

`boundedInjectiveDerived` uses the existing exact equivalence `K⁺(Inj A) ≌ D⁺(A)`.
`BoundedInjectiveComparison` specifies the component using every pair of resolutions.
Equality in `HomotopyCategory.Plus` means equality of homotopy classes of chain maps.
In particular its comparison arrow can be represented by a chain map, and its augmentation
square says precisely that the two chain maps are homotopic.

## Main definitions

- `CategoryTheory.boundedInjectiveDerived`: the concrete functor computed on injectives.
- `CategoryTheory.boundedInjectiveResolutionIso`: its canonical resolution computation.
- `CategoryTheory.BoundedInjectiveComparison`: the formula for every pair of resolutions.

## Main statements

- `CategoryTheory.boundedInjectiveFibreDescent`: existence and uniqueness of the comparison.
- `CategoryTheory.boundedInjectiveComparison_id`: compatibility with identity data.
- `CategoryTheory.boundedInjectiveComparison_comp`: compatibility with composition data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA wA uA' vA' wA' uA'' vA'' wA'' uB vB wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [EnoughInjectives A']
  [HasDerivedCategory.{wA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- Apply a homotopy functor after the existing injective replacement equivalence and then
localize its output. This is the concrete functor `RF` in Stacks, Tag 05TK and Step 2 of
(blueprint: lem-amb-bounded-injective-fibre-descent). No representative is chosen from a
mere existence assertion: the quasi-inverse belongs to an equivalence. -/
def boundedInjectiveDerived (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B) :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus B :=
  (DerivedCategory.Plus.injectiveObjectEquivalence A).inverse ⋙
    (InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ F ⋙ DerivedCategory.Plus.Qh

/-- The shift comparisons on `RF` are those of the exact injective equivalence and `F`.
Source: Stacks, `lemma-j-is-exact`, Step 2 of
(blueprint: lem-amb-bounded-injective-fibre-descent). -/
instance boundedInjectiveDerived_commShift
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B) [F.CommShift ℤ] :
    (boundedInjectiveDerived F).CommShift ℤ :=
  inferInstanceAs (((DerivedCategory.Plus.injectiveObjectEquivalence A).inverse ⋙
    (InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ F ⋙ DerivedCategory.Plus.Qh).CommShift ℤ)

/-- The canonical computation on a bounded below injective resolution. The first factor
applies `RF` to the augmentation and the second is the inverse unit of the injective
replacement equivalence, after applying the inclusion, `F` and localization.
Source: Stacks, Tag 05TK and `remark-big-localization`, Steps 2 and 6 of
(blueprint: lem-amb-bounded-injective-fibre-descent). -/
def boundedInjectiveResolutionIso
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (K : HomotopyCategory.Plus A) (I : HomotopyCategory.Plus (InjectiveObject A))
    (k : K ⟶ (InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I)
    [IsIso (DerivedCategory.Plus.Qh.map k)] :
    (boundedInjectiveDerived F).obj (DerivedCategory.Plus.Qh.obj K) ≅
      DerivedCategory.Plus.Qh.obj
        (F.obj ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I)) :=
  (boundedInjectiveDerived F).mapIso (asIso (DerivedCategory.Plus.Qh.map k)) ≪≫
    ((InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ F ⋙ DerivedCategory.Plus.Qh).mapIso
      ((DerivedCategory.Plus.injectiveObjectEquivalence A).unitIso.app I).symm

/-- The resolution formula for a comparison. Both augmentations are quasi-isomorphisms
(equivalently their localizations are isomorphisms). The universally quantified `u` is a
homotopy class with `E(k) ≫ u = k'`. There is no injectivity condition on `E(I)`.
The equation uses the canonical exact-functor localization comparison to identify
`D⁺E(QK)` with `Q(EK)`.
Source: Stacks, Tag 05TK and `remark-big-localization`, Steps 3--6 of
(blueprint: lem-amb-bounded-injective-fibre-descent). -/
def BoundedInjectiveComparison
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (E : A ⥤ A') [E.Additive]
    [hElim : PreservesFiniteLimits E] [hEcolim : PreservesFiniteColimits E]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F')
    (t : boundedInjectiveDerived F ⟶ E.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F') :
    Prop :=
  ∀ (K : HomotopyCategory.Plus A)
    (I : HomotopyCategory.Plus (InjectiveObject A))
    (J : HomotopyCategory.Plus (InjectiveObject A'))
    (k : K ⟶ (InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I)
    [IsIso (DerivedCategory.Plus.Qh.map k)]
    (k' : E.mapHomotopyCategoryPlus.obj K ⟶
      (InjectiveObject.ι A').mapHomotopyCategoryPlus.obj J)
    [IsIso (DerivedCategory.Plus.Qh.map k')]
    (u : E.mapHomotopyCategoryPlus.obj
      ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I) ⟶
      (InjectiveObject.ι A').mapHomotopyCategoryPlus.obj J),
    E.mapHomotopyCategoryPlus.map k ≫ u = k' →
    (boundedInjectiveResolutionIso F K I k).hom ≫
        DerivedCategory.Plus.Qh.map
          (τ.app ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I) ≫ F'.map u) =
      t.app (DerivedCategory.Plus.Qh.obj K) ≫
        (boundedInjectiveDerived F').map (E.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (boundedInjectiveResolutionIso F' (E.mapHomotopyCategoryPlus.obj K) J k').hom

/-- Exactness of the functor computed by injective representatives.
Source: Stacks, Tag 05TK and `lemma-j-is-exact`.
Proof: Step 1 uses the interval `[0,0]` of
`lem-trf-filtered-localization-injective-model` to obtain the injective equivalence.
In Step 2 its quasi-inverse has the conjugate shift comparisons and is exact by
`lem-sf-triangulated-right-adjoint`. The injective inclusion is exact because shifts and
finite cone sums retain injectives. Compose this with exact `F` and exact localization,
using `def-weil-abstract-derived-category` and `def-weil-triangulated-category`.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
theorem boundedInjectiveDerived_isTriangulated
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    [F.CommShift ℤ] [F.IsTriangulated] :
    (boundedInjectiveDerived F).IsTriangulated := by
  sorry

/-- The comparison homotopy class exists uniquely, even when `E(I)` is not injective.
Source: Stacks, Tags 05TG and 05TK, and the K-injective Hom comparison.
Proof: Step 3 uses `lem-sc-bounded-below-injective-resolution-existence` and
`lem-weil-pbc-bounded-below-injectives-kinjective`. Exact `E` preserves quasi-isomorphisms
by `lem-sf-exact-functor-derived-triangulated`. In Step 4 lift
`Q(k') Q(E(k))⁻¹` uniquely using `lem-weil-pbc-kinjective-hom-derived`, or the `[0,0]`
Hom clause of `lem-trf-filtered-localization-injective-model`. Injectivity of the same
Hom map with source `EK` proves the augmentation equation in the homotopy category.
Only the target `J` needs to be K-injective.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
theorem boundedInjectiveComparison_exists_unique_lift
    (E : A ⥤ A') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (K : HomotopyCategory.Plus A) (I : HomotopyCategory.Plus (InjectiveObject A))
    (J : HomotopyCategory.Plus (InjectiveObject A'))
    (k : K ⟶ (InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I)
    [IsIso (DerivedCategory.Plus.Qh.map k)]
    (k' : E.mapHomotopyCategoryPlus.obj K ⟶
      (InjectiveObject.ι A').mapHomotopyCategoryPlus.obj J)
    [IsIso (DerivedCategory.Plus.Qh.map k')] :
    ∃! u : E.mapHomotopyCategoryPlus.obj
        ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I) ⟶
        (InjectiveObject.ι A').mapHomotopyCategoryPlus.obj J,
      E.mapHomotopyCategoryPlus.map k ≫ u = k' := by
  sorry

/-- Descent of a shift-compatible comparison on bounded below homotopy categories.
Source: Stacks, Tag 05TK, the adjacent resolution discussion, and the comparison calculations
in Steps 1--8 of the DAG node.
Proof: (1) Specialize `lem-trf-filtered-localization-injective-model` to `[0,0]`.
(2) Use the adjoint injective equivalence and its conjugate shifts; its inverse is exact by
`lem-sf-triangulated-right-adjoint`. This gives the displayed concrete `RF,RF'`.
(3) Resolve `K,EK` by `lem-sc-bounded-below-injective-resolution-existence`; exact `E`
preserves quasi-isomorphisms by `lem-sf-exact-functor-derived-triangulated`.
(4) Lift `Q(k') Q(E(k))⁻¹` by `lem-weil-pbc-kinjective-hom-derived`; bounded below injectives
are K-injective by `lem-weil-pbc-bounded-below-injectives-kinjective`. Apply `F'(u) τ_I`.
(5) For any derived arrow `α`, lift it to maps `a:I_K→I_L`, `b:J_K→J_L`. Their localized
square gives `b u_K = u_L E(a)` by the same Hom bijection, and naturality of `τ` gives the
naturality square. This includes every `K→L[1]`.
(6) The unique comparisons between two resolutions are homotopy equivalences. The same
square with `α=1` identifies the formula for all `I,J,k,k',u`, and proves uniqueness.
(7) Compute on shifted resolutions with comparison `u[n]`. Naturality of the shift
isomorphism of `F'` and shift compatibility of `τ` give the induced shift square for every
integer `n`; Step 6 transfers it to arbitrary chosen resolutions.
(8) Identity uses `u=1`. For composable comparisons use `w=E'(u)≫v`; naturality of the second
transformation identifies the two formulas. Associativity gives the triple comparison.
The identity and composition equalities are stated below.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
theorem boundedInjectiveFibreDescent
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (E : A ⥤ A') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F') [NatTrans.CommShift τ ℤ] :
    ∃! t : boundedInjectiveDerived F ⟶ E.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F',
      BoundedInjectiveComparison F F' E τ t ∧ NatTrans.CommShift t ℤ := by
  sorry

/-- Identity comparison data, with the canonical termwise identity isomorphism inserted.
Source: Step 8, identity calculation following Stacks, Tag 05TK.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
def boundedInjectiveIdentityDatum
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B) :
    F ⟶ (𝟭 A).mapHomotopyCategoryPlus ⋙ F :=
  (Functor.leftUnitor F).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusIdIso A).inv F

/-- Descent respects identity data, after the canonical identification `D⁺(id) ≅ id`.
Source: Step 8, Stacks, Tag 05TK.
Proof: Use identical resolutions and identity comparison `u=1`. The resolution formula is
then the identity, and Step 6 gives the equality for all choices. Every derived object has
an injective representative, so the equality holds at every object.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
theorem boundedInjectiveComparison_id
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    [F.CommShift ℤ] [F.IsTriangulated]
    (t : boundedInjectiveDerived F ⟶
      (𝟭 A).mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F)
    (ht : BoundedInjectiveComparison F F (𝟭 A) (boundedInjectiveIdentityDatum F) t)
    (X : DerivedCategory.Plus A) :
    t.app X ≫ (boundedInjectiveDerived F).map
        ((Functor.mapDerivedCategoryPlusIdIso A).hom.app X) = 𝟙 _ := by
  sorry

variable {A'' : Type uA''} [Category.{vA''} A''] [Abelian A''] [EnoughInjectives A'']
  [HasDerivedCategory.{wA''} A'']

/-- Composite comparison data, using the canonical termwise composition isomorphism.
Source: Step 8, comparison/pasting calculation extending Stacks, Tag 05TK.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
def boundedInjectiveCompositeDatum
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (F'' : HomotopyCategory.Plus A'' ⥤ HomotopyCategory.Plus B)
    (E : A ⥤ A') (E' : A' ⥤ A'') [E.Additive] [E'.Additive]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F')
    (σ : F' ⟶ E'.mapHomotopyCategoryPlus ⋙ F'') :
    F ⟶ (E ⋙ E').mapHomotopyCategoryPlus ⋙ F'' :=
  τ ≫ Functor.whiskerLeft E.mapHomotopyCategoryPlus σ ≫
    (Functor.associator E.mapHomotopyCategoryPlus E'.mapHomotopyCategoryPlus F'').inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (E ⋙ E'))).hom F''

/-- Descent respects composition, with the canonical isomorphism
`D⁺(E⋙E') ≅ D⁺E⋙D⁺E'` inserted. Together with the identity law this includes all iterated
compositions, since natural-transformation composition and the canonical comparison
isomorphisms are associative.
Source: Step 8, comparison/pasting calculation following Stacks, Tag 05TK.
Proof: Resolve `K,EK,E'EK` by `I,J,H` and choose `u:EI→J`, `v:E'J→H`.
Then `w=E'(u)≫v` satisfies the composite augmentation equation. Naturality of `σ` at `u`
identifies `τ_I≫F'(u)≫σ_J≫F''(v)` with
`τ_I≫σ_EI≫F''(E'(u)≫v)`. Apply localization and the resolution formula; Step 6 makes
this independent of all choices. Naturality of the localization comparison inserts
`mapDerivedCategoryPlusCompIso`. No injectivity of `EI` or `E'J` is used.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
theorem boundedInjectiveComparison_comp
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (F'' : HomotopyCategory.Plus A'' ⥤ HomotopyCategory.Plus B)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    [F''.CommShift ℤ] [F''.IsTriangulated]
    (E : A ⥤ A') (E' : A' ⥤ A'') [E.Additive] [E'.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F') [NatTrans.CommShift τ ℤ]
    (σ : F' ⟶ E'.mapHomotopyCategoryPlus ⋙ F'') [NatTrans.CommShift σ ℤ]
    (t : boundedInjectiveDerived F ⟶ E.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F')
    (s : boundedInjectiveDerived F' ⟶ E'.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F'')
    (r : boundedInjectiveDerived F ⟶
      (@Functor.mapDerivedCategoryPlus A A'' _ _ _ _ _ _ (E ⋙ E') _
        (comp_preservesFiniteLimits E E') (comp_preservesFiniteColimits E E')) ⋙
          boundedInjectiveDerived F'')
    (ht : BoundedInjectiveComparison F F' E τ t)
    (hs : BoundedInjectiveComparison F' F'' E' σ s)
    (hr : BoundedInjectiveComparison F F'' (E ⋙ E')
      (hElim := comp_preservesFiniteLimits E E')
      (hEcolim := comp_preservesFiniteColimits E E')
      (boundedInjectiveCompositeDatum F F' F'' E E' τ σ) r)
    (X : DerivedCategory.Plus A) :
    r.app X ≫ (boundedInjectiveDerived F'').map
        ((Functor.mapDerivedCategoryPlusCompIso E E').hom.app X) =
      t.app X ≫ s.app (E.mapDerivedCategoryPlus.obj X) := by
  sorry

end CategoryTheory
