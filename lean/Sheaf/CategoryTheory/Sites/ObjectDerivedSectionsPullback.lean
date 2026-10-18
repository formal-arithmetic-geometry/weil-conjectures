/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Sheaf.CategoryTheory.Sites.PullbackInjectiveEvaluationAcyclic

/-! # Derived sections under a continuous cocontinuous site functor

Source: Stacks Project, Cohomology on Sites, Tag 0DD8, part (1), bounded-below case;
Sites, Tags 00WV, 00XO and 00XR
(blueprint: lem-trf-site-object-derived-sections-pullback).

The inverse image below is Mathlib's precomposition on sheaves. Its name in Mathlib
uses the continuous-functor variance; for a cocontinuous functor it is the inverse
image of the induced geometric morphism. The canonical derived pullback is formed
from the literal identity on sections, using the ordinary right-derived comparison.
The theorem asserts invertibility of this natural transformation. Its inverse is
the comparison in the direction written in the node.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SiteObjectDerivedSections

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : Precoverage C) (K : Precoverage D)
  (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
  (f : C ⥤ D)
  (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
  (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
    ∀ (a : Y ⟶ X) (b : Z ⟶ X), S a → PreservesLimit (cospan a b) f)

include hJ hK hcover hpullback

/-- The Stacks continuity conditions give Mathlib continuity for the generated topologies.
This is the sheaf-condition proof needed to define the actual precomposition inverse image.
Source: Stacks, Sites, Tags 00WV and 00WW
(blueprint: lem-trf-site-object-derived-sections-pullback).
Proof: a target sheaf satisfies the equalizer condition on the image of every source
cover, by `hcover`. Preservation of covering pullbacks identifies that equalizer with
the source covering equalizer for precomposition. The site axioms identify these
covering sheaves with sheaves for the generated Grothendieck topology. This uses only
covering pullbacks and bind composition, so applies also to finite covering sites. -/
theorem continuous : f.IsContinuous J.toGrothendieck K.toGrothendieck := by
  sorry

/-- The abelian inverse image is the actual precomposition, on objects and morphisms.
Source: Stacks, Sites, Tag 00XR and algebraic structures, Tag 00YV
(blueprint: lem-trf-site-object-derived-sections-pullback). -/
def inverseImage : Sheaf K.toGrothendieck AddCommGrpCat.{u} ⥤
    Sheaf J.toGrothendieck AddCommGrpCat.{u} :=
  letI := continuous J K hJ hK f hcover hpullback
  f.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck

/-- The precomposition inverse image is additive and exact, so has a termwise derived lift.
Source: Stacks, Sites, Tags 00XR and 00YV
(blueprint: lem-trf-site-object-derived-sections-pullback).
Proof: addition on sheaf morphisms is sectionwise, and precomposition preserves it.
Limits of sheaves are sectionwise, so precomposition preserves finite limits. The
continuous-cocontinuous adjunction makes this functor left adjoint to the cocontinuous
pushforward (Mathlib `sheafAdjunctionCocontinuous`), hence it preserves finite colimits.
This is also the abelian specialization of the constant-left-module inverse-image theorem. -/
theorem inverseImage_exact [f.IsCocontinuous J.toGrothendieck K.toGrothendieck] :
    (inverseImage J K hJ hK f hcover hpullback).Additive ∧
      PreservesFiniteLimits (inverseImage J K hJ hK f hcover hpullback) ∧
      PreservesFiniteColimits (inverseImage J K hJ hK f hcover hpullback) := by
  sorry

/-- Additivity from the named exactness theorem.
Source: Stacks, 00YV (blueprint: lem-trf-site-object-derived-sections-pullback). -/
instance inverseImageAdditive [f.IsCocontinuous J.toGrothendieck K.toGrothendieck] :
    (inverseImage J K hJ hK f hcover hpullback).Additive :=
  (inverseImage_exact J K hJ hK f hcover hpullback).1

/-- Left exactness from the named exactness theorem.
Source: Stacks, 00YV (blueprint: lem-trf-site-object-derived-sections-pullback). -/
instance inverseImagePreservesFiniteLimits
    [f.IsCocontinuous J.toGrothendieck K.toGrothendieck] :
    PreservesFiniteLimits (inverseImage J K hJ hK f hcover hpullback) :=
  (inverseImage_exact J K hJ hK f hcover hpullback).2.1

/-- Right exactness from the named exactness theorem.
Source: Stacks, 00YV (blueprint: lem-trf-site-object-derived-sections-pullback). -/
instance inverseImagePreservesFiniteColimits
    [f.IsCocontinuous J.toGrothendieck K.toGrothendieck] :
    PreservesFiniteColimits (inverseImage J K hJ hK f hcover hpullback) :=
  (inverseImage_exact J K hJ hK f hcover hpullback).2.2

/-- The identity on sections over corresponding site objects, including all restriction
and coefficient maps, before deriving. Source: Stacks, 00XR and 0DD8
(blueprint: lem-trf-site-object-derived-sections-pullback). -/
def sectionsIdentity (U : C) :
    (sheafSections K.toGrothendieck AddCommGrpCat.{u}).obj (op (f.obj U)) ⋙
        𝟭 AddCommGrpCat.{u} ≅
      inverseImage J K hJ hK f hcover hpullback ⋙
        (sheafSections J.toGrothendieck AddCommGrpCat.{u}).obj (op U) :=
  Iso.refl _

/-- Mathlib's section functor is the additive composite of presheaf forgetting and evaluation.
Source: Stacks, 01FT (blueprint: lem-trf-site-object-derived-sections-pullback). -/
instance sectionsAdditive {E : Type u} [SmallCategory E]
    (T : GrothendieckTopology E) (V : E) :
    ((sheafSections T AddCommGrpCat.{u}).obj (op V)).Additive :=
  inferInstanceAs ((sheafToPresheaf T AddCommGrpCat.{u} ⋙
    (evaluation Eᵒᵖ AddCommGrpCat.{u}).obj (op V)).Additive)

variable [f.IsCocontinuous J.toGrothendieck K.toGrothendieck]
  [HasDerivedCategory.{w} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
  [HasDerivedCategory.{w} AddCommGrpCat.{u}]

/-- The ordinary derived pullback of sections. On an injective representative `I`, this
is the identity on evaluated complexes followed by the right-derived unit for `f⁻¹I`.
Source: Stacks, 0DD8, and Derived Categories, 015E/05TI
(blueprint: lem-trf-site-object-derived-sections-pullback). -/
def pullback (U : C) :
    ((sheafSections K.toGrothendieck AddCommGrpCat.{u}).obj
      (op (f.obj U))).rightDerivedFunctorPlus ⟶
      (inverseImage J K hJ hK f hcover hpullback).mapDerivedCategoryPlus ⋙
        ((sheafSections J.toGrothendieck AddCommGrpCat.{u}).obj
          (op U)).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u})).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (sectionsIdentity J K hJ hK f hcover hpullback U).hom

end

/-- For every site object, the canonical bounded-below comparison is a natural isomorphism
`RΓ(U,g⁻¹M) ≅ RΓ(f(U),M)`, with inverse the ordinary derived pullback of sections.

Source: Stacks Project, Cohomology on Sites, Tag 0DD8, part (1), bounded-below proof
(blueprint: lem-trf-site-object-derived-sections-pullback).

Proof:
1. The continuous-cocontinuous adjunction identifies inverse image with precomposition.
   This is compatible with addition, zero, negation, sheaf maps and restrictions, so
   `sectionsIdentity` is the canonical additive identity on evaluation. Exactness of
   inverse image follows from the constant-left-module inverse-image theorem at ℤ,
   since every abelian sheaf has its unique integer action.
2. The small-site sheaf theorem gives enough injectives. Represent a bounded-below
   derived object by an injective complex `I`, zero below an integer bound, using
   `DerivedCategory.Plus.exists_injective_nonempty_iso`. Exact inverse image gives
   the representative `f⁻¹I`. The right-derived injective-computation theorem computes
   `RΓ(f(U),M)` on the evaluated complex of `I`.
3. The pulled-back-injective evaluation-acyclicity theorem, Tag 0D6X, makes every term
   of `f⁻¹I` acyclic for evaluation at `U`. Leray's acyclic-complex unit theorem
   (`isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`) therefore computes
   `RΓ(U,f⁻¹M)` on this same evaluated complex. The termwise identities commute with
   differentials by naturality, and give an isomorphism of evaluated complexes.
4. The defining factorization of `rightDerivedFunctorPlusBaseChange` identifies
   `pullback` with this termwise identity followed by the acyclic-complex unit. Thus
   this particular canonical map is invertible. Replacing `f⁻¹I` by an injective
   representative gives the usual derived pullback, by naturality and injective
   normalization of the unit. Derived-functor uniqueness gives independence of all
   representatives. Finally, `pullback` is a natural transformation, so its inverse
   is natural in every bounded-below `M`, as required in the stated direction. -/
theorem comparison_exists
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (f : C ⥤ D)
    (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
    (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), S a → PreservesLimit (cospan a b) f)
    [f.IsCocontinuous J.toGrothendieck K.toGrothendieck]
    [HasDerivedCategory.{w} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] (U : C) :
    ∃ e : (inverseImage J K hJ hK f hcover hpullback).mapDerivedCategoryPlus ⋙
        ((sheafSections J.toGrothendieck AddCommGrpCat.{u}).obj
          (op U)).rightDerivedFunctorPlus ≅
      ((sheafSections K.toGrothendieck AddCommGrpCat.{u}).obj
        (op (f.obj U))).rightDerivedFunctorPlus,
      e.inv = pullback J K hJ hK f hcover hpullback U := by
  sorry

end CategoryTheory.SiteObjectDerivedSections
