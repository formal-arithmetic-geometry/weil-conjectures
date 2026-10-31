/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Equivalence

/-! # Bounded-below equivalence from acyclic heart tests

Source: Stacks Project, sites-cohomology.tex, Tags 0D7S, 0D7T and 0D7U,
`lemma-bounded-in-image-upstairs`, `lemma-bounded-in-image-downstairs` and
`lemma-equivalence-bounded` (blueprint: lem-fd-bounded-below-acyclic-heart-adjunction).

The conclusions specify preservation of the two full subcategories and invertibility
of the canonical unit and counit. These are the data making the restrictions inverse
equivalences; no triangulated structure or weak Serre closure is asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u wA wB uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- The canonical cohomology edge comparison, expressed as the mate of exact-functor
cohomology under the ordinary and bounded-below derived adjunctions.

Source: Stacks Project, sites-cohomology.tex, Tag 0D7U, acyclic-cohomology edge;
derived.tex, Tag 09T5, canonical derived adjunction
(blueprint: lem-fd-bounded-below-acyclic-heart-adjunction).

At L this is the ordinary adjoint of F(H^q(RG L)) → H^q(F RG L) → H^q(L),
where the second arrow is cohomology of the canonical derived counit. Thus the
comparison is fixed by the adjunctions and the termwise cohomology comparison. -/
noncomputable def derivedPlusHomologyMate
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A]
    [HasDerivedCategory.{wB} B] [EnoughInjectives B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) (q : ℤ) :
    G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q ⟶
      DerivedCategory.Plus.homologyFunctor B q ⋙ G :=
  (mateEquiv adj.derivedPlus adj
    (TwoSquare.mk _ _ _ _ (F.mapDerivedCategoryPlusHomologyFunctorIso q).hom)).natTrans

end CategoryTheory.Adjunction

namespace CategoryTheory.RingedToposMorphism

set_option synthInstance.maxHeartbeats 200000 in
-- Resolve sheaf-module instances in both localized full subcategories.
set_option maxHeartbeats 1600000 in
-- Elaborate the module categories and both full-subcategory inclusions.
/-- The exact module pullback and derived module direct image restrict to inverse
bounded-below equivalences on the two heart classes, with their canonical unit,
counit and natural edge isomorphisms.

Source: Stacks Project, sites-cohomology.tex, Tags 0D7S, 0D7T and 0D7U;
weak Serre closure is unnecessary for equivalences of full subcategories alone.
(blueprint: lem-fd-bounded-below-acyclic-heart-adjunction).

Proof plan:
1. The small-site module categories are Grothendieck abelian and have enough
injectives (lem-pur-ringed-site-grothendieck-abelian,
lem-sp-grothendieck-enough-injectives). The ordinary adjunction identifies F with
module pullback (lem-weil-pbc-ringed-topoi-module-adjunction). Exactness gives
termwise DF and its cohomology comparison (lem-weil-pbc-exact-functor-bounded-below),
and lem-trf-bounded-below-derived-adjunction supplies its canonical adjunction.
2. For M in P, positive acyclicity and negative vanishing
(lem-weil-pbc-derived-functor-negative-vanishing) reduce the derived heart unit
to degree zero. Its normalization is the ordinary unit by
lem-weil-pbc-derived-adjunction-single-zero. The cohomology criterion
lem-weil-pbc-derived-plus-iso-on-cohomology makes this unit invertible.
3. For K with cohomology in P, exactness identifies H^q(DF K) with F(H^q K).
Apply lem-fd-acyclic-heart-edge and the unit identity of
lem-fd-derived-unit-counit-cohomology-compatibility. The heart unit and edge are
invertible, so every cohomology of the derived unit is invertible, hence so is it.
4. For L with cohomology in P.map F, write each H^q L as F M up to isomorphism.
The same edge lemma and counit compatibility identify cohomology of the derived
counit with the heart counit. The latter is invertible by the triangle identity
and invertibility of the unit on M. Apply the cohomology criterion again.
5. DF preserves the specified class by exactness. The edge, the chosen heart
isomorphism and the inverse heart unit identify H^q(RG L) with M in P;
isomorphism closure gives preservation by RG. Restrict the canonical adjunction
to these full subcategories. Its invertible unit and counit give inverse equivalences.
6. Truncation and adjunction naturality identify the edge with the mate defined
above and make it natural in L and heart maps. The adjunction triangle identities
are inherited by the restrictions. The final natural isomorphism is precisely
H^q(RG L) ≅ G(H^q L), in every integer degree. No subobject, quotient or
extension closure was used. -/
theorem boundedBelowAcyclicHeartAdjunction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wA} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (F : ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (adj : F ⊣ f.modules) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (fun (_hF : F.Additive)
      (_hA : IsGrothendieckAbelian.{u} (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))) ↦
    letI := _hF
    letI := _hA
    ∀ (P : ObjectProperty
      (ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)))
      [P.ContainsZero] [P.IsClosedUnderIsomorphisms],
      (∀ M, P M → IsIso (adj.unit.app M)) →
      (∀ M, P M → ∀ p : ℕ, 0 < p →
        IsZero ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
          (f.modules.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj (F.obj M))))) →
      (∀ X : DerivedCategory.Plus
          (ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)),
        (∀ q : ℤ, P ((DerivedCategory.Plus.homologyFunctor _ q).obj X)) →
        (∀ q : ℤ, P.map F ((DerivedCategory.Plus.homologyFunctor _ q).obj
          (F.mapDerivedCategoryPlus.obj X))) ∧ IsIso (adj.derivedPlus.unit.app X)) ∧
      (∀ Y : DerivedCategory.Plus
          (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)),
        (∀ q : ℤ, P.map F ((DerivedCategory.Plus.homologyFunctor _ q).obj Y)) →
        (∀ q : ℤ, P ((DerivedCategory.Plus.homologyFunctor _ q).obj
          (f.modules.rightDerivedFunctorPlus.obj Y))) ∧
          IsIso (adj.derivedPlus.counit.app Y)) ∧
      (∃ E :
        ((DerivedCategory.homologyProperty P).inverseImage DerivedCategory.Plus.ι).FullSubcategory ≌
          ((DerivedCategory.homologyProperty (P.map F)).inverseImage
            DerivedCategory.Plus.ι).FullSubcategory,
        E.functor ⋙
            ((DerivedCategory.homologyProperty (P.map F)).inverseImage DerivedCategory.Plus.ι).ι =
          ((DerivedCategory.homologyProperty P).inverseImage DerivedCategory.Plus.ι).ι ⋙
            F.mapDerivedCategoryPlus ∧
        E.inverse ⋙
            ((DerivedCategory.homologyProperty P).inverseImage DerivedCategory.Plus.ι).ι =
          ((DerivedCategory.homologyProperty (P.map F)).inverseImage DerivedCategory.Plus.ι).ι ⋙
            f.modules.rightDerivedFunctorPlus ∧
        (∀ X, HEq
          (((DerivedCategory.homologyProperty P).inverseImage DerivedCategory.Plus.ι).ι.map
            (E.unitIso.hom.app X)) (adj.derivedPlus.unit.app X.obj)) ∧
        (∀ Y, HEq
          (((DerivedCategory.homologyProperty (P.map F)).inverseImage
            DerivedCategory.Plus.ι).ι.map (E.counitIso.hom.app Y))
          (adj.derivedPlus.counit.app Y.obj))) ∧
      (∀ q : ℤ, ∃ e :
        ((DerivedCategory.homologyProperty (P.map F)).inverseImage DerivedCategory.Plus.ι).ι ⋙
            (f.modules.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor _ q) ≅
          ((DerivedCategory.homologyProperty (P.map F)).inverseImage DerivedCategory.Plus.ι).ι ⋙
            (DerivedCategory.Plus.homologyFunctor _ q ⋙ f.modules),
        e.hom = Functor.whiskerLeft
          ((DerivedCategory.homologyProperty (P.map F)).inverseImage DerivedCategory.Plus.ι).ι
          (adj.derivedPlusHomologyMate q)))
      (adj.left_adjoint_additive)
      (SheafOfModules.isGrothendieckAbelian
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) := by
  sorry

end CategoryTheory.RingedToposMorphism
