/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality

/-! # The derived direct-image mate on a bounded-below complex

Source: Stacks Project, Derived Categories, Lemmas 0DVC and 09T5, and
Pro-etale Cohomology, Tag 09A6 (blueprint: lem-sp-derived-adjunction-from-underived).

The three component maps below retain the exact-functor factorization isomorphisms.
Thus the statement does not assume that comparison sends K-injectives to K-injectives.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The etale right-derived unit after applying exact site comparison.
Source: Stacks, Derived Categories, Lemma 09T5 and the right-derived-functor unit
(blueprint: lem-sp-derived-adjunction-from-underived). -/
noncomputable def fixedComparisonEtaleUnitPlus (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (f : U ⟶ T)
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.map
    ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient _).obj K))

/-- The localization of the degreewise ordinary mate, with its source identified by
exact-functor factorization. The ordinary comparison is the counit mate of the
inverse pullback comparison, as in `fixedComparisonDirectImageMatePlus_counit`.
Source: Stacks, Pro-etale Cohomology, Tag 09A6
(blueprint: lem-sp-derived-adjunction-from-underived). -/
noncomputable def fixedComparisonUnderivedMatePlus (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (f : U ⟶ T)
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlusFactorsh.hom.app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) f).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj K)) ≫
    DerivedCategory.Plus.Qh.map
      ((NatTrans.mapHomotopyCategoryPlus
        (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} A))).app
          ((HomotopyCategory.Plus.quotient _).obj K))

/-- The pro-etale right-derived unit at the termwise comparison of `K`, with its target
identified by exact-functor factorization. No K-injectivity of that comparison is asserted.
Source: Stacks, Derived Categories, Lemma 09T5 and the right-derived-functor unit
(blueprint: lem-sp-derived-adjunction-from-underived). -/
noncomputable def fixedComparisonProEtaleUnitPlus (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (f : U ⟶ T)
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusUnit.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj K)) ≫
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.map
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlusFactorsh.inv.app
        ((HomotopyCategory.Plus.quotient _).obj K))

private lemma baseChange_factorization
    {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
    [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
    [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
    [EnoughInjectives B] [EnoughInjectives B']
    {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
    [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
    [PreservesFiniteLimits β] [PreservesFiniteColimits β]
    [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
    (e : G ⋙ γ ⟶ β ⋙ G') (K : HomotopyCategory.Plus B) :
    γ.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnit.app K) ≫
        (Functor.rightDerivedFunctorPlusBaseChange e).app (DerivedCategory.Plus.Qh.obj K) =
      (γ.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K)) ≫
        (G'.rightDerivedFunctorPlusUnit.app (β.mapHomotopyCategoryPlus.obj K) ≫
        G'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlusFactorsh.inv.app K)) := by
  simpa only [Category.assoc] using
    Functor.rightDerivedFunctorPlusBaseChange_fac_app e K

private lemma cancel_left_iso {C : Type*} [Category* C] {X Y Z : C}
    (e : X ⟶ Y) (m n : Y ⟶ Z) [IsIso e] (h : e ≫ m = e ≫ n) : m = n :=
  (cancel_epi e).1 h

/-- The canonical derived counit mate is induced by the ordinary mate on every
bounded-below complex, including complexes which are not K-injective.
Source: Stacks, Derived Categories, Lemmas 0DVC and 09T5; Pro-etale Cohomology, Tag 09A6
(blueprint: lem-sp-derived-adjunction-from-underived).

Proof: `fixedComparisonDirectImageMatePlus` is by definition the right-derived base change
`Functor.rightDerivedFunctorPlusBaseChange` of the ordinary comparison square
`lowerStarComparisonUpperStarBaseChange`. Its unit factorization
`Functor.rightDerivedFunctorPlusBaseChange_fac_app` at the class of `K` in the bounded-below
homotopy category is, after unfolding the three component maps and
`DerivedCategory.Plus.Q` as the quotient followed by `Qh` and reassociating, exactly the
asserted equality. No K-injectivity is used. -/
theorem fixedComparisonDirectImageMatePlus_from_underived
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (f : U ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    fixedComparisonEtaleUnitPlus A f K ≫
        (fixedComparisonDirectImageMatePlus A f).app (DerivedCategory.Plus.Q.obj K) =
      fixedComparisonUnderivedMatePlus A f K ≫ fixedComparisonProEtaleUnitPlus A f K := by
  exact baseChange_factorization
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} A))
    ((HomotopyCategory.Plus.quotient _).obj K)

/-- The right-derived etale direct-image unit itself is invertible on a K-injective
complex, before applying site comparison.
Source: Stacks, Derived Categories, Section K-injective complexes
(blueprint: lem-sp-derived-adjunction-from-underived).

Proof: the right-derived functor unit at a K-injective complex is invertible, by
`def-sfb-right-derived-functor`: the complex is already a resolution of itself and
an additive functor carries homotopy equivalences to homotopy equivalences. -/
theorem isIso_etaleDirectImageUnitPlus_of_isKInjective
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (f : U ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    [K.obj.IsKInjective] :
    IsIso ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient _).obj K)) := by
  let F := Etale.lowerStar (ModuleCat.{u + 1} A) f
  let H := (HomotopyCategory.Plus.quotient _).obj K
  have hu : IsIso (F.ιRightDerivedFunctorUnit.app H) := by
    change IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K.obj))
    infer_instance
  have he : DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app H) ≫
      F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj H) =
      F.ιRightDerivedFunctorUnit.app H := by
    change F.rightDerivedFunctorPlusιUnit.app H ≫ _ = _
    simp [Functor.rightDerivedFunctorPlusCompatibility]
  have : IsIso (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app H) ≫
      F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj H)) := by
    rw [he]
    exact hu
  have : IsIso (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app H)) :=
    IsIso.of_isIso_comp_right _
      (F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj H))
  exact isIso_of_reflects_iso (F.rightDerivedFunctorPlusUnit.app H) DerivedCategory.Plus.ι

/-- On a K-injective complex the etale comparison unit is invertible, as is its image
under exact site comparison.
Source: Stacks, Derived Categories, Section K-injective complexes
(blueprint: lem-sp-derived-adjunction-from-underived).

Proof: a K-injective complex computes the right-derived direct image, so its
right-derived unit is an isomorphism (`def-sfb-right-derived-functor`). A functor
preserves isomorphisms, giving the assertion after applying site comparison. -/
theorem isIso_fixedComparisonEtaleUnitPlus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (f : U ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    [K.obj.IsKInjective] : IsIso (fixedComparisonEtaleUnitPlus A f K) := by
  have := isIso_etaleDirectImageUnitPlus_of_isKInjective A f K
  dsimp only [fixedComparisonEtaleUnitPlus]
  exact Functor.map_isIso _ _

attribute [instance] isIso_fixedComparisonEtaleUnitPlus

/-- On a K-injective complex, cancel the invertible etale unit to compute the named
mate by the localized ordinary mate followed by the pro-etale comparison unit.
Source: Stacks, Derived Categories, Section K-injective complexes and Lemma 09T5
(blueprint: lem-sp-derived-adjunction-from-underived).

Proof: the preceding theorem makes the etale unit invertible. Precompose the equality
`fixedComparisonDirectImageMatePlus_from_underived` by its inverse and cancel.
The pro-etale unit stays in the formula, since the termwise comparison of a K-injective
complex need not itself be K-injective. This is step 4 of the node's proof. -/
theorem fixedComparisonDirectImageMatePlus_from_kinjective
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (f : U ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    [K.obj.IsKInjective] :
    (fixedComparisonDirectImageMatePlus A f).app (DerivedCategory.Plus.Q.obj K) =
      inv (fixedComparisonEtaleUnitPlus A f K) ≫
        fixedComparisonUnderivedMatePlus A f K ≫ fixedComparisonProEtaleUnitPlus A f K := by
  apply cancel_left_iso (fixedComparisonEtaleUnitPlus A f K)
  simpa only [IsIso.hom_inv_id_assoc] using
    fixedComparisonDirectImageMatePlus_from_underived A f K

end AlgebraicGeometry.ProEtale
