/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSpanModuleComparisonData
import all WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization

/-! # Derived normalization of a supplied ordinary scalar comparison

Source: Stacks Project, Derived Categories, Tags 070Y and 09T5.
(blueprint: lem-sf-finite-span-scalar-derived). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteSpanComparison

private theorem unitQ_eq_unit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (P : CochainComplex A ℤ) :
    F.rightDerivedFunctorUnitQ P =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  change 𝟙 _ ≫ _ ≫ F.rightDerivedFunctor.map (𝟙 _) = _
  rw [F.rightDerivedFunctor.map_id, Category.comp_id, Category.id_comp]

private theorem chainNormalization (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : CochainComplex (modules l Y) ℤ)
    (I : CochainComplex (modules l X) ℤ) [I.IsKInjective]
    (a : ((inverse l f (d.coefficientMap f)).mapHomologicalComplex (.up ℤ)).obj L ⟶ I) :
    (nativeDerivedAdjunction l f).homEquiv _ _
        ((inverse l f (d.coefficientMap f)).mapDerivedCategoryFactors.hom.app L ≫
          DerivedCategory.Q.map a) ≫
      ((direct l f (d.coefficientMap f)).rightDerivedFunctorObjQIso I).hom =
    DerivedCategory.Q.map
      (((adjunction l f (d.coefficientMap f)).mapHomologicalComplex (.up ℤ)).homEquiv L I a) := by
  let F := inverse l f (d.coefficientMap f)
  let G := direct l f (d.coefficientMap f)
  let adj := adjunction l f (d.coefficientMap f)
  have hη := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso (modules l Y) (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ (.up ℤ)).obj L)
  rw [factorsh_quotient] at hη
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient, qh_map_quotient] at hη
  change (nativeDerivedAdjunction l f).unit.app (DerivedCategory.Q.obj L) ≫
    G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app L) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app L) ≫
        G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj L)) at hη
  rw [← unitQ_eq_unit] at hη
  rw [Adjunction.homEquiv_unit, G.rightDerivedFunctor.map_comp, ← Category.assoc, hη]
  simp only [Category.assoc]
  rw [← G.rightDerivedFunctorUnitQ_naturality_assoc a,
    G.rightDerivedFunctorUnitQ_eq I, Iso.inv_hom_id,
    Category.comp_id, ← DerivedCategory.Q.map_comp, Adjunction.homEquiv_unit]

/-- The normalized right-derived scalar comparison, constructed from the ordinary mate.
Source: Stacks Project, Derived Categories, Tags 070Y and 09T5; Cohomology on Sites,
Tag 07A6. (blueprint: lem-sf-finite-span-scalar-derived).

Proof. Postcomposition by the exact equivalence commutes with right derivation.
Apply right derivation to the ordinary push comparison, use the composition comparison
for the K-injective-preserving source equivalence, and replace its right derived functor
by its exact localization. The unit factorization of these four isomorphisms gives the
normalization equation for every complex. The exact derived mate theorem identifies this
comparison with the mate of the localized ordinary pull comparison. Finally the derived
adjunction unit factorization, followed by naturality of the direct-image derived unit,
identifies transposition of a chain map with ordinary transposition. On a K-injective
complex that derived unit is the inverse computation isomorphism, so cancellation gives
the displayed chain-map equation. No scheme finiteness or field hypothesis is needed. -/
theorem finiteSpanScalarTransportDerived (l : ℕ) [Fact l.Prime] [d : Data.{u} l]
    (hm :
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (mateEquiv (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (adjunction l f (d.coefficientMap f)) (d.pullComparison f).inv).natTrans =
        (d.pushComparison f).hom)) :
    ∃ β : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctor ⋙
        (equivalence l Y (d.theta Y)).functor.mapDerivedCategory ≅
      (equivalence l X (d.theta X)).functor.mapDerivedCategory ⋙
        (direct l f (d.coefficientMap f)).rightDerivedFunctor,
      let d' : Data.{u} l := { d with derivedPushComparison := β }
      letI := d'
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (internal l X) ℤ),
    (equivalence l Y (d'.theta Y)).functor.mapDerivedCategory.map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctorUnitQ P) ≫
      (d'.derivedPushComparison f).hom.app (DerivedCategory.Q.obj P) ≫
      (direct l f (d'.coefficientMap f)).rightDerivedFunctor.map
        ((equivalence l X (d'.theta X)).functor.mapDerivedCategoryFactors.hom.app P) =
    (equivalence l Y (d'.theta Y)).functor.mapDerivedCategoryFactors.hom.app
      (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).mapHomologicalComplex
        (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (d'.pushComparison f) (.up ℤ)).hom.app P) ≫
      (direct l f (d'.coefficientMap f)).rightDerivedFunctorUnitQ
        (((equivalence l X (d'.theta X)).functor.mapHomologicalComplex (.up ℤ)).obj P)) ∧
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y), DerivedNormalization l f) := by
  refine ⟨fun f ↦ rightSquareIso
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f)
    (equivalence l _ (d.theta _)).functor (equivalence l _ (d.theta _)).functor
    (direct l f (d.coefficientMap f)) (d.pushComparison f), ?_⟩
  constructor
  · intro X Y f P
    simpa only [unitQ_eq_unit] using
      rightSquareFactors (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f)
        (equivalence l Y (d.theta Y)).functor (equivalence l X (d.theta X)).functor
        (direct l f (d.coefficientMap f)) (d.pushComparison f) P
  · intro X Y f
    constructor
    · exact rightSquareMate
        (equivalence l Y (d.theta Y)).functor (equivalence l X (d.theta X)).functor
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
        (adjunction l f (d.coefficientMap f)) (d.pullComparison f) (d.pushComparison f) (hm f)
    · exact chainNormalization l f

end AlgebraicGeometry.ProEtale.FiniteSpanComparison
