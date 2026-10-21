/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.SectionComparisonArrows
public import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback

/-! # Counit-normalized local section comparison formulas

Source: main-20261015, sec-smooth-purity/sk-thm-dnc, opening and Local construction
(blueprint: def-trf-section-local-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
open SectionComparisonArrows

/-- Units pull back along every scheme morphism.
Source: sk-thm-dnc, domain checks (blueprint: def-trf-section-local-comparison-data).
Proof: apply the global-sections ring map to the unit N; ring homomorphisms preserve
units and natural-number casts, including on the empty scheme. -/
theorem invertibleOnSource (N : ℕ) {X T : Scheme.{u}} (v : X ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) : IsUnit (N : Γ(X, ⊤)) := by
  simpa only [map_natCast] using hT.map v.appTop.hom

/-- The degree-zero finite Tate sheaf with its even shift.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
def tateObject (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (d : ℕ) : DerivedCategoryModule A T :=
  ((_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateTwist T N A hA d))⟦2 * (d : ℤ)⟧

/-- Tate pullback, using the root-normalized comparison, degree-zero localization and shifts.
Source: sk-thm-dnc, Local construction (blueprint: def-trf-section-local-comparison-data).
-/
@[irreducible]
def tatePullback (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))) (d : ℕ) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj (tateObject A N hA T d) ≅
      tateObject A N hA T' d :=
  ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.commShiftIso
    (2 * (d : ℤ))).app _ ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v).app _ ≪≫
          (_root_.DerivedCategory.singleFunctor _ 0).mapIso
            ((Scheme.finiteEtaleTwistPullbackData A N hN hA).c v hT hT' (d : ℤ)))

/-- The explicit right functor in the ordinary affine-space adjunction.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
def affineRight (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (d : ℕ) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin d)) T) :=
  ((upperStar (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) T ↘ T)).mapDerivedCategory ⋙
    derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) T)
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin d)) T) N A hA d))) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- Compare the chosen affine-space right adjoint with the explicit affine adjunction,
using uniqueness respecting counits, and remove the inverse-image coefficient unit.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def affineDualizingIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (_hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T] (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d) :
    dualizingComplex (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ≅
        tateObject A N hA (AffineSpace (ULift.{u} (Fin d)) T) d :=
  ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T)).rightAdjointUniq
        adj).app
          (𝟙_ _) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) T)
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin d)) T) N A hA d))).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin d)) T ↘ T)).symm.app (𝟙_ _) ≪≫
            leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A)
              (AffineSpace (ULift.{u} (Fin d)) T ↘ T)) ≪≫
        derivedTensorLeftUnitor (ModuleCat.{u + 1} A) _ _)

/-- Pull the affine comparison to a section and use canonical Tate pullback.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def affineSectionIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (r : T ⟶ AffineSpace (ULift.{u} (Fin d)) T)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d) :
    sectionInvariant A (AffineSpace (ULift.{u} (Fin d)) T ↘ T) r ≅ tateObject A N hA T d :=
  (upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.mapIso
      (affineDualizingIso A N hN hA T hT d adj) ≪≫
    tatePullback A N hN hA r
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin d)) T ↘ T) hT) hT d


/-- Finite-type sources over a Noetherian scheme are Noetherian.
Source: sk-thm-dnc, domain checks (blueprint: def-trf-section-local-comparison-data).
Proof: local finite type preserves local Noetherianity, and quasi-compactness over
quasi-compact T makes the source quasi-compact. Apply IsNoetherian.mk. -/
theorem noetherianSource {X T : Scheme.{u}} [IsNoetherian T] (v : X ⟶ T)
    [LocallyOfFiniteType v] [QuasiCompact v] : IsNoetherian X := by
  exact isNoetherian_of_locallyOfFiniteType v

/-- Restriction to compatible sections of the unique counit-compatible locality comparison.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def sectionLocality (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (v : U ⟶ X) [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (f : X ⟶ T) [HasCompactification f] (f' : U ⟶ T) [HasCompactification f']
    (w : v ≫ f = f') (r : T ⟶ X) (r' : T ⟶ U) (hr : r' ≫ v = r) :
    sectionInvariant A f r ≅ sectionInvariant A f' r' := by
  subst f'
  let l := (existsUnique_etaleAmbientAdjointLocalityIso A v f
    (HasCompactification.compactification f) (HasCompactification.compactification (v ≫ f))
    (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedUpperShriek (ModuleCat.{u + 1} A) (v ≫ f))
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (v ≫ f))).exists.choose
  exact (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r' v r hr.symm).app _ ≪≫
    (upperStar (ModuleCat.{u + 1} A) r').leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app _ ≪≫
        l.app (𝟙_ _))

/-- Section-chart identification: invert the counit-normalized locality map, then apply
its standard affine-space adjunction. No orientation of a fibre is supplied.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def chartMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) (f : X ⟶ T) [HasCompactification f]
    (r : T ⟶ X) (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = f)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d) :
    sectionInvariant A f r ⟶ tateObject A N hA T d :=
  letI : IsNoetherian (AffineSpace (ULift.{u} (Fin d)) T) :=
    noetherianSource (AffineSpace (ULift.{u} (Fin d)) T ↘ T)
  (sectionLocality A e (AffineSpace (ULift.{u} (Fin d)) T ↘ T) f w
    (r ≫ e) r rfl).inv ≫ (affineSectionIso A N hN hA T hT d (r ≫ e) adj).hom

/-- The raw local comparison from the two chart identifications and Tate pullback.
Source: sk-thm-dnc, Local construction, composition of identifications
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def rawComparison (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (C : DerivedCategoryModule A T)
    (F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) T))
    (c : C ≅ tateObject A N hA T d)
    (f : F ≅ tateObject A N hA (AffineSpace (ULift.{u} (Fin 1)) T) d) :
    F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C :=
  f ≪≫ (tatePullback A N hN hA (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT
    (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) hT) d).symm ≪≫
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.mapIso c.symm

/-- Restriction at one, including the specified inverse-image section compositor.
Source: sk-thm-dnc, correction at one
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def restrictionAtOne (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {C : DerivedCategoryModule A T}
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) T)}
    (l : F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C) :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.obj F ≅ C :=
  (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.mapIso l ≪≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)
        (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T)).app C

/-- The discrepancy h = (i1*lambda) theta^(-1), in composition order.
Source: sk-thm-dnc, correction at one
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def discrepancy (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {C : DerivedCategoryModule A T}
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) T)}
    (l : F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C)
    (theta : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.obj F ≅ C) : C ≅ C :=
  theta.symm ≪≫ restrictionAtOne A T l

/-- The normalization is lambda followed by a*(h^(-1)).
Source: sk-thm-dnc, correction at one
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def normalizedComparison (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {C : DerivedCategoryModule A T}
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) T)}
    (l : F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C)
    (theta : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.obj F ≅ C) :
    F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj C :=
  l ≪≫ (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.mapIso
      (discrepancy A T l theta).symm


/-- Restrict the actual theta to the local affine base, using only inverse-image compositors.
Source: sk-thm-dnc, correction at one
(blueprint: def-trf-section-local-comparison-data). -/
@[irreducible]
def restrictedTheta (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S T : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] (b : T ⟶ S) :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj (family A g s)) ⟶
      (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj (sectionInvariant A g s) :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) T)
    (AffineSpace.map (ULift.{u} (Fin 1)) b)).app _).inv ≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) T ≫
          AffineSpace.map (ULift.{u} (Fin 1)) b)
        (AffineSpace.oneSection_comp_map b)).app _).hom ≫
      (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map (atOne A g s hs)
end AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
