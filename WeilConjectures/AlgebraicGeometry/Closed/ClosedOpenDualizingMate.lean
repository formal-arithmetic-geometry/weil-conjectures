/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.DualizingOpenMate.DualizingOpenMate
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
public import WeilConjectures.CategoryTheory.SixFunctors.CounitMateTransport
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.DualizingOpenMate.DualizingOpenMate
import all WeilConjectures.SixFunctors.Coefficient.CoefficientDualizingClosedAssembly
import WeilConjectures.AlgebraicGeometry.Open.OpenClosedCompactScalar
import all WeilConjectures.CategoryTheory.SixFunctors.CounitMateTransport

/-! # Counit normalization through an open and a closed chart

Source: the finite dualizing proof, paragraphs 2--3
(blueprint: dualizing-open-closed-mate-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [-instance] CategoryTheory.catToReflQuiver in
theorem scalarMap_eq_globalMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] :
    ExceptionalCoefficients.dualizingScalarMap φ f =
      DualizingOpenMate.globalMate φ (HasCompactification.compactification f)
        (rightDerivedUpperShriek A f)
        (rightDerivedUpperShriek B f)
        (rightDerivedUpperShriekAdjunction A f)
        (rightDerivedUpperShriekAdjunction B f) := by
  rw [ExceptionalCoefficients.dualizingScalarMap_eq]
  unfold ExceptionalCoefficients.mateMap DualizingOpenMate.globalMate
  exact transpose_three_maps
    (rightDerivedUpperShriekAdjunction B f)
    (X := (scalarExtension φ X).obj
      ((rightDerivedUpperShriek A f).obj
        (𝟙_ (DerivedCategoryModule A S))))
    (ExceptionalCoefficients.comparisonInverse φ (HasCompactification.compactification f)
      ((rightDerivedUpperShriek A f).obj
        (𝟙_ (DerivedCategoryModule A S))))
    ((scalarExtension φ S).map
      ((rightDerivedUpperShriekAdjunction A f).counit.app
        (𝟙_ (DerivedCategoryModule A S))))
    (ExceptionalCoefficients.unitIso φ S).hom

/-- A coefficient mate together with its defining counit equation.
Source: the finite dualizing proof, paragraph 3
(blueprint: closed-open-dualizing-mate). -/
structure CoefficientCounitMateData
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (b : F' ⊣ G') (Q : C ⥤ C') (T : D ⥤ D')
    (d : F ⋙ T ≅ Q ⋙ F') (M : D) where
  hom : Q.obj (G.obj M) ⟶ G'.obj (T.obj M)
  counit : F'.map hom ≫ b.counit.app (T.obj M) =
    d.inv.app (G.obj M) ≫ T.map (a.counit.app M)

/-- Transposing a morphism and evaluating the counit returns that morphism.
Source: adjunction transposition in the finite dualizing proof, paragraph 3
(blueprint: closed-open-dualizing-mate). -/
theorem coefficientCounitMate_counit
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {X : C} {Y : D} (x : F.obj X ⟶ Y) :
    F.map (counitTranspose a x) ≫ a.counit.app Y = x :=
  counitTranspose_counit a x

/-- Construct the mate and its counit law by adjunction transposition.
Source: the finite dualizing proof, paragraph 3
(blueprint: closed-open-dualizing-mate). -/
@[irreducible] def coefficientCounitMateData
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (b : F' ⊣ G') (Q : C ⥤ C') (T : D ⥤ D')
    (d : F ⋙ T ≅ Q ⋙ F') (M : D) : CoefficientCounitMateData a b Q T d M where
  hom := counitTranspose b (d.inv.app (G.obj M) ≫ T.map (a.counit.app M))
  counit := coefficientCounitMate_counit _ _

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The proper direct-image scalar isomorphism, with its canonical hom.
Source: proper finite coefficient extension
(blueprint: closed-open-dualizing-mate). -/
@[irreducible] def closedScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V P : Scheme.{u}} [IsNoetherian V] [IsNoetherian P]
    (i : V ⟶ P) [IsClosedImmersion i] :
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ⋙ scalarExtension φ P ≅
      scalarExtension φ V ⋙ (lowerStar (ModuleCat.{u + 1} B) i).rightDerivedFunctor := by
  letI (M : DerivedCategoryModule A V) : IsIso ((scalarMate φ i).app M) :=
    (properFiniteCoefficientExtension φ i).1 M
  exact NatIso.ofComponents (fun M ↦ asIso ((scalarMate φ i).app M))
    (fun f ↦ (scalarMate φ i).naturality f)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem closedScalarIso_hom_app
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V P : Scheme.{u}} [IsNoetherian V] [IsNoetherian P]
    (i : V ⟶ P) [IsClosedImmersion i] (M : DerivedCategoryModule A V) :
    (closedScalarIso φ i).hom.app M = (scalarMate φ i).app M := by
  unfold closedScalarIso
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The constructed closed mate, retaining its counit law as data.
Source: the finite dualizing proof, paragraph 3
(blueprint: closed-open-dualizing-mate). -/
@[irreducible] def closedCoefficientMateData
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V P : Scheme.{u}} [IsNoetherian V] [IsNoetherian P]
    (i : V ⟶ P) [IsClosedImmersion i] (M : DerivedCategoryModule A P) :
    CoefficientCounitMateData
      (rightDerivedLowerStarUpperShriekAdjunctionOfIsProper A i)
      (rightDerivedLowerStarUpperShriekAdjunctionOfIsProper B i)
      (scalarExtension φ V) (scalarExtension φ P) (closedScalarIso φ i) M :=
  coefficientCounitMateData _ _ _ _ _ _

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The closed coefficient mate in the ordinary direct-image adjunction.
Its inverse direct-image comparison exists by proper finite coefficient extension.
Source: finite dualizing proof, paragraph 3
(blueprint: dualizing-open-closed-mate-normalization). -/
def closedDualizingCoefficientMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V P : Scheme.{u}} [IsNoetherian V] [IsNoetherian P]
    (i : V ⟶ P) [IsClosedImmersion i] (M : DerivedCategoryModule A P) :
    (scalarExtension φ V).obj
        ((rightDerivedUpperShriek A i).obj M) ⟶
      (rightDerivedUpperShriek B i).obj
        ((scalarExtension φ P).obj M) :=
  (closedCoefficientMateData φ i M).hom

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem closedMate_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V P : Scheme.{u}} [IsNoetherian V] [IsNoetherian P]
    (i : V ⟶ P) [IsClosedImmersion i] (M : DerivedCategoryModule A P) :
    closedDualizingCoefficientMate φ i M = (closedCoefficientMateData φ i M).hom := by
  rfl

end AlgebraicGeometry.Etale
