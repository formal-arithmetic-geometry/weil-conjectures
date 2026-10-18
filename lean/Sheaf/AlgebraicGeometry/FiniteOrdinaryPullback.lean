/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Canonical ordinary sections comparison and pullback

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
prop-trf-graph-frobenius-operator.proof.md, Steps 1--2; Stacks Tags 08J6 and 0D6E
(blueprint: def-trf-finite-ordinary-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Point sections and realization-inverse sections have the same scalar-normalized
terminal evaluation. Source: blueprint Steps 1--2; Stacks Tags 00YV and 08J6
(blueprint: def-trf-finite-ordinary-pullback).

Proof: restrict the intrinsic scalar action along the constant-scalar unit. The
sheafification unit identifies the resulting module sheaf with the original fixed-scalar
sheaf. Evaluation at the terminal object and the realization equivalence unit give the
displayed equation. These units are isomorphisms, so this specifies an isomorphism.
Every intrinsic module is in the essential image of realization; the equation on every
section there determines every component, and hence the natural isomorphism uniquely. -/
theorem finiteOrdinaryPointComparison_existsUnique
    (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] [Finite A] :
    ∃! e : pointFiniteSections D.k A ≅
        (sfIntrinsicModuleEquivalence (Spec (.of D.k)) A).inverse ⋙
          (sheafSections (ProEt.topology (Spec (.of D.k)))
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
              (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))),
      ∀ (M : Sheaf (ProEt.topology (Spec (.of D.k)))
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
        (s : M.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        (e.hom.app ((sfIntrinsicModuleEquivalence (Spec (.of D.k)) A).functor.obj M) ≫
          ((sheafSections (ProEt.topology (Spec (.of D.k)))
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
              (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k)))))).map
                ((sfIntrinsicModuleEquivalence (Spec (.of D.k)) A).unitIso.inv.app M))
          (sfIntrinsicRealizationUnit (Spec (.of D.k)) A M
            (Opposite.op (ProEt.mk (𝟙 (Spec (.of D.k))))) s) = s := by
  sorry

/-- The unique terminal-section comparison, followed by terminal evaluation inverse.
Source: blueprint Steps 1--2; Stacks Tag 08J6
(blueprint: def-trf-finite-ordinary-pullback). -/
def finiteOrdinaryPointComparison (D : FiniteFieldDatum.{u})
    (A : Type u) [CommRing A] [Finite A] :
    pointFiniteSections D.k A ≅ proEtaleUnitLeraySections A (Spec (.of D.k)) :=
  (finiteOrdinaryPointComparison_existsUnique D A).exists.choose ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence (Spec (.of D.k)) A).inverse
      (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId _)).symm

/-- The functor underlying the recorded finiteOrdinarySections, with exactly its coefficient
category and localization universe. Source: blueprint ordinary-cohomology definition
(blueprint: def-trf-finite-ordinary-pullback). -/
abbrev finiteOrdinarySectionsFunctor (D : FiniteFieldDatum.{u})
    (A : Type u) [CommRing A] (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))] :
    proEtaleDerivedCategory Y A ⥤
      DerivedCategory.{u + 2} (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
  proEtaleConstantDerivedDirectImage (Y ↘ Spec (.of D.k)) A ⋙
    (pointFiniteSections D.k A).mapDerivedCategory

/-- Absolute sections in the localization universe of finiteOrdinarySections. This is
the same right-derived construction, with no restriction on the site universes.
Source: Stacks Tag 08J6 (blueprint: def-trf-finite-ordinary-pullback). -/
abbrev finiteOrdinaryAbsoluteSections (A : Type u) [CommRing A] [Finite A]
    (Y : Scheme.{u}) : proEtaleDerivedCategory Y A ⥤
      DerivedCategory.{u + 2} (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
  (proEtaleUnitLeraySections A Y).rightDerivedFunctor

/-- The canonical a_Y Leray comparison followed by exact point sections. The exact
postcomposition comparison and the scalar-normalized terminal identification fix all data.
Source: blueprint Steps 1--2; Stacks Tags 08J6 and 0D6E
(blueprint: def-trf-finite-ordinary-pullback). -/
def finiteOrdinarySectionsComparison (D : FiniteFieldDatum.{u})
    (A : Type u) [CommRing A] [Finite A] (Y : Scheme.{u})
    [Y.Over (Spec (.of D.k))] :
    finiteOrdinarySectionsFunctor D A Y ≅ finiteOrdinaryAbsoluteSections A Y :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (proEtaleConstantModuleDirectImage (Y ↘ Spec (.of D.k)) A)
      (pointFiniteSections D.k A)).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (Functor.isoWhiskerLeft _ (finiteOrdinaryPointComparison D A) ≪≫
        Functor.isoWhiskerRight
          (proEtaleUnitLerayDirectImageIso A (Y ↘ Spec (.of D.k))).symm _ ≪≫
        proEtaleUnitLerayTerminalIso A (Y ↘ Spec (.of D.k)))

/-- Leray for arbitrary h in the coefficient localization of the recorded finite sections.
Source: Stacks Tag 0D6E (blueprint: def-trf-finite-ordinary-pullback). -/
def finiteOrdinaryAbsoluteLeray (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (proEtaleConstantRingPushforward A h).rightDerivedFunctor ⋙
        finiteOrdinaryAbsoluteSections A Y ≅ finiteOrdinaryAbsoluteSections A X :=
  Functor.rightDerivedFunctorCompIso' (proEtaleConstantRingPushforward A h)
    (proEtaleUnitLeraySections A Y) (proEtaleUnitLerayTerminalIso A h)

/-- Canonical direct-image global-sections identification in Fib_s composed with Ra_Y*.
It applies to every endomorphism, including semilinear ones.
Source: blueprint Steps 1--2; Stacks Tag 0D6E
(blueprint: def-trf-finite-ordinary-pullback). -/
def finiteOrdinaryLeray (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] [Finite A]
    {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))] (h : Y ⟶ Y) :
    (proEtaleConstantRingPushforward A h).rightDerivedFunctor ⋙
        finiteOrdinarySectionsFunctor D A Y ≅ finiteOrdinarySectionsFunctor D A Y :=
  Functor.isoWhiskerLeft _ (finiteOrdinarySectionsComparison D A Y) ≪≫
    finiteOrdinaryAbsoluteLeray A h ≪≫ (finiteOrdinarySectionsComparison D A Y).symm

/-- Ordinary pullback in the recorded Fib_s composed with Ra_Y* model: its derived unit
followed by canonical global sections of direct image. No k-linearity of h is assumed.
Source: blueprint Steps 1--2 (blueprint: def-trf-finite-ordinary-pullback). -/
def finiteOrdinaryPullback (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] [Finite A]
    {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))] (h : Y ⟶ Y)
    (M : proEtaleDerivedCategory Y A) :
    (finiteOrdinarySectionsFunctor D A Y).obj M ⟶
      (finiteOrdinarySectionsFunctor D A Y).obj
        ((proEtaleConstantRingDerivedPullback A h).obj M) :=
  (finiteOrdinarySectionsFunctor D A Y).map
      ((proEtaleConstantRingAdjunction A h).mapDerivedCategoryRightDerivedAdjunction.unit.app M) ≫
    (finiteOrdinaryLeray D A h).hom.app ((proEtaleConstantRingDerivedPullback A h).obj M)

/-- The comparison transports the actual ordinary unit pullback, for every endomorphism
(in particular both Phi^m and g^m). Source: blueprint Steps 1--2; Stacks Tag 0D6E
(blueprint: def-trf-finite-ordinary-pullback).

Proof: expand the finite ordinary pullback and its Leray comparison. Naturality of
finiteOrdinarySectionsComparison at the derived adjunction unit moves the source
comparison across that unit. Cancel its inverse with its hom at the target. What remains
is exactly the absolute unit followed by its terminal-object Leray comparison. -/
theorem finiteOrdinaryPullback_absolute_compatibility
    (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] [Finite A]
    {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))] (h : Y ⟶ Y)
    (M : proEtaleDerivedCategory Y A) :
    finiteOrdinaryPullback D A h M ≫
        (finiteOrdinarySectionsComparison D A Y).hom.app
          ((proEtaleConstantRingDerivedPullback A h).obj M) =
      (finiteOrdinarySectionsComparison D A Y).hom.app M ≫
        (finiteOrdinaryAbsoluteSections A Y).map
          ((proEtaleConstantRingAdjunction A h).mapDerivedCategoryRightDerivedAdjunction.unit.app
            M) ≫
        (finiteOrdinaryAbsoluteLeray A h).hom.app
          ((proEtaleConstantRingDerivedPullback A h).obj M) := by
  sorry

end WeilConjectures
