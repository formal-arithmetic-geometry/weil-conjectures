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
  let T := Spec (.of D.k)
  let E := sfIntrinsicModuleEquivalence T A
  let W := Opposite.op (ProEt.mk (𝟙 T))
  let Q := (sheafSections (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj W
  let P := pointFiniteSections D.k A
  let B := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)
  let adj := PresheafOfModules.sheafificationAdjunction
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
  let η : Q ⟶ E.functor ⋙ P :=
    { app M := (adj.unit.app (B.obj M.obj)).app W
      naturality M N f := by
        exact congrArg (fun g ↦ g.app W) (adj.unit.naturality (B.map f.hom)) }
  have hunit (M : Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
      IsIso (adj.unit.app (B.obj M.obj)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [adj, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj
        M).property
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    let _ := hunit M
    exact inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ W).map
      (adj.unit.app (B.obj M.obj))))
  let e : P ≅ E.inverse ⋙ Q := Iso.isoInverseComp (asIso η).symm
  have hn (M : Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
      η.app M ≫ e.hom.app (E.functor.obj M) ≫
        Q.map (E.unitIso.inv.app M) = 𝟙 (Q.obj M) := by
    dsimp [e, Iso.isoInverseComp]
    simp only [Category.id_comp, Category.assoc]
    have ht := (inv η).naturality (E.unitIso.inv.app M)
    dsimp only [Functor.comp_obj, Functor.comp_map] at ht
    rw [← ht]
    simp only [← P.map_comp_assoc, E.counitIso_functor_comp]
    rw [P.map_id, Category.id_comp]
    exact (asIso η).hom_inv_id_app M
  refine ⟨e, ?_, ?_⟩
  · intro M s
    exact ConcreteCategory.congr_hom (hn M) s
  · intro e' he'
    change P ≅ E.inverse ⋙ Q at e'
    have heq (M : Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
        e'.hom.app (E.functor.obj M) = e.hom.app (E.functor.obj M) := by
      apply (cancel_mono (Q.map (E.unitIso.inv.app M))).mp
      have : IsIso (η.app M) :=
        (NatTrans.isIso_iff_isIso_app η).mp ‹IsIso η› M
      apply (cancel_epi (η.app M)).mp
      rw [hn]
      ext s
      exact he' M s
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply (cancel_epi (P.map (E.counitIso.hom.app N))).mp
    have h₁ := e'.hom.naturality (E.counitIso.hom.app N)
    have h₂ := e.hom.naturality (E.counitIso.hom.app N)
    exact h₁.trans ((congrArg
      (fun f ↦ f ≫ (E.inverse ⋙ Q).map (E.counitIso.hom.app N))
      (heq (E.inverse.obj N))).trans h₂.symm)

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
  dsimp [finiteOrdinaryPullback, finiteOrdinaryLeray]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← NatTrans.naturality_assoc]
  rfl


end WeilConjectures
