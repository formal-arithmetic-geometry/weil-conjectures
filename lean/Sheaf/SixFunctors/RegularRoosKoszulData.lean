/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedCompleteKoszulReconstruction
public import Sheaf.CategoryTheory.DerivedTowerCounitProjections
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Data.List.TFAE
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Regular quotient Roos completeness and the canonical Koszul unit

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E; sites-cohomology.tex,
Tag 0941; derived.tex, Tags 09T5 and 0FND
(blueprint: lem-sf-regular-roos-koszul-unit).

All limits below are total derived limits of strict towers, not ordinary product cones.
The index `n : ℕ` represents the positive exponent `n+1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RegularRoosKoszul

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})

/-- The existing underlying ring sheaf, with independent site universes.
Source: Stacks 0A0E (blueprint: lem-sf-regular-roos-koszul-unit). -/
abbrev ring := (sheafCompose J
  (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

/-- The recorded category of module sheaves, with no additional structure chosen.
Source: Stacks 0A0E (blueprint: lem-sf-regular-roos-koszul-unit). -/
abbrev Modules := ringedSiteModules.{max c v r, max c v r, v, c} (ring.{c, v, r} R)

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules.{c, v, r} R)]

/-- The comparison of the already specified total derived limit `koszulRlim`.
It is chosen together with that functor by its right-derived universal property.
Source: Stacks 0941 (blueprint: lem-sf-regular-roos-koszul-unit). -/
def limitComparison :
    (lim : (ℕᵒᵖ ⥤ Modules.{c, v, r} R) ⥤ Modules.{c, v, r} R).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ koszulRlim R :=
  Classical.choose (Classical.choose_spec
    (ringedStrictTowerHomotopyLimitIndependentCoefficients.{w, c, v, max c v r} J (ring.{c, v, r} R)
      (fun U a b ↦ @mul_comm (R.obj.obj U) _ a b)))

attribute [local irreducible] koszulRlim limitComparison

/-- The specified total derived limit of any strict tower of complexes.
Source: Stacks 0941 (blueprint: def-sf-normalized-strict-tower-augmentation). -/
def towerLimit (T : ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, r} R) ℤ) :
    DerivedCategory.{w} (Modules.{c, v, r} R) :=
  (koszulRlim R).obj (DerivedCategory.Q.obj (koszulTowerComplex R T))

/-- The derived constant-tower/limit unit on a representative: localize the ordinary
constant/limit adjunction unit and follow the total right-derived comparison. This is
the representative formula for the normalized derived adjunction unit of the recorded
counit-projection theorem, including the exact-constant factorization.
Source: Stacks 09T5, 0FND, 0941 (blueprint: lem-sf-regular-roos-koszul-unit). -/
def constantUnit (Q : CochainComplex (Modules.{c, v, r} R) ℤ) :
    DerivedCategory.Q.{w}.obj Q ⟶ towerLimit.{c, v, r, w} R ((Functor.const ℕᵒᵖ).obj Q) :=
  DerivedCategory.Q.map
    ((Adjunction.mapHomologicalComplex (.up ℤ)
      (constLimAdj : (Functor.const ℕᵒᵖ : Modules.{c, v, r} R ⥤ _) ⊣ lim)).unit.app Q) ≫
    (limitComparison.{c, v, r, w} R).app
      (koszulTowerComplex R ((Functor.const ℕᵒᵖ).obj Q))

/-- The specified unit for any strictly augmented tower, using the derived adjunction
unit and the actual strict augmentation, using its canonical representative formula.
Source: Stacks 09T5, 0FND, 0941 (blueprint: lem-sf-regular-roos-koszul-unit). -/
def augmentedUnit (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
    (T : ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, r} R) ℤ)
    (α : (Functor.const ℕᵒᵖ).obj Q ⟶ T) :
    DerivedCategory.Q.{w}.obj Q ⟶ towerLimit.{c, v, r, w} R T :=
  DerivedCategory.Q.map
    ((Adjunction.mapHomologicalComplex (.up ℤ)
      (constLimAdj : (Functor.const ℕᵒᵖ : Modules.{c, v, r} R ⥤ _) ⊣ lim)).unit.app Q ≫
      (lim.mapHomologicalComplex (.up ℤ)).map (koszulTowerComplexMap R α)) ≫
    (limitComparison.{c, v, r, w} R).app (koszulTowerComplex R T)

/-- The normalized augmented unit equals the previous formula using the constant unit.
Source: Stacks 0941 (blueprint: def-sf-normalized-strict-tower-augmentation).
Proof: naturality of the right-derived comparison moves the strict augmentation across
that comparison; functoriality then combines the localized ordinary unit and limit map. -/
theorem augmentedUnit_previous_formula
    (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
    (T : ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, r} R) ℤ)
    (α : (Functor.const ℕᵒᵖ).obj Q ⟶ T) :
    constantUnit.{c, v, r, w} R Q ≫
        (koszulRlim R).map (DerivedCategory.Q.map
          (koszulTowerComplexMap.{c, v, max c v r} R α)) =
      DerivedCategory.Q.map
        ((Adjunction.mapHomologicalComplex (.up ℤ)
          (constLimAdj : (Functor.const ℕᵒᵖ : Modules.{c, v, r} R ⥤ _) ⊣ lim)).unit.app Q ≫
          (lim.mapHomologicalComplex (.up ℤ)).map (koszulTowerComplexMap.{c, v, max c v r} R α)) ≫
        (limitComparison.{c, v, r, w} R).app (koszulTowerComplex R T) := by
  have hn := (limitComparison.{c, v, r, w} R).naturality
    (koszulTowerComplexMap.{c, v, max c v r} R α)
  dsimp only [Functor.comp_map] at hn
  unfold constantUnit
  rw [Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ DerivedCategory.Q.map
      ((Adjunction.mapHomologicalComplex (.up ℤ)
        (constLimAdj : (Functor.const ℕᵒᵖ : Modules.{c, v, r} R ⥤ _) ⊣ lim)).unit.app Q) ≫ f)
    hn.symm

/-- The degree-zero Koszul unit for the chosen representative of the same derived object.
Source: Stacks 099B, 0A0E (blueprint: lem-sf-regular-roos-koszul-unit). -/
def koszulUnit (P : DerivedCategory.{w} (Modules.{c, v, r} R))
    (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
    (e : DerivedCategory.Q.{w}.obj Q ≅ P) (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections) :
    P ⟶ koszulCompletion R Q t :=
  e.inv ≫ augmentedUnit.{c, v, r, w} R Q (koszulTensorTower R Q t) (koszulStrictAugmentation R Q t)

/-- The quotient completion object, computed by the actual total derived limit.
Source: Stacks 0941, 0A0E (blueprint: lem-sf-regular-roos-koszul-unit). -/
def quotientLimit (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections) :
    DerivedCategory.{w} (Modules.{c, v, r} R) :=
  towerLimit.{c, v, r, w} R (reductionTensorTower R Q t)

/-- The specified quotient unit, obtained from the strict quotient augmentation.
Source: Stacks 0941, 0A0E (blueprint: lem-sf-regular-roos-koszul-unit). -/
def quotientUnit (P : DerivedCategory.{w} (Modules.{c, v, r} R))
    (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
    (e : DerivedCategory.Q.{w}.obj Q ≅ P) (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections) :
    P ⟶ quotientLimit.{c, v, r, w} R Q t :=
  e.inv ≫ augmentedUnit.{c, v, r, w} R Q (reductionTensorTower R Q t)
    (koszulStrictAugmentation R Q t ≫ koszulTensorTowerComparison R Q t)

/-- The specified quotient chain comparison after total derived inverse limit.
Source: Stacks 0A0E (blueprint: lem-sf-regular-roos-koszul-unit). -/
def comparison (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections) :
    koszulCompletion R Q t ⟶ quotientLimit.{c, v, r, w} R Q t :=
  (koszulRlim R).map (DerivedCategory.Q.map
    (koszulTowerComplexMap R (koszulTensorTowerComparison R Q t)))

/-- Tensoring a representative map, keeping the tensor functors explicit in its type.
Source: Stacks 0941 (blueprint: def-sf-regular-roos-koszul-data). -/
def tensorComplexMap {Q Q' : CochainComplex (Modules.{c, v, r} R) ℤ} (f : Q ⟶ Q') :
    koszulTensorFunctor.{c, v, max c v r} R Q ⟶
      koszulTensorFunctor.{c, v, max c v r} R Q' :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  ((MonoidalCategory.curriedTensor (Modules.{c, v, r} R)).map₂CochainComplex.flip).map f

attribute [irreducible] tensorComplexMap

/-- The map of tensor towers induced by a map of representative complexes. This is
whiskering of the recorded total tensor bifunctor, with no new tensor construction.
Source: Stacks 0A0E (blueprint: lem-sf-regular-roos-koszul-unit). -/
def tensorTowerMap {Q Q' : CochainComplex (Modules.{c, v, r} R) ℤ} (f : Q ⟶ Q')
    (T : ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, r} R) ℤ) :
    T ⋙ koszulTensorFunctor R Q ⟶ T ⋙ koszulTensorFunctor R Q' :=
  Functor.whiskerLeft T (tensorComplexMap.{c, v, r} R f)

/-- The actual map on Koszul limits induced by tensoring a map of complexes.
Source: Stacks 0A0E (blueprint: lem-sf-regular-roos-koszul-unit). -/
def koszulMap {Q Q' : CochainComplex (Modules.{c, v, r} R) ℤ} (f : Q ⟶ Q')
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections) :
    koszulCompletion R Q t ⟶ koszulCompletion R Q' t :=
  (koszulRlim R).map (DerivedCategory.Q.map (koszulTowerComplexMap R
    (tensorTowerMap.{c, v, r} R f (principalKoszulTower R t))))

/-- The actual map on quotient limits induced by tensoring a map of complexes.
Source: Stacks 0A0E (blueprint: lem-sf-regular-roos-koszul-unit). -/
def quotientMap {Q Q' : CochainComplex (Modules.{c, v, r} R) ℤ} (f : Q ⟶ Q')
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections) :
    quotientLimit.{c, v, r, w} R Q t ⟶ quotientLimit.{c, v, r, w} R Q' t :=
  (koszulRlim R).map (DerivedCategory.Q.map (koszulTowerComplexMap R
    (tensorTowerMap.{c, v, r} R f (principalReductionTower R t))))

variable [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{max c v r}]
  [∀ W : C, HasSheafify (J.over W) CommRingCat.{max c v r}]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ W : C, HasDerivedCategory.{w}
  (SheafOfModules.{max c v r} ((sheafCompose (J.over W)
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over W)))]

/-- The recorded exact derived slice restriction, with the target ring sheaf written
as the underlying ring of `R.over W`. Only the definitional presentation changes.
Source: Stacks 08JB (blueprint: lem-sf-regular-roos-koszul-unit). -/
def restriction (W : C) :
    DerivedCategory.{w} (Modules.{c, v, r} R) ⥤
      DerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose (J.over W)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over W))) :=
  letI : HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((ring.{c, v, r} R).over W)) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose (J.over W)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over W))))
  ringedDerivedRestrictionGeneral.{c, v, max c v r, max c v r, w, w} (ring.{c, v, r} R) W

/-- Local derived completeness tested against all slice sections in the principal ideal.
This is the predicate in the regular Roos criterion, with its original tests unchanged.
Source: Stacks 0999, 099B (blueprint: def-sf-regular-roos-koszul-data). -/
def locallyComplete (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections)
    (P : DerivedCategory.{w} (Modules.{c, v, r} R)) : Prop :=
  ∀ (W : C) (f : ((R.over W).obj ⋙ forget CommRingCat).sections),
    (∃ y : R.obj.obj (op W),
      (globalSectionMultiplication.{c, v, max c v r} R t).val.app (op W) y =
        f.val (op (Over.mk (𝟙 W)))) →
    IsZero ((derivedInternalHomOfUniverses.{max c v, v, r, w}
        (J.over W) (R.over W)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalizationOfUniverses.{max c v r, max c v, v} (R.over W) f)),
        (restriction.{c, v, r, w} R W).obj P))

attribute [irreducible] locallyComplete


end CategoryTheory.RegularRoosKoszul
