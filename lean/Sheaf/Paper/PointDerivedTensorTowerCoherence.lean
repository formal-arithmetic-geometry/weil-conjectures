/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

import Sheaf.Paper.SectionsScalarOrdinaryTower
public import Sheaf.Paper.PointDerivedSectionsTensorDescent
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Paper.PointFiniteFreeSectionsTensor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.CategoryTheory.ExactScalarTowerTransport

/-! # Ordinary scalar towers and point sections

Source: Stacks 03EK, 06YY, 0G7E, 0D6D and 04VG; the final paragraph of blueprint
main-20261015, def-weil-finite-coefficient-point
(blueprint: lem-weil-point-derived-tensor-tower-coherence).

All tensors below are ordinary change of rings. The completed sheaves supply the
coefficient rings, but no completion functor occurs in the assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 80000
set_option genCtorIdx false
set_option genSizeOf false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option linter.mathlibStandardSet false
set_option linter.overlappingInstances false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.haveILetI false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe t u m r
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.PointTensorTower

attribute [local irreducible] completedScalarChangeData CategoryTheory.Limits.limit
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedIntegralCoefficientSheafUnrestricted
  completedScalarTensorSection completedCoefficientMap
  integralScalarIntegerInclusion completedScalarRelativeDegree
  Padic
  Padic.coefficientExtensionIntegers
  HasDerivedCategory.standard SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom
  Functor.mapDerivedCategory Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryNatIso
attribute [local instance 20000] Algebra.toModule IntermediateField.algebra'

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]

/-- The already defined finite intermediate extensions, including repeated fields.
Source: blueprint coefficient conventions
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev Fields := {E : IntermediateField ℚ_[l] Ω // FiniteDimensional ℚ_[l] E}

/-- Finiteness is the property defining this subtype, not an extra assumption.
Source: blueprint coefficient conventions
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
instance finiteField (E : Fields l Ω) : FiniteDimensional ℚ_[l] E.1 := E.2


variable {l Ω} (k : Type t) [Field k]

/-- The original valuation ring; no second coefficient ring is introduced.
Source: Stacks 03EK (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev integers (E : Fields l Ω) := Padic.coefficientExtensionIntegers l E.1

/-- The recorded sheaf-module category at Spec k.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev modules (E : Fields l Ω) := SheafOfModules.{max u (t + 1)}
  (completedIntegralCoefficientSheafUnrestricted l E.1 (Spec (.of k)))

/-- The original unbounded cochain category.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev complexes (E : Fields l Ω) := CochainComplex (modules k E) ℤ

/-- Ordinary scalar extension on sheaves along the given field inclusion.
Source: Stacks 03EK (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev scalar {E L : Fields l Ω} (h : E.1 ≤ L.1) :
    modules k E ⥤ modules k L :=
  completedOrdinaryScalarExtension l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k))

/-- Reexport the recorded additivity on the transparent scalar-extension alias.
Source: Stacks 03EK (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
instance scalarAdditive {E L : Fields l Ω} (h : E.1 ≤ L.1) : (scalar k h).Additive :=
  completedOrdinaryScalarExtension_additive l E.1 L.1
    (IntermediateField.inclusion h) (Spec (.of k))

/-- The recorded termwise extension, without completion.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev scalarC {E L : Fields l Ω} (h : E.1 ≤ L.1) :
    complexes k E ⥤ complexes k L :=
  completedOrdinaryScalarComplex l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k))

/-- The prescribed ordinary K-flat derived extension and its counit are retained.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev scalarD {E L : Fields l Ω} (h : E.1 ≤ L.1) :
    DerivedCategory (modules k E) ⥤ DerivedCategory (modules k L) :=
  completedDerivedScalarExtension l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k))

/-- Ordinary extension on modules over valuation rings.
Source: Stacks 03EK (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev tensor {E L : Fields l Ω} (h : E.1 ≤ L.1) :=
  pointFiniteFreeModuleTensor.{t, u} l E.1 L.1 (IntermediateField.inclusion h)

/-- Standard localization of the existing module category in its natural universe.
Source: Stacks 05RU (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
instance moduleDerived (R : Type r) [Ring R] :
    HasDerivedCategory (ModuleCat.{m} R) :=
  HasDerivedCategory.standard _

/-- All pairwise normalized comparisons furnished by the two dependency statements.
Their bases may differ; only their uniquely normalized section-ring maps are used.
Source: Stacks 03EK, 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
structure Comparisons where
  finite : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
    PointFiniteFreeSectionsTensorData k l E.1 L.1 (IntermediateField.inclusion h)
  derived : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
    PointDerivedSectionsTensorData.{t, u, max (u + 1) (t + 2), max (u + 1) (t + 2)}
      (finite E L h)

variable (B : Comparisons k (l := l) (Ω := Ω))

/-- Use one normalized section-ring identification for each field throughout a tower.
Source: Stacks 03CW (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev sections (E : Fields l Ω) :
    modules k E ⥤ ModuleCat.{max u (t + 1)} (integers E) :=
  pointFiniteFreeEvaluation k l E.1 (B.finite E E le_rfl).coefficientE

/-- Exactness is supplied by descent at the identity pair.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
instance sectionsAdditive (E : Fields l Ω) : (sections k B E).Additive :=
  (B.derived E E le_rfl).sectionsE_additive

/-- Exactness is supplied by descent at the identity pair.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
instance sectionsLimits (E : Fields l Ω) : PreservesFiniteLimits (sections k B E) :=
  (B.derived E E le_rfl).sectionsE_limits

/-- Exactness is supplied by descent at the identity pair.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
instance sectionsColimits (E : Fields l Ω) : PreservesFiniteColimits (sections k B E) :=
  (B.derived E E le_rfl).sectionsE_colimits

/-- Derived sections using the single normalized coefficient identification.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev sectionsD (E : Fields l Ω) :
    DerivedCategory (modules k E) ⥤
      DerivedCategory (ModuleCat.{max u (t + 1)} (integers E)) :=
  (sections k B E).mapDerivedCategory

/-- Exact-derived module extension, with exactness furnished by descent.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev tensorD {E L : Fields l Ω} (h : E.1 ≤ L.1) :
    DerivedCategory (ModuleCat.{max u (t + 1)} (integers E)) ⥤
      DerivedCategory (ModuleCat.{max u (t + 1)} (integers L)) :=
  letI := (B.derived E L h).module_limits
  letI := (B.derived E L h).module_colimits
  (tensor.{t} h).mapDerivedCategory

/-- Canonical localization comparison for module extension.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev tensorFactors {E L : Fields l Ω} (h : E.1 ≤ L.1) :=
  letI := (B.derived E L h).module_limits
  letI := (B.derived E L h).module_colimits
  (tensor.{t} h).mapDerivedCategoryFactors

/-- The sheaf tensor generator, using the published sheafification map.
Source: Stacks 03EK (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def generator {E L : Fields l Ω} (h : E.1 ≤ L.1) (F : modules k E)
    (U : (Spec (.of k)).ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l L.1 (Spec (.of k))).obj.obj U)
    (x : F.val.obj U) : ((scalar k h).obj F).val.obj U :=
  completedScalarTensorSection l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k)) F U a x

/-- The actual sheaf coefficient inclusion evaluated on a section.
Source: Stacks 03EK (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev coefficient {E L : Fields l Ω} (h : E.1 ≤ L.1)
    (U : (Spec (.of k)).ProEtᵒᵖ) :=
  (completedCoefficientMap l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k))).hom.app U

/-- The already defined inclusion of valuation rings.
Source: blueprint coefficient conventions
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev inclusion {E L : Fields l Ω} (h : E.1 ≤ L.1) :=
  integralScalarIntegerInclusion l E.1 L.1 (IntermediateField.inclusion h)

/-- A pure tensor in the actual extended module, with its target type explicit.
Source: Stacks 03EK (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev moduleGenerator {E L : Fields l Ω} (h : E.1 ≤ L.1)
    (N : ModuleCat.{max u (t + 1)} (integers E)) (a : integers L) (n : N) :
    (tensor.{t} h).obj N := a ⊗ₜ[integers E, inclusion h] n

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The natural scalar, section, associator and unit maps, at both levels.
Source: Stacks 03EK, 06YY, 0G7E, 0D6D, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
structure Maps where
  sheafComp : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1),
    scalar k (E := E) (L := L) h ⋙
      scalar k (E := L) (L := M) g ≅ scalar k (E := E) (L := M) (h.trans g)
  moduleComp : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1),
    tensor.{t} (E := E) (L := L) h ⋙
      tensor.{t} (E := L) (L := M) g ≅ tensor.{t} (E := E) (L := M) (h.trans g)
  theta : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
    sections k B E ⋙ tensor.{t} (E := E) (L := L) h ≅ scalar k (E := E) (L := L) h ⋙ sections k B L
  thetaD : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
    sectionsD k B E ⋙
      tensorD k B (E := E) (L := L) h ≅ scalarD k (E := E) (L := L) h ⋙ sectionsD k B L
  alpha : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1),
    scalarD k (E := E) (L := L) h ⋙
      scalarD k (E := L) (L := M) g ≅ scalarD k (E := E) (L := M) (h.trans g)
  alphaMod : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1),
    tensorD k B (E := E) (L := L) h ⋙
      tensorD k B (E := L) (L := M) g ≅ tensorD k B (E := E) (L := M) (h.trans g)
  sheafUnit : ∀ E : Fields l Ω, scalar k (E := E) le_rfl ≅ 𝟭 (modules k E)
  moduleUnit : ∀ E : Fields l Ω,
    tensor.{t} (E := E) le_rfl ≅ 𝟭 (ModuleCat.{max u (t + 1)} (integers E))
  unitD : ∀ E : Fields l Ω, scalarD k (E := E) le_rfl ≅ 𝟭 (DerivedCategory (modules k E))
  moduleUnitD : ∀ E : Fields l Ω,
    tensorD k B (E := E) le_rfl ≅
      𝟭 (DerivedCategory (ModuleCat.{max u (t + 1)} (integers E)))

/-- The sheaf formula clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsSheafFormulaStatement (C : Maps k B) : Prop :=
  ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (F : modules k E) (U : (Spec (.of k)).ProEtᵒᵖ)
  (a : (completedIntegralCommRingSheafUnrestricted l L.1 (Spec (.of k))).obj.obj U)
  (b : (completedIntegralCommRingSheafUnrestricted l M.1 (Spec (.of k))).obj.obj U)
  (x : F.val.obj U),
  ((C.sheafComp E L M h g).hom.app F).val.app U
    (generator k (E := L) (L := M) g
      ((scalar k (E := E) (L := L) h).obj F) U b
      (generator k (E := E) (L := L) h F U a x)) =
      generator k (E := E) (L := M) (h.trans g) F U
        (coefficient k (E := L) (L := M) g U a * b) x

/-- The sheaf inverse clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsSheafInverseStatement (C : Maps k B) : Prop :=
  ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (F : modules k E) (U : (Spec (.of k)).ProEtᵒᵖ)
  (b : (completedIntegralCommRingSheafUnrestricted l M.1 (Spec (.of k))).obj.obj U)
  (x : F.val.obj U),
  ((C.sheafComp E L M h g).inv.app F).val.app U
    (generator k (E := E) (L := M) (h.trans g) F U b x) =
      generator k (E := L) (L := M) g
        ((scalar k (E := E) (L := L) h).obj F) U b
        (generator k (E := E) (L := L) h F U 1 x)

/-- The module formula clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsModuleFormulaStatement (C : Maps k B) : Prop :=
  ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (N : ModuleCat.{max u (t + 1)} (integers E)) (a : integers L) (b : integers M) (n : N),
  (C.moduleComp E L M h g).hom.app N
    (moduleGenerator.{t} (E := L) (L := M) g
      ((tensor.{t} (E := E) (L := L) h).obj N) b
      (moduleGenerator.{t} (E := E) (L := L) h N a n)) =
      moduleGenerator.{t} (E := E) (L := M) (h.trans g) N (inclusion (E := L) (L := M) g a * b) n

/-- The module inverse clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsModuleInverseStatement (C : Maps k B) : Prop :=
  ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (N : ModuleCat.{max u (t + 1)} (integers E)) (b : integers M) (n : N),
  (C.moduleComp E L M h g).inv.app N (moduleGenerator.{t} (E := E) (L := M) (h.trans g) N b n) =
    moduleGenerator.{t} (E := L) (L := M) g
      ((tensor.{t} (E := E) (L := L) h).obj N) b
      (moduleGenerator.{t} (E := E) (L := L) h N 1 n)

/-- The theta normalized clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsThetaNormalizedStatement (C : Maps k B) : Prop :=
  ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
  HEq (C.theta E L h) (B.finite E L h).comparison

/-- The square clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsSquareStatement (C : Maps k B) : Prop :=
  ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1) (F : modules k E),
  (tensor.{t} (E := L) (L := M) g).map ((C.theta E L h).hom.app F) ≫
    (C.theta L M g).hom.app ((scalar k (E := E) (L := L) h).obj F) ≫
    (sections k B M).map ((C.sheafComp E L M h g).hom.app F) =
  (C.moduleComp E L M h g).hom.app ((sections k B E).obj F) ≫
    (C.theta E M (h.trans g)).hom.app F

/-- The sheaf unit formula clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsSheafUnitFormulaStatement (C : Maps k B) : Prop :=
  ∀ (E : Fields l Ω) (F : modules k E) (U : (Spec (.of k)).ProEtᵒᵖ)
  (a : (completedIntegralCommRingSheafUnrestricted l E.1 (Spec (.of k))).obj.obj U)
  (x : F.val.obj U),
  ((C.sheafUnit E).hom.app F).val.app U (generator k (E := E) (L := E) le_rfl F U a x) =
    @SMul.smul _ _ (F.val.obj U).isModule.toSMul a x

/-- The module unit formula clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsModuleUnitFormulaStatement (C : Maps k B) : Prop :=
  ∀ (E : Fields l Ω)
  (N : ModuleCat.{max u (t + 1)} (integers E)) (a : integers E) (n : N),
  (C.moduleUnit E).hom.app N (moduleGenerator.{t} (E := E) (L := E) le_rfl N a n) = a • n

/-- The unit square clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsUnitSquareStatement (C : Maps k B) : Prop :=
  ∀ (E : Fields l Ω) (F : modules k E),
  (C.theta E E le_rfl).hom.app F ≫ (sections k B E).map ((C.sheafUnit E).hom.app F) =
    (C.moduleUnit E).hom.app ((sections k B E).obj F)

/-- The sheaf tower clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsSheafTowerStatement (C : Maps k B) : Prop :=
  ∀ (E L M H : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (j : M.1 ≤ H.1) (F : modules k E),
  (scalar k (E := M) (L := H) j).map ((C.sheafComp E L M h g).hom.app F) ≫
    (C.sheafComp E M H (h.trans g) j).hom.app F =
  (C.sheafComp L M H g j).hom.app ((scalar k (E := E) (L := L) h).obj F) ≫
    (C.sheafComp E L H h (g.trans j)).hom.app F

/-- The module tower clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def OrdinaryLawsModuleTowerStatement (C : Maps k B) : Prop :=
  ∀ (E L M H : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (j : M.1 ≤ H.1) (N : ModuleCat.{max u (t + 1)} (integers E)),
  (tensor.{t} (E := M) (L := H) j).map ((C.moduleComp E L M h g).hom.app N) ≫
    (C.moduleComp E M H (h.trans g) j).hom.app N =
  (C.moduleComp L M H g j).hom.app ((tensor.{t} (E := E) (L := L) h).obj N) ≫
    (C.moduleComp E L H h (g.trans j)).hom.app N

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The balanced formulas and ordinary section, unit and four-field equations.
Source: Stacks 03EK, 06YY, 0G7E, 0D6D, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
structure OrdinaryLaws (C : Maps k B) : Prop where
  sheaf_formula : OrdinaryLawsSheafFormulaStatement k B C
  sheaf_inverse : OrdinaryLawsSheafInverseStatement k B C
  module_formula : OrdinaryLawsModuleFormulaStatement k B C
  module_inverse : OrdinaryLawsModuleInverseStatement k B C
  theta_normalized : OrdinaryLawsThetaNormalizedStatement k B C
  square : OrdinaryLawsSquareStatement k B C
  sheaf_unit_formula : OrdinaryLawsSheafUnitFormulaStatement k B C
  module_unit_formula : OrdinaryLawsModuleUnitFormulaStatement k B C
  unit_square : OrdinaryLawsUnitSquareStatement k B C
  sheaf_tower : OrdinaryLawsSheafTowerStatement k B C
  module_tower : OrdinaryLawsModuleTowerStatement k B C

/-- The thetaD normalized clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def DerivedLawsThetadNormalizedStatement (Z : Maps k B) : Prop :=
  ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
  HEq (Z.thetaD E L h) (B.derived E L h).theta

/-- The representative clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def DerivedLawsRepresentativeStatement (Z : Maps k B) : Prop :=
  ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (C : complexes k E),
  (scalarD k (E := L) (L := M) g).map
      (completedScalarCounit l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k)) C) ≫
    completedScalarCounit l L.1 M.1 (IntermediateField.inclusion g) (Spec (.of k))
      ((scalarC k (E := E) (L := L) h).obj C) ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (Z.sheafComp E L M h g) (.up ℤ)).hom.app C) =
  (Z.alpha E L M h g).hom.app (DerivedCategory.Q.obj C) ≫
    completedScalarCounit l E.1 M.1 (IntermediateField.inclusion (h.trans g))
      (Spec (.of k)) C

/-- The module representative clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def DerivedLawsModuleRepresentativeStatement (Z : Maps k B) : Prop :=
  ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (C : CochainComplex (ModuleCat.{max u (t + 1)} (integers E)) ℤ),
  (Z.alphaMod E L M h g).hom.app (DerivedCategory.Q.obj C) ≫
    (tensorFactors k B (E := E) (L := M) (h.trans g)).hom.app C =
  (tensorD k B (E := L) (L := M) g).map ((tensorFactors k B (E := E) (L := L) h).hom.app C) ≫
    (tensorFactors k B (E := L) (L := M) g).hom.app
      (((tensor.{t} (E := E) (L := L) h).mapHomologicalComplex (.up ℤ)).obj C) ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (Z.moduleComp E L M h g) (.up ℤ)).hom.app C)

/-- The derived square clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def DerivedLawsDerivedSquareStatement (Z : Maps k B) : Prop :=
  ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (K : DerivedCategory (modules k E)),
  (tensorD k B (E := L) (L := M) g).map ((Z.thetaD E L h).hom.app K) ≫
    (Z.thetaD L M g).hom.app ((scalarD k (E := E) (L := L) h).obj K) ≫
    (sectionsD k B M).map ((Z.alpha E L M h g).hom.app K) =
  (Z.alphaMod E L M h g).hom.app ((sectionsD k B E).obj K) ≫
    (Z.thetaD E M (h.trans g)).hom.app K

/-- The unit representative clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def DerivedLawsUnitRepresentativeStatement (Z : Maps k B) : Prop :=
  ∀ (E : Fields l Ω) (C : complexes k E),
  (Z.unitD E).hom.app (DerivedCategory.Q.obj C) =
    completedScalarCounit l E.1 E.1 (IntermediateField.inclusion le_rfl) (Spec (.of k)) C ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (Z.sheafUnit E) (.up ℤ)).hom.app C)

/-- The module unit representative clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def DerivedLawsModuleUnitRepresentativeStatement (Z : Maps k B) : Prop :=
  ∀ (E : Fields l Ω)
  (C : CochainComplex (ModuleCat.{max u (t + 1)} (integers E)) ℤ),
  (Z.moduleUnitD E).hom.app (DerivedCategory.Q.obj C) =
    (tensorFactors k B (E := E) le_rfl).hom.app C ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (Z.moduleUnit E) (.up ℤ)).hom.app C)

/-- The derived unit square clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def DerivedLawsDerivedUnitSquareStatement (Z : Maps k B) : Prop :=
  ∀ (E : Fields l Ω) (K : DerivedCategory (modules k E)),
  (Z.thetaD E E le_rfl).hom.app K ≫ (sectionsD k B E).map ((Z.unitD E).hom.app K) =
    (Z.moduleUnitD E).hom.app ((sectionsD k B E).obj K)

/-- The derived tower clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def DerivedLawsDerivedTowerStatement (Z : Maps k B) : Prop :=
  ∀ (E L M H : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (j : M.1 ≤ H.1) (K : DerivedCategory (modules k E)),
  (scalarD k (E := M) (L := H) j).map ((Z.alpha E L M h g).hom.app K) ≫
    (Z.alpha E M H (h.trans g) j).hom.app K =
  (Z.alpha L M H g j).hom.app ((scalarD k (E := E) (L := L) h).obj K) ≫
    (Z.alpha E L H h (g.trans j)).hom.app K

/-- The derived module tower clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def DerivedLawsDerivedModuleTowerStatement (Z : Maps k B) : Prop :=
  ∀ (E L M H : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (j : M.1 ≤ H.1) (K : DerivedCategory (ModuleCat.{max u (t + 1)} (integers E))),
  (tensorD k B (E := M) (L := H) j).map ((Z.alphaMod E L M h g).hom.app K) ≫
    (Z.alphaMod E M H (h.trans g) j).hom.app K =
  (Z.alphaMod L M H g j).hom.app ((tensorD k B (E := E) (L := L) h).obj K) ≫
    (Z.alphaMod E L H h (g.trans j)).hom.app K

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Normalized descent, representative equations and all derived coherence laws.
Source: Stacks 03EK, 06YY, 0G7E, 0D6D, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
structure DerivedLaws (Z : Maps k B) : Prop where
  thetaD_normalized : DerivedLawsThetadNormalizedStatement k B Z
  representative : DerivedLawsRepresentativeStatement k B Z
  module_representative : DerivedLawsModuleRepresentativeStatement k B Z
  derived_square : DerivedLawsDerivedSquareStatement k B Z
  unit_representative : DerivedLawsUnitRepresentativeStatement k B Z
  module_unit_representative : DerivedLawsModuleUnitRepresentativeStatement k B Z
  derived_unit_square : DerivedLawsDerivedUnitSquareStatement k B Z
  derived_tower : DerivedLawsDerivedTowerStatement k B Z
  derived_module_tower : DerivedLawsDerivedModuleTowerStatement k B Z

/-- The square clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def ChainLawsSquareStatement (Z : Maps k B) : Prop :=
  ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
  (P : complexes k E) (i : ℤ),
  (tensor.{t} (E := L) (L := M) g).map ((Z.theta E L h).hom.app (P.X i)) ≫
    (Z.theta L M g).hom.app ((scalar k (E := E) (L := L) h).obj (P.X i)) ≫
    (sections k B M).map ((Z.sheafComp E L M h g).hom.app (P.X i)) =
  (Z.moduleComp E L M h g).hom.app ((sections k B E).obj (P.X i)) ≫
    (Z.theta E M (h.trans g)).hom.app (P.X i)

/-- The unit clause, named to share its type.
Source: Stacks 03EK, 06YY, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def ChainLawsUnitStatement (Z : Maps k B) : Prop :=
  ∀ (E : Fields l Ω) (P : complexes k E) (i : ℤ),
  (Z.theta E E le_rfl).hom.app (P.X i) ≫
    (sections k B E).map ((Z.sheafUnit E).hom.app (P.X i)) =
  (Z.moduleUnit E).hom.app ((sections k B E).obj (P.X i))

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Cochain square and unit equations in every degree. Every component is obtained
termwise from a natural transformation, so it commutes with differentials; equality
of cochain maps is exactly equality of these components for every integer degree.
Source: Stacks 03EK and 06YY
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
structure ChainLaws (Z : Maps k B) : Prop where
  square : ChainLawsSquareStatement k B Z
  unit : ChainLawsUnitStatement k B Z

/-- Flat-term K-flat models remain valid after ordinary extension.
Source: Stacks 03EK, 06YY, 0G7E, 0D6D, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
def PreservesModels : Prop :=
  ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1) (P : complexes k E),
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E.1 (Spec (.of k))) P →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology (Spec (.of k)))
      (R := completedIntegralCommRingSheafUnrestricted l E.1 (Spec (.of k))) (P.X i)) →
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l L.1 (Spec (.of k)))
      ((scalarC k (E := E) (L := L) h).obj P) ∧
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology (Spec (.of k)))
      (R := completedIntegralCommRingSheafUnrestricted l L.1 (Spec (.of k)))
      (((scalarC k (E := E) (L := L) h).obj P).X i)) ∧
    IsIso (completedScalarCounit l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k)) P)

end WeilConjectures.PointTensorTower

namespace WeilConjectures


attribute [local irreducible] completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarTensorSection completedCoefficientMap Padic Padic.coefficientExtensionIntegers
  integralScalarIntegerInclusion completedScalarRelativeDegree
attribute [local instance 20000] Algebra.toModule IntermediateField.algebra'

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom
  CategoryTheory.Limits.limit

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- These conversions use the same direct assignment as scalar_exact_comparison in
-- PointDerivedSectionsTensorDescent; the kernel checks the resulting proof term.
local elab "kernel_exact " h:ident : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let some hp := (← Lean.getLCtx).findFromUserName? h.getId
      | throwError "missing proved conversion term"
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar hp.fvarId)
  Lean.Elab.Tactic.replaceMainGoal []

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tower_comparisons_nonempty
    (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    Nonempty (PointTensorTower.Comparisons D.k (l := l) (Ω := Ω)) := by
  classical
  let finite (E L : PointTensorTower.Fields l Ω) (h : E.1 ≤ L.1) :=
    (point_finite_free_sections_tensor D l hl Ω E.1 L.1 h).some
  exact ⟨{ finite := finite
           derived := fun E L h ↦
             (point_derived_sections_tensor_descent D l hl Ω E.1 L.1 h (finite E L h)).some }⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tower_coefficient_comp
    {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] [Algebra ℚ_[l] Ω]
    (k : Type t) [Field k] (E L M : PointTensorTower.Fields l Ω)
    (h : E.1 ≤ L.1) (g : L.1 ≤ M.1) :
    completedCoefficientMap l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k)) ≫
      completedCoefficientMap l L.1 M.1 (IntermediateField.inclusion g) (Spec (.of k)) =
    completedCoefficientMap l E.1 M.1 (IntermediateField.inclusion (h.trans g))
      (Spec (.of k)) := by
  apply (completedCoefficientMap_existsUnique l E.1 M.1
    (IntermediateField.inclusion (h.trans g)) (Spec (.of k))).unique
  · intro n
    rw [Category.assoc, completedCoefficientMap_projection,
      ← Category.assoc, completedCoefficientMap_projection, Category.assoc]
    congr 1
    unfold integralScalarQuotientSheafMap
    dsimp only [integralCoefficientCommRingSheaf]
    rw [← Functor.map_comp]
    congr 1
    ext x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn
    unfold integralScalarQuotientMap integralScalarIntegerInclusion
    rfl
  · intro n
    exact completedCoefficientMap_projection l E.1 M.1
      (IntermediateField.inclusion (h.trans g)) (Spec (.of k)) n

namespace PointTensorTower


variable {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] [Algebra ℚ_[l] Ω]
  (k : Type t) [Field k]


private theorem coefficientE_eq (B : Comparisons k (l := l) (Ω := Ω))
    (E L : Fields l Ω) (h : E.1 ≤ L.1) :
    (B.finite E L h).coefficientE = (B.finite E E le_rfl).coefficientE := by
  ext a
  exact ((B.finite E L h).constantE a).trans ((B.finite E E le_rfl).constantE a).symm

private theorem coefficientL_eq (B : Comparisons k (l := l) (Ω := Ω))
    (E L : Fields l Ω) (h : E.1 ≤ L.1) :
    (B.finite E L h).coefficientL = (B.finite L L le_rfl).coefficientE := by
  ext a
  exact ((B.finite E L h).constantL a).trans ((B.finite L L le_rfl).constantE a).symm

private theorem theta_exists (B : Comparisons k (l := l) (Ω := Ω))
    (E L : Fields l Ω) (h : E.1 ≤ L.1) :
    ∃ θ : sections k B E ⋙ tensor.{t} h ≅ scalar k h ⋙ sections k B L,
      HEq θ (B.finite E L h).comparison := by
  apply CategoryTheory.ScalarTower.comparison_exists_heq
    (pointFiniteFreeEvaluation k l E.1 (B.finite E L h).coefficientE) (sections k B E)
    (pointFiniteFreeEvaluation k l L.1 (B.finite E L h).coefficientL) (sections k B L)
    (scalar k h) (tensor.{t} h) _ _ (B.finite E L h).comparison
  · exact congrArg (pointFiniteFreeEvaluation k l E.1) (coefficientE_eq k B E L h).symm
  · exact congrArg (pointFiniteFreeEvaluation k l L.1) (coefficientL_eq k B E L h).symm


private theorem normalized_theta_formula
    (E L : Fields l Ω) (h : E.1 ≤ L.1)
    (ce ce' : integers E ≃+*
      (completedIntegralCoefficientSheafUnrestricted l E.1 (Spec (.of k))).obj.obj
        (pointFiniteFreeFinal k))
    (cl cl' : integers L ≃+*
      (completedIntegralCoefficientSheafUnrestricted l L.1 (Spec (.of k))).obj.obj
        (pointFiniteFreeFinal k))
    (he : ce = ce') (hl : cl = cl')
    (θ : pointFiniteFreeEvaluation k l E.1 ce ⋙ tensor.{t} h ≅
      scalar k h ⋙ pointFiniteFreeEvaluation k l L.1 cl)
    (θ' : pointFiniteFreeEvaluation k l E.1 ce' ⋙ tensor.{t} h ≅
      scalar k h ⋙ pointFiniteFreeEvaluation k l L.1 cl') (hh : HEq θ' θ)
    (hn : ∀ F a (n : (pointFiniteFreeEvaluation k l E.1 ce).obj F),
      θ.hom.app F (moduleGenerator.{t} h _ a n) =
        generator k h F (pointFiniteFreeFinal k) (cl a) n) :
    ∀ F a (n : (pointFiniteFreeEvaluation k l E.1 ce').obj F),
      θ'.hom.app F (moduleGenerator.{t} h _ a n) =
        generator k h F (pointFiniteFreeFinal k) (cl' a) n := by
  subst ce'
  subst cl'
  cases hh
  exact hn


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generator_pure (E L : Fields l Ω) (h : E.1 ≤ L.1) (F : modules k E) U a x :
      CategoryTheory.SectionsScalarOrdinaryTower.pure
        (completedCoefficientMap l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k)))
        (scalar k h)
        (completedOrdinaryScalarExtension_obj l E.1 L.1
          (IntermediateField.inclusion h) (Spec (.of k))) F U a x = generator k h F U a x := by
  have hx := Eq.refl (generator k h F U a x)
  unfold generator completedScalarTensorSection at hx
  kernel_exact hx


attribute [local irreducible] generator CategoryTheory.SectionsScalarOrdinaryTower.pure

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinary_tower (B : Comparisons k (l := l) (Ω := Ω))
    (θ : ∀ E L h, sections k B E ⋙ tensor.{t} h ≅ scalar k h ⋙ sections k B L)
    (hθ : ∀ E L h, HEq (θ E L h) (B.finite E L h).comparison) :
    ∃! O : CategoryTheory.ScalarTower.OrdinaryMaps
      (modules k) (fun E : Fields l Ω ↦ ModuleCat.{max u (t + 1)} (integers E))
      (fun (E L : Fields l Ω) (h : E.1 ≤ L.1) ↦ scalar k h)
      (fun (E L : Fields l Ω) (h : E.1 ≤ L.1) ↦ tensor.{t} h),
      CategoryTheory.SectionsScalarOrdinaryTower.Formula.{u, u, t + 1, t + 1, t}
        (fun E : Fields l Ω ↦ completedIntegralCommRingSheafUnrestricted l E.1 (Spec (.of k)))
        (fun E : Fields l Ω ↦ CommRingCat.of (integers E))
        (fun (E L : Fields l Ω) (h : E.1 ≤ L.1) ↦ completedCoefficientMap l E.1 L.1
          (IntermediateField.inclusion h)
          (Spec (.of k)))
        (fun (E L : Fields l Ω) (h : E.1 ≤ L.1) ↦ CommRingCat.ofHom (inclusion h))
        (fun (E L : Fields l Ω) (h : E.1 ≤ L.1) ↦ scalar k h)
        (fun (E L : Fields l Ω) (h : E.1 ≤ L.1) ↦ completedOrdinaryScalarExtension_obj l E.1 L.1
          (IntermediateField.inclusion h) (Spec (.of k))) O ∧
      CategoryTheory.ScalarTower.Coherent (sections k B) θ O := by
  let R (E : Fields l Ω) :=
    completedIntegralCommRingSheafUnrestricted l E.1 (Spec (.of k))
  let A (E : Fields l Ω) := CommRingCat.of (integers E)
  let f (E L : Fields l Ω) (h : E.1 ≤ L.1) :=
    completedCoefficientMap l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k))
  let a (E L : Fields l Ω) (h : E.1 ≤ L.1) := CommRingCat.ofHom (inclusion h)
  apply CategoryTheory.SectionsScalarOrdinaryTower.coherence.{u, u, t + 1, t + 1, t}
    (Scheme.ProEt.mk (𝟙 (Spec (.of k)))) R A f a
    (fun (E L : Fields l Ω) (h : E.1 ≤ L.1) ↦ scalar k h)
    (fun (E L : Fields l Ω) (h : E.1 ≤ L.1) ↦ completedOrdinaryScalarExtension_obj l E.1 L.1
          (IntermediateField.inclusion h) (Spec (.of k)))
    (fun E : Fields l Ω ↦ (B.finite E E le_rfl).coefficientE.toRingHom) θ
  · exact Scheme.ProEt.isTerminalMkId _
  · intro E
    have hi : IntermediateField.inclusion (show E.1 ≤ E.1 from le_rfl) =
        AlgHom.id ℚ_[l] E.1 := IntermediateField.inclusion_self
    dsimp only [f]
    rw [hi]
    exact completedCoefficientMap_id l E.1 (Spec (.of k))
  · intro E L M h g
    exact tower_coefficient_comp k E L M h g
  · intro E
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    dsimp only [a]
    unfold inclusion integralScalarIntegerInclusion
    rfl
  · intro E L M h g
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    dsimp only [a]
    unfold inclusion integralScalarIntegerInclusion
    rfl
  · intro E L h F N v
    dsimp only [f]
    change (completedOrdinaryScalarExtension l E.1 L.1
      (IntermediateField.inclusion h) (Spec (.of k))).map v = _
    exact completedOrdinaryScalarExtension_map l E.1 L.1
      (IntermediateField.inclusion h) (Spec (.of k)) v
  · intro E L h
    apply RingHom.ext
    intro x
    have hx := (B.finite E L h).coefficient_compatibility x
    have he := congrArg (fun e ↦ e x) (coefficientE_eq k B E L h)
    have hl := congrArg (fun e ↦ e (inclusion h x)) (coefficientL_eq k B E L h)
    exact (congrArg (fun v ↦ ((f E L h).hom.app (pointFiniteFreeFinal k)) v)
      he.symm).trans (hx.trans hl)
  · intro E L h F b n
    have hcomparison := (B.finite E L h).comparison_tensor
    have hn := normalized_theta_formula k E L h
      (B.finite E L h).coefficientE (B.finite E E le_rfl).coefficientE
      (B.finite E L h).coefficientL (B.finite L L le_rfl).coefficientE
      (coefficientE_eq k B E L h) (coefficientL_eq k B E L h)
      (B.finite E L h).comparison (θ E L h) (hθ E L h)
      (by kernel_exact hcomparison) F b n
    have hnormalized := hn.trans (generator_pure k E L h F (pointFiniteFreeFinal k)
      ((B.finite L L le_rfl).coefficientE b) n).symm
    -- The endpoints use two definitionally equal ring presentations. Let the kernel
    -- check this conversion, as in PointDerivedSectionsTensorDescent.scalar_exact_comparison.
    kernel_exact hnormalized



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localized_eq
    {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    {ι : E →ₐ[ℚ_[l]] L}
    (d : PointFiniteFreeSectionsTensorData k l E L ι)
    (b : PointDerivedSectionsTensorData.{t, u, max (u + 1) (t + 2),
      max (u + 1) (t + 2)} d) :
    letI := d.sheaf_additive
    letI : (pointFiniteFreeEvaluation k l E d.coefficientE).Additive :=
      b.sectionsE_additive
    letI : (pointFiniteFreeEvaluation k l L d.coefficientL).Additive :=
      b.sectionsL_additive
    letI := b.sectionsE_limits
    letI := b.sectionsE_colimits
    letI := b.sectionsL_limits
    letI := b.sectionsL_colimits
    letI := b.sheaf_limits
    letI := b.sheaf_colimits
    letI := b.module_limits
    letI := b.module_colimits
    letI : (pointFiniteFreeModuleTensor.{t, u} l E L ι).Additive :=
      d.module_additive
    Functor.mapDerivedCategoryNatIso (F := PointDerivedSectionsTensor.A d)
      (G := PointDerivedSectionsTensor.B d) d.comparison = b.localized := by
  have := d.sheaf_additive
  have : (pointFiniteFreeEvaluation k l E d.coefficientE).Additive :=
    b.sectionsE_additive
  have : (pointFiniteFreeEvaluation k l L d.coefficientL).Additive :=
    b.sectionsL_additive
  have := b.sectionsE_limits
  have := b.sectionsE_colimits
  have := b.sectionsL_limits
  have := b.sectionsL_colimits
  have := b.sheaf_limits
  have := b.sheaf_colimits
  have := b.module_limits
  have := b.module_colimits
  have : (pointFiniteFreeModuleTensor.{t, u} l E L ι).Additive := d.module_additive
  exact CategoryTheory.ScalarTower.localizedComparison_eq
    (PointDerivedSectionsTensor.A d) (PointDerivedSectionsTensor.B d)
    d.comparison d.complexes d.complexes_hom b.localized b.localized_representative


private theorem scalarLimits (B : Comparisons k (l := l) (Ω := Ω))
    (E L : Fields l Ω) (h : E.1 ≤ L.1) : PreservesFiniteLimits (scalar k h) :=
  (B.derived E L h).sheaf_limits

private theorem scalarColimits (B : Comparisons k (l := l) (Ω := Ω))
    (E L : Fields l Ω) (h : E.1 ≤ L.1) : PreservesFiniteColimits (scalar k h) :=
  (B.derived E L h).sheaf_colimits

private theorem tensorLimits (B : Comparisons k (l := l) (Ω := Ω))
    (E L : Fields l Ω) (h : E.1 ≤ L.1) : PreservesFiniteLimits (tensor.{t} h) :=
  (B.derived E L h).module_limits

private theorem tensorColimits (B : Comparisons k (l := l) (Ω := Ω))
    (E L : Fields l Ω) (h : E.1 ≤ L.1) : PreservesFiniteColimits (tensor.{t} h) :=
  (B.derived E L h).module_colimits

private abbrev ordinaryData := CategoryTheory.ScalarTower.OrdinaryMaps
  (modules k) (fun E : Fields l Ω ↦ ModuleCat.{max u (t + 1)} (integers E))
  (fun E L h ↦ scalar k (E := E) (L := L) h) (fun E L h ↦ tensor.{t} (E := E) (L := L) h)

private abbrev derivedData (B : Comparisons k (l := l) (Ω := Ω)) :=
  CategoryTheory.ScalarTower.OrdinaryMaps
    (fun E : Fields l Ω ↦ DerivedCategory (modules k E))
    (fun E : Fields l Ω ↦ DerivedCategory (ModuleCat.{max u (t + 1)} (integers E)))
    (fun E L h ↦ scalarD k (E := E) (L := L) h) (fun E L h ↦ tensorD k B h)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def canonicalThetaD (B : Comparisons k (l := l) (Ω := Ω))
    (θ : ∀ E L h, sections k B E ⋙ tensor.{t} h ≅ scalar k h ⋙ sections k B L)
    (E L : Fields l Ω) (h : E.1 ≤ L.1) :
    sectionsD k B E ⋙ tensorD k B h ≅ scalarD k h ⋙ sectionsD k B L := by
  have := scalarAdditive (l := l) (Ω := Ω) k (E := E) (L := L) h
  have := sectionsAdditive k B E
  have := sectionsAdditive k B L
  have := sectionsLimits k B E
  have := sectionsColimits k B E
  have := sectionsLimits k B L
  have := sectionsColimits k B L
  have : PreservesFiniteLimits (scalar k h) := scalarLimits k B E L h
  have : PreservesFiniteColimits (scalar k h) := scalarColimits k B E L h
  have : PreservesFiniteLimits (tensor.{t} h) := tensorLimits k B E L h
  have : PreservesFiniteColimits (tensor.{t} h) := tensorColimits k B E L h
  exact (Functor.mapDerivedCategoryCompIso (sections k B E) (tensor.{t} h)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (θ E L h) ≪≫
    Functor.mapDerivedCategoryCompIso (scalar k h) (sections k B L) ≪≫
    Functor.isoWhiskerRight (B.derived E L h).comparison (sectionsD k B L)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem canonicalThetaD_normalized (B : Comparisons k (l := l) (Ω := Ω))
    (θ : ∀ E L h, sections k B E ⋙ tensor.{t} h ≅ scalar k h ⋙ sections k B L)
    (hθ : ∀ E L h, HEq (θ E L h) (B.finite E L h).comparison)
    (E L : Fields l Ω) (h : E.1 ≤ L.1) :
    HEq (canonicalThetaD k B θ E L h) (B.derived E L h).theta := by
  have := scalarAdditive (l := l) (Ω := Ω) k (E := E) (L := L) h
  have := sectionsAdditive k B E
  have := sectionsAdditive k B L
  have := sectionsLimits k B E
  have := sectionsColimits k B E
  have := sectionsLimits k B L
  have := sectionsColimits k B L
  have : PreservesFiniteLimits (scalar k h) := scalarLimits k B E L h
  have : PreservesFiniteColimits (scalar k h) := scalarColimits k B E L h
  have : PreservesFiniteLimits (tensor.{t} h) := tensorLimits k B E L h
  have : PreservesFiniteColimits (tensor.{t} h) := tensorColimits k B E L h
  have := (B.derived E L h).sectionsE_additive
  have := (B.derived E L h).sectionsL_additive
  have := (B.derived E L h).sectionsE_limits
  have := (B.derived E L h).sectionsE_colimits
  have := (B.derived E L h).sectionsL_limits
  have := (B.derived E L h).sectionsL_colimits
  have he : sections k B E = PointDerivedSectionsTensor.sectionsE (B.finite E L h) := by
    unfold sections PointDerivedSectionsTensor.sectionsE
    rw [coefficientE_eq k B E L h]
  have hl : sections k B L = PointDerivedSectionsTensor.sectionsL (B.finite E L h) := by
    unfold sections PointDerivedSectionsTensor.sectionsL
    rw [coefficientL_eq k B E L h]
  have hloc := localized_eq k (B.finite E L h) (B.derived E L h)
  have htheta := (B.derived E L h).theta_eq
  have hn := CategoryTheory.ScalarTower.normalizedComparison_localized_heq
    (C₁ := modules k E) (C₂ := modules k L)
    (N₁ := ModuleCat.{max u (t + 1)} (integers E))
    (N₂ := ModuleCat.{max u (t + 1)} (integers L))
    (PointDerivedSectionsTensor.sectionsE (B.finite E L h)) (sections k B E)
    (PointDerivedSectionsTensor.sectionsL (B.finite E L h)) (sections k B L)
    (scalar k (E := E) (L := L) h) (tensor.{t} (E := E) (L := L) h)
    (scalarD k (E := E) (L := L) h)
    (B.derived E L h).comparison
    he hl (B.finite E L h).comparison (θ E L h) (hθ E L h)
    (B.derived E L h).localized (B.derived E L h).theta
    (by kernel_exact hloc) (by kernel_exact htheta)
  kernel_exact hn


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def mapsOfData (B : Comparisons k (l := l) (Ω := Ω))
    (θ : ∀ E L h, sections k B E ⋙ tensor.{t} h ≅ scalar k h ⋙ sections k B L)
    (O : ordinaryData (l := l) (Ω := Ω) k) (A : derivedData k B) : Maps k B where
  sheafComp := fun E L M h g ↦ O.sheafComp E L M h g
  moduleComp := fun E L M h g ↦ O.moduleComp E L M h g
  theta := θ
  thetaD := canonicalThetaD k B θ
  alpha := fun E L M h g ↦ A.sheafComp E L M h g
  alphaMod := fun E L M h g ↦ A.moduleComp E L M h g
  sheafUnit := fun E ↦ O.sheafUnit E
  moduleUnit := fun E ↦ O.moduleUnit E
  unitD := fun E ↦ A.sheafUnit E
  moduleUnitD := fun E ↦ A.moduleUnit E


private theorem maps_ext (B : Comparisons k (l := l) (Ω := Ω)) (Z W : Maps k B)
    (hsc : Z.sheafComp = W.sheafComp) (hmc : Z.moduleComp = W.moduleComp)
    (ht : Z.theta = W.theta) (htd : Z.thetaD = W.thetaD)
    (ha : Z.alpha = W.alpha) (ham : Z.alphaMod = W.alphaMod)
    (hsu : Z.sheafUnit = W.sheafUnit) (hmu : Z.moduleUnit = W.moduleUnit)
    (hud : Z.unitD = W.unitD) (hmd : Z.moduleUnitD = W.moduleUnitD) : Z = W := by
  cases Z
  cases W
  cases hsc
  cases hmc
  cases ht
  cases htd
  cases ha
  cases ham
  cases hsu
  cases hmu
  cases hud
  cases hmd
  rfl


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinaryLaws_of_data (B : Comparisons k (l := l) (Ω := Ω))
    (θ : ∀ E L h, sections k B E ⋙ tensor.{t} h ≅ scalar k h ⋙ sections k B L)
    (hθ : ∀ E L h, HEq (θ E L h) (B.finite E L h).comparison)
    (O : ordinaryData (l := l) (Ω := Ω) k) (A : derivedData k B)
    (hF : CategoryTheory.SectionsScalarOrdinaryTower.Formula.{u, u, t + 1, t + 1, t}
      (fun E : Fields l Ω ↦ completedIntegralCommRingSheafUnrestricted l E.1 (Spec (.of k)))
      (fun E : Fields l Ω ↦ CommRingCat.of (integers E))
      (fun E L h ↦ completedCoefficientMap l E.1 L.1
        (IntermediateField.inclusion h) (Spec (.of k)))
      (fun E L h ↦ CommRingCat.ofHom (inclusion h))
      (fun E L h ↦ scalar k (E := E) (L := L) h)
      (fun E L h ↦ completedOrdinaryScalarExtension_obj l E.1 L.1
          (IntermediateField.inclusion h) (Spec (.of k))) O)
    (hO : CategoryTheory.ScalarTower.Coherent (sections k B) θ O) :
    OrdinaryLaws k B (mapsOfData k B θ O A) := by
  constructor
  · have hx := hF.sheaf_formula
    kernel_exact hx
  · have hx := hF.sheaf_inverse
    kernel_exact hx
  · have hx := hF.module_formula
    kernel_exact hx
  · have hx := hF.module_inverse
    kernel_exact hx
  · kernel_exact hθ
  · have hx := hO.square
    kernel_exact hx
  · have hx := hF.sheaf_unit_formula
    kernel_exact hx
  · have hx := hF.module_unit_formula
    kernel_exact hx
  · have hx := hO.unit
    kernel_exact hx
  · have hx := hO.sheaf_tower
    kernel_exact hx
  · have hx := hO.module_tower
    kernel_exact hx

attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.IsFlatOnSite SheafOfModules.monoidalCategory
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem preserves_models (B : Comparisons k (l := l) (Ω := Ω)) :
    PreservesModels k (l := l) (Ω := Ω) := by
  intro E L h P hk hf
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E.1 (Spec (.of k)))
  letI := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l L.1 (Spec (.of k)))
  have hflat0 (i : ℤ) := hf i
  unfold SheafOfModules.IsFlatOnSite at hflat0
  let φ := completedCoefficientMap l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k))
  have hflat (i : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory
          (completedIntegralCommRingSheafUnrestricted l E.1 (Spec (.of k)))) (P.X i)) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E.1 (Spec (.of k))) (P.X i)) (hflat0 i)
  have hchange := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (R := completedIntegralCommRingSheafUnrestricted l E.1 (Spec (.of k)))
    (S := completedIntegralCommRingSheafUnrestricted l L.1 (Spec (.of k)))
    φ P (scalar k h)
    (completedOrdinaryScalarExtension_obj l E.1 L.1
          (IntermediateField.inclusion h) (Spec (.of k)))
    (completedOrdinaryScalarExtension_map l E.1 L.1 (IntermediateField.inclusion h)
      (Spec (.of k)))
  have hkin := hk
  unfold CochainComplex.IsKFlatIndependentCoefficients at hkin
  have hchanged := hchange (by
    unfold CochainComplex.IsKFlatIndependentCoefficients
    kernel_exact hkin) hflat
  obtain ⟨hk', hf'⟩ := hchanged
  refine ⟨?_, ?_, ?_⟩
  · kernel_exact hk'
  · intro i
    unfold SheafOfModules.IsFlatOnSite
    have hflat' := (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l L.1 (Spec (.of k)))
        ((((scalar k h).mapHomologicalComplex (.up ℤ)).obj P).X i)).symm (hf' i)
    kernel_exact hflat'
  · have : PreservesFiniteLimits (scalar k h) := scalarLimits k B E L h
    have : PreservesFiniteColimits (scalar k h) := scalarColimits k B E L h
    have hε := (B.derived E L h).comparison_counit P
    rw [← hε]
    exact IsIso.comp_isIso' ((B.derived E L h).comparison.app
      (DerivedCategory.Q.obj P)).isIso_inv
      (((scalar k h).mapDerivedCategoryFactors).app P).isIso_hom

end PointTensorTower

open PointTensorTower


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary scalar associators are compatible with point sections, including units,
four-field towers, arbitrary derived morphisms and all flat-term K-flat models.
Source: Stacks 03EK, 06YS, 06YY, 0G7E, 0D6D and 04VG; blueprint
main-20261015, def-weil-finite-coefficient-point, final paragraph
(blueprint: lem-weil-point-derived-tensor-tower-coherence).

Proof:
1. For every pair choose the finite-free normalized sections comparison of
lem-weil-point-finite-free-sections-tensor and its counit-normalized descent from
lem-weil-point-derived-sections-tensor-descent. All complexes are permitted, including
an intermediate scalar extension. Constants uniquely identify the section rings,
so independent basis choices give the same comparisons.
2. Define the sheaf associator by (x tensor a) tensor b mapped to x tensor ab.
The inner balance is (rx) tensor ab = x tensor r(ab); the outer balance is
x tensor (ac)b = x tensor a(cb). Its inverse inserts 1. Apply the sheaf tensor
universal property def-pur-sheaf-tensor-product and def-weil-pbc-sheafification
successively. The composites are identities by balance. The same formulas define
the module associator; they commute with restrictions and with every map of modules.
3. Apply these maps termwise. Differentials act only on x, so they commute without
signs. Resolve by lem-pc-kflat-resolution. Apply
lem-weil-pbc-ringed-topos-kflat-pullback to the identity underlying topos and the
coefficient inclusion: scalar extension preserves K-flatness and flat terms.
lem-pur-derived-change-of-rings computes both successive extensions on these models.
4. Both routes through the section square take (n tensor a) tensor b to n tensor ab,
by the normalized comparison formula. Additivity and balancing prove equality before
sheafification; its uniqueness extends equality to sheaves, then to cochain maps.
5. Descend the maps and this equality by lem-weil-pbc-localization-universal-property.
Conjugate by the counit-fixed identifications in the descent dependency. This gives
exactly the displayed derived square and the two representative equations.
6. For a roof q inverse followed by f, naturality for q and f, and invertibility of
the quasi-isomorphism image, give naturality on that roof. Full faithfulness of
precomposition with localization makes the transformations unique with the displayed
representative equations. Thus every resolution computes the same transformations.
7. In the identity case multiplication x tensor r mapped to rx has inverse
x mapped to x tensor 1. On sections the normalized comparison intertwines this
with n tensor r mapped to rn. Apply termwise and descend as in step 5.
8. For four fields both composites take the nested tensor to x tensor (ab)c =
x tensor a(bc); the section formula gives n tensor abc. Successive tensor universal
properties prove equality of sheaf maps. Termwise extension and localization preserve
these equalities. Repeated fields and identity stages are included. -/
theorem point_derived_tensor_tower_coherence
    (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    ∃ B : PointTensorTower.Comparisons D.k (l := l) (Ω := Ω),
      ∃! C : PointTensorTower.Maps D.k B,
        PointTensorTower.OrdinaryLaws D.k B C ∧
        PointTensorTower.DerivedLaws D.k B C ∧
        PointTensorTower.ChainLaws D.k B C ∧
        PointTensorTower.PreservesModels D.k (l := l) (Ω := Ω) := by
  classical
  obtain ⟨B⟩ := tower_comparisons_nonempty D l _hl Ω
  refine ⟨B, ?_⟩
  choose θ hθ using theta_exists D.k B
  obtain ⟨O, ⟨hF, hO⟩, hOu⟩ := PointTensorTower.ordinary_tower D.k B θ hθ
  have : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
      PreservesFiniteLimits (scalar D.k h) := PointTensorTower.scalarLimits D.k B
  have : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
      PreservesFiniteColimits (scalar D.k h) := PointTensorTower.scalarColimits D.k B
  have : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
      PreservesFiniteLimits (tensor.{t} h) := PointTensorTower.tensorLimits D.k B
  have : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
      PreservesFiniteColimits (tensor.{t} h) := PointTensorTower.tensorColimits D.k B
  have : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1), (scalar D.k h).Additive :=
    fun E L h ↦ scalarAdditive (l := l) (Ω := Ω) D.k (E := E) (L := L) h
  have : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1), (tensor.{t} h).Additive :=
    fun E L h ↦ pointFiniteFreeModuleTensor_additive.{t, u} l E.1 L.1
      (IntermediateField.inclusion h)
  have : ∀ E, (sections D.k B E).Additive := sectionsAdditive D.k B
  have : ∀ E, PreservesFiniteLimits (sections D.k B E) := sectionsLimits D.k B
  have : ∀ E, PreservesFiniteColimits (sections D.k B E) := sectionsColimits D.k B
  obtain ⟨A, hA, hAu⟩ := CategoryTheory.ScalarTower.exact_transport_unique
    (S := modules D.k)
    (M := fun E : Fields l Ω ↦ ModuleCat.{max u (t + 1)} (integers E))
    (T := fun E L h ↦ scalar D.k (E := E) (L := L) h)
    (t := fun E L h ↦ tensor.{t} (E := E) (L := L) h)
    (G := sections D.k B) (TD := fun E L h ↦ scalarD D.k (E := E) (L := L) h)
    (c := fun E L h ↦ (B.derived E L h).comparison)
    (gAdd := sectionsAdditive D.k B) (gLim := sectionsLimits D.k B)
    (gColim := sectionsColimits D.k B) θ O hO
  rcases hA with ⟨hrep, hmrep, hunit, hmunit, hcoh⟩
  let C := PointTensorTower.mapsOfData D.k B θ O A
  have ho : OrdinaryLaws D.k B C :=
    PointTensorTower.ordinaryLaws_of_data D.k B θ hθ O A hF hO
  have hs (E L : Fields l Ω) (h : E.1 ≤ L.1) (P : complexes D.k E) :
      (CategoryTheory.ScalarTower.sigma (modules D.k)
        (fun E L h ↦ scalar D.k (E := E) (L := L) h)
        (fun E L h ↦ scalarD D.k (E := E) (L := L) h)
        (fun E L h ↦ (B.derived E L h).comparison) E L h).hom.app P =
      completedScalarCounit l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of D.k)) P :=
    by
      change (B.derived E L h).comparison.inv.app (DerivedCategory.Q.obj P) ≫
        (scalar D.k h).mapDerivedCategoryFactors.hom.app P = _
      exact (B.derived E L h).comparison_counit P
  have hrepConv := CategoryTheory.ScalarTower.representative_counit_iff
    (T := fun E L h ↦ scalar D.k (E := E) (L := L) h)
    (c := fun E L h ↦ (B.derived E L h).comparison) O A
    (fun E L h P ↦ completedScalarCounit l E.1 L.1
      (IntermediateField.inclusion h) (Spec (.of D.k)) P) hs
  have hunitConv := CategoryTheory.ScalarTower.unit_counit_iff
    (T := fun E L h ↦ scalar D.k (E := E) (L := L) h)
    (c := fun E L h ↦ (B.derived E L h).comparison) O A
    (fun E L h P ↦ completedScalarCounit l E.1 L.1
      (IntermediateField.inclusion h) (Spec (.of D.k)) P) hs
  have hrepNormalized := hrepConv.mp hrep
  have hunitNormalized := hunitConv.mp hunit
  have hAC : CategoryTheory.ScalarTower.Coherent (sectionsD D.k B)
      (PointTensorTower.canonicalThetaD D.k B θ) A := by
    kernel_exact hcoh
  have hd : DerivedLaws D.k B C := by
    constructor
    · have hn := PointTensorTower.canonicalThetaD_normalized D.k B θ hθ
      kernel_exact hn
    · kernel_exact hrepNormalized
    · kernel_exact hmrep
    · have hx := hAC.square
      kernel_exact hx
    · kernel_exact hunitNormalized
    · kernel_exact hmunit
    · have hx := hAC.unit
      kernel_exact hx
    · have hx := hAC.sheaf_tower
      kernel_exact hx
    · have hx := hAC.module_tower
      kernel_exact hx
  refine ⟨C, ⟨ho, hd, ?_, PointTensorTower.preserves_models D.k B⟩, ?_⟩
  · exact ⟨fun E L M h g P i ↦ ho.square E L M h g (P.X i),
      fun E P i ↦ ho.unit_square E (P.X i)⟩
  · intro Z hZ
    have hθZ : Z.theta = θ := by
      funext E L h
      exact eq_of_heq ((hZ.1.theta_normalized E L h).trans (hθ E L h).symm)
    let OZ : PointTensorTower.ordinaryData (l := l) (Ω := Ω) D.k :=
      ⟨Z.sheafComp, Z.moduleComp, Z.sheafUnit, Z.moduleUnit⟩
    have hOZ : OZ = O := hOu OZ (by
      constructor
      · constructor
        · have hx := hZ.1.sheaf_formula
          kernel_exact hx
        · have hx := hZ.1.sheaf_inverse
          kernel_exact hx
        · exact hZ.1.module_formula
        · exact hZ.1.module_inverse
        · have hx := hZ.1.sheaf_unit_formula
          kernel_exact hx
        · exact hZ.1.module_unit_formula
      · rw [← hθZ]
        exact ⟨hZ.1.square, hZ.1.unit_square, hZ.1.sheaf_tower, hZ.1.module_tower⟩)
    have hθDZ : Z.thetaD = PointTensorTower.canonicalThetaD D.k B θ := by
      funext E L h
      have hn := hd.thetaD_normalized E L h
      have hz := eq_of_heq ((hZ.2.1.thetaD_normalized E L h).trans hn.symm)
      kernel_exact hz
    have hsc := congrArg CategoryTheory.ScalarTower.OrdinaryMaps.sheafComp hOZ
    have hmc := congrArg CategoryTheory.ScalarTower.OrdinaryMaps.moduleComp hOZ
    have hsu := congrArg CategoryTheory.ScalarTower.OrdinaryMaps.sheafUnit hOZ
    have hmu := congrArg CategoryTheory.ScalarTower.OrdinaryMaps.moduleUnit hOZ
    let AZ : PointTensorTower.derivedData D.k B :=
      ⟨Z.alpha, Z.alphaMod, Z.unitD, Z.moduleUnitD⟩
    have hAZL : CategoryTheory.ScalarTower.RepresentativeLaws
        (S := modules D.k)
        (M := fun E : Fields l Ω ↦ ModuleCat.{max u (t + 1)} (integers E))
        (T := fun E L h ↦ scalar D.k (E := E) (L := L) h)
        (t := fun E L h ↦ tensor.{t} (E := E) (L := L) h)
        (TD := fun E L h ↦ scalarD D.k (E := E) (L := L) h)
        (c := fun E L h ↦ (B.derived E L h).comparison)
        OZ AZ := by
      refine { representative := ?_
               module_representative := hZ.2.1.module_representative
               unit_representative := ?_
               module_unit_representative := hZ.2.1.module_unit_representative }
      · intro E L M h g P
        simp only [hs]
        have hz := hZ.2.1.representative E L M h g P
        kernel_exact hz
      · intro E P
        simp only [hs]
        have hz := hZ.2.1.unit_representative E P
        kernel_exact hz
    have hAZ : AZ = A := hAu OZ hOZ AZ hAZL
    have hal := congrArg
      (fun X : PointTensorTower.derivedData D.k B ↦ X.sheafComp) hAZ
    have ham := congrArg
      (fun X : PointTensorTower.derivedData D.k B ↦ X.moduleComp) hAZ
    have hud := congrArg
      (fun X : PointTensorTower.derivedData D.k B ↦ X.sheafUnit) hAZ
    have hmd := congrArg
      (fun X : PointTensorTower.derivedData D.k B ↦ X.moduleUnit) hAZ
    exact PointTensorTower.maps_ext D.k B Z C hsc hmc hθZ hθDZ hal ham hsu hmu hud hmd

end WeilConjectures

