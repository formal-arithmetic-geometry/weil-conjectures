/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

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
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Ordinary scalar towers and point sections

Source: Stacks 03EK, 06YY, 0G7E, 0D6D and 04VG; the final paragraph of blueprint
main-20261015, def-weil-finite-coefficient-point
(blueprint: lem-weil-point-derived-tensor-tower-coherence).

All tensors below are ordinary change of rings. The completed sheaves supply the
coefficient rings, but no completion functor occurs in the assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u m r
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.PointTensorTower

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
abbrev modules (E : Fields l Ω) := integralTowerModules l E.1 (Spec (.of k))

/-- The original unbounded cochain category.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev complexes (E : Fields l Ω) := CochainComplex (modules k E) ℤ

/-- Ordinary scalar extension on sheaves along the given field inclusion.
Source: Stacks 03EK (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev scalar {E L : Fields l Ω} (h : E.1 ≤ L.1) :=
  completedOrdinaryScalarExtension l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k))

/-- Reexport the recorded additivity on the transparent scalar-extension alias.
Source: Stacks 03EK (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
instance scalarAdditive {E L : Fields l Ω} (h : E.1 ≤ L.1) : (scalar k h).Additive :=
  completedOrdinaryScalarExtension_additive l E.1 L.1
    (IntermediateField.inclusion h) (Spec (.of k))

/-- The recorded termwise extension, without completion.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev scalarC {E L : Fields l Ω} (h : E.1 ≤ L.1) :=
  completedOrdinaryScalarComplex l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k))

/-- The prescribed ordinary K-flat derived extension and its counit are retained.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev scalarD {E L : Fields l Ω} (h : E.1 ≤ L.1) :=
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
abbrev sections (E : Fields l Ω) :=
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
abbrev sectionsD (E : Fields l Ω) := (sections k B E).mapDerivedCategory

/-- Exact-derived module extension, with exactness furnished by descent.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
abbrev tensorD {E L : Fields l Ω} (h : E.1 ≤ L.1) :=
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
abbrev generator {E L : Fields l Ω} (h : E.1 ≤ L.1) (F : modules k E)
    (U : (Spec (.of k)).ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l L.1 (Spec (.of k))).obj.obj U)
    (x : F.val.obj U) :=
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
    scalar k h ⋙ scalar k g ≅ scalar k (h.trans g)
  moduleComp : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1),
    tensor.{t} h ⋙ tensor.{t} g ≅ tensor.{t} (h.trans g)
  theta : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
    sections k B E ⋙ tensor.{t} h ≅ scalar k h ⋙ sections k B L
  thetaD : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
    sectionsD k B E ⋙ tensorD k B h ≅ scalarD k h ⋙ sectionsD k B L
  alpha : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1),
    scalarD k h ⋙ scalarD k g ≅ scalarD k (h.trans g)
  alphaMod : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1),
    tensorD k B h ⋙ tensorD k B g ≅ tensorD k B (h.trans g)
  sheafUnit : ∀ E : Fields l Ω, scalar k (E := E) le_rfl ≅ 𝟭 (modules k E)
  moduleUnit : ∀ E : Fields l Ω,
    tensor.{t} (E := E) le_rfl ≅ 𝟭 (ModuleCat.{max u (t + 1)} (integers E))
  unitD : ∀ E : Fields l Ω, scalarD k (E := E) le_rfl ≅ 𝟭 (DerivedCategory (modules k E))
  moduleUnitD : ∀ E : Fields l Ω,
    tensorD k B (E := E) le_rfl ≅
      𝟭 (DerivedCategory (ModuleCat.{max u (t + 1)} (integers E)))

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The balanced formulas and ordinary section, unit and four-field equations.
Source: Stacks 03EK, 06YY, 0G7E, 0D6D, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
structure OrdinaryLaws (C : Maps k B) : Prop where
  sheaf_formula : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (F : modules k E) U a b x,
    ((C.sheafComp E L M h g).hom.app F).val.app U
      (generator k g ((scalar k h).obj F) U b (generator k h F U a x)) =
        generator k (h.trans g) F U (coefficient k g U a * b) x
  sheaf_inverse : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (F : modules k E) U b x,
    ((C.sheafComp E L M h g).inv.app F).val.app U
      (generator k (h.trans g) F U b x) =
        generator k g ((scalar k h).obj F) U b (generator k h F U 1 x)
  module_formula : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (N : ModuleCat.{max u (t + 1)} (integers E)) (a : integers L) (b : integers M) (n : N),
    (C.moduleComp E L M h g).hom.app N
      (moduleGenerator.{t} g ((tensor.{t} h).obj N) b (moduleGenerator.{t} h N a n)) =
        moduleGenerator.{t} (h.trans g) N (inclusion g a * b) n
  module_inverse : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (N : ModuleCat.{max u (t + 1)} (integers E)) (b : integers M) (n : N),
    (C.moduleComp E L M h g).inv.app N (moduleGenerator.{t} (h.trans g) N b n) =
      moduleGenerator.{t} g ((tensor.{t} h).obj N) b (moduleGenerator.{t} h N 1 n)
  theta_normalized : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
    HEq (C.theta E L h) (B.finite E L h).comparison
  square : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1) (F : modules k E),
    (tensor.{t} g).map ((C.theta E L h).hom.app F) ≫
      (C.theta L M g).hom.app ((scalar k h).obj F) ≫
      (sections k B M).map ((C.sheafComp E L M h g).hom.app F) =
    (C.moduleComp E L M h g).hom.app ((sections k B E).obj F) ≫
      (C.theta E M (h.trans g)).hom.app F
  sheaf_unit_formula : ∀ (E : Fields l Ω) (F : modules k E) U a x,
    ((C.sheafUnit E).hom.app F).val.app U (generator k le_rfl F U a x) = a • x
  module_unit_formula : ∀ (E : Fields l Ω)
    (N : ModuleCat.{max u (t + 1)} (integers E)) (a : integers E) (n : N),
    (C.moduleUnit E).hom.app N (moduleGenerator.{t} le_rfl N a n) = a • n
  unit_square : ∀ (E : Fields l Ω) (F : modules k E),
    (C.theta E E le_rfl).hom.app F ≫ (sections k B E).map ((C.sheafUnit E).hom.app F) =
      (C.moduleUnit E).hom.app ((sections k B E).obj F)
  sheaf_tower : ∀ (E L M H : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (j : M.1 ≤ H.1) (F : modules k E),
    (scalar k j).map ((C.sheafComp E L M h g).hom.app F) ≫
      (C.sheafComp E M H (h.trans g) j).hom.app F =
    (C.sheafComp L M H g j).hom.app ((scalar k h).obj F) ≫
      (C.sheafComp E L H h (g.trans j)).hom.app F
  module_tower : ∀ (E L M H : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (j : M.1 ≤ H.1) (N : ModuleCat.{max u (t + 1)} (integers E)),
    (tensor.{t} j).map ((C.moduleComp E L M h g).hom.app N) ≫
      (C.moduleComp E M H (h.trans g) j).hom.app N =
    (C.moduleComp L M H g j).hom.app ((tensor.{t} h).obj N) ≫
      (C.moduleComp E L H h (g.trans j)).hom.app N

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Normalized descent, representative equations and all derived coherence laws.
Source: Stacks 03EK, 06YY, 0G7E, 0D6D, 04VG
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
structure DerivedLaws (Z : Maps k B) : Prop where
  thetaD_normalized : ∀ (E L : Fields l Ω) (h : E.1 ≤ L.1),
    HEq (Z.thetaD E L h) (B.derived E L h).theta
  representative : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (C : complexes k E),
    (scalarD k g).map
        (completedScalarCounit l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k)) C) ≫
      completedScalarCounit l L.1 M.1 (IntermediateField.inclusion g) (Spec (.of k))
        ((scalarC k h).obj C) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (Z.sheafComp E L M h g) (.up ℤ)).hom.app C) =
    (Z.alpha E L M h g).hom.app (DerivedCategory.Q.obj C) ≫
      completedScalarCounit l E.1 M.1 (IntermediateField.inclusion (h.trans g))
        (Spec (.of k)) C
  module_representative : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (C : CochainComplex (ModuleCat.{max u (t + 1)} (integers E)) ℤ),
    (Z.alphaMod E L M h g).hom.app (DerivedCategory.Q.obj C) ≫
      (tensorFactors k B (h.trans g)).hom.app C =
    (tensorD k B g).map ((tensorFactors k B h).hom.app C) ≫
      (tensorFactors k B g).hom.app
        (((tensor.{t} h).mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (Z.moduleComp E L M h g) (.up ℤ)).hom.app C)
  derived_square : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (K : DerivedCategory (modules k E)),
    (tensorD k B g).map ((Z.thetaD E L h).hom.app K) ≫
      (Z.thetaD L M g).hom.app ((scalarD k h).obj K) ≫
      (sectionsD k B M).map ((Z.alpha E L M h g).hom.app K) =
    (Z.alphaMod E L M h g).hom.app ((sectionsD k B E).obj K) ≫
      (Z.thetaD E M (h.trans g)).hom.app K
  unit_representative : ∀ (E : Fields l Ω) (C : complexes k E),
    (Z.unitD E).hom.app (DerivedCategory.Q.obj C) =
      completedScalarCounit l E.1 E.1 (IntermediateField.inclusion le_rfl) (Spec (.of k)) C ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Z.sheafUnit E) (.up ℤ)).hom.app C)
  module_unit_representative : ∀ (E : Fields l Ω)
    (C : CochainComplex (ModuleCat.{max u (t + 1)} (integers E)) ℤ),
    (Z.moduleUnitD E).hom.app (DerivedCategory.Q.obj C) =
      (tensorFactors k B (E := E) le_rfl).hom.app C ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Z.moduleUnit E) (.up ℤ)).hom.app C)
  derived_unit_square : ∀ (E : Fields l Ω) (K : DerivedCategory (modules k E)),
    (Z.thetaD E E le_rfl).hom.app K ≫ (sectionsD k B E).map ((Z.unitD E).hom.app K) =
      (Z.moduleUnitD E).hom.app ((sectionsD k B E).obj K)
  derived_tower : ∀ (E L M H : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (j : M.1 ≤ H.1) (K : DerivedCategory (modules k E)),
    (scalarD k j).map ((Z.alpha E L M h g).hom.app K) ≫
      (Z.alpha E M H (h.trans g) j).hom.app K =
    (Z.alpha L M H g j).hom.app ((scalarD k h).obj K) ≫
      (Z.alpha E L H h (g.trans j)).hom.app K
  derived_module_tower : ∀ (E L M H : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (j : M.1 ≤ H.1) (K : DerivedCategory (ModuleCat.{max u (t + 1)} (integers E))),
    (tensorD k B j).map ((Z.alphaMod E L M h g).hom.app K) ≫
      (Z.alphaMod E M H (h.trans g) j).hom.app K =
    (Z.alphaMod L M H g j).hom.app ((tensorD k B h).obj K) ≫
      (Z.alphaMod E L H h (g.trans j)).hom.app K

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Cochain square and unit equations in every degree. Every component is obtained
termwise from a natural transformation, so it commutes with differentials; equality
of cochain maps is exactly equality of these components for every integer degree.
Source: Stacks 03EK and 06YY
(blueprint: lem-weil-point-derived-tensor-tower-coherence). -/
structure ChainLaws (Z : Maps k B) : Prop where
  square : ∀ (E L M : Fields l Ω) (h : E.1 ≤ L.1) (g : L.1 ≤ M.1)
    (P : complexes k E) (i : ℤ),
    (tensor.{t} g).map ((Z.theta E L h).hom.app (P.X i)) ≫
      (Z.theta L M g).hom.app ((scalar k h).obj (P.X i)) ≫
      (sections k B M).map ((Z.sheafComp E L M h g).hom.app (P.X i)) =
    (Z.moduleComp E L M h g).hom.app ((sections k B E).obj (P.X i)) ≫
      (Z.theta E M (h.trans g)).hom.app (P.X i)
  unit : ∀ (E : Fields l Ω) (P : complexes k E) (i : ℤ),
    (Z.theta E E le_rfl).hom.app (P.X i) ≫
      (sections k B E).map ((Z.sheafUnit E).hom.app (P.X i)) =
    (Z.moduleUnit E).hom.app ((sections k B E).obj (P.X i))

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
      ((scalarC k h).obj P) ∧
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology (Spec (.of k)))
      (R := completedIntegralCommRingSheafUnrestricted l L.1 (Spec (.of k)))
      (((scalarC k h).obj P).X i)) ∧
    IsIso (completedScalarCounit l E.1 L.1 (IntermediateField.inclusion h) (Spec (.of k)) P)

end WeilConjectures.PointTensorTower

namespace WeilConjectures

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
  sorry

end WeilConjectures

