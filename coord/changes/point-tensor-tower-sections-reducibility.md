# WeilConjectures.PointTensorTower.generator and law-record interfaces

## Reason

The local modules alias now spells out SheafOfModules over the completed ring sheaf,
rather than reaching that same ring through the commutative-sheaf forgetful functor.
These categories are definitionally equal. The scalar, scalarC and scalarD aliases
keep their original bodies, with explicit source and target categories.

Repeated conversion unfolds completed coefficient limits and sheafification while
checking pure tensor formulas. The generator becomes a semireducible definition with
its already inferred result type explicit; its construction stays verbatim. The
sections, sectionsD and tensorD abbreviations retain their original bodies and
reducibility, with explicit result types. tensorFactors and moduleGenerator are unchanged.

Maps makes the existing finite-field endpoints explicit without changing its field types.
Law-record clauses are factored into named proposition definitions with the same
formulas. The fields retain their names and refer to these definitions. Finite-field
endpoints and section element types are explicit. The ordinary sheaf unit formula
spells out the existing module action. These are definitionally equal presentations:
no mathematical hypothesis or conclusion changes. They prevent the formula types
from being repeatedly expanded while elaborating record projections and conversions.
The final proof uses local irreducibility for large completed and derived constructions;
proof conversion terms are still checked by Lean's kernel.

## Old

```lean
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
```

## New

```lean
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
```

The additional file-level removal of the pro-etale sheafification instance avoids
competing choices in the point calculations. The existing essentially-small instance
removal is retained. Both direct consumer sources were checked unchanged against
this instance environment.

## Users

`tools/downstream.py Sheaf.Paper.PointDerivedTensorTowerCoherence --uses sections`
finds two downstream modules and no use of the alias outside the item. The same
check with sectionsD, tensorD, tensorFactors, OrdinaryLaws, DerivedLaws and ChainLaws
finds no external use of those declarations either. The generator search also reports
CompletedModelSectionsTransport; inspection identifies its separate local generator
definition and uses, with no reference to PointTensorTower.generator. moduleGenerator
has no external use.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointDerivedTensorTowerCoherence | H6 | Explicit unfolding in normalization proofs. |
| Sheaf.Paper.CompletedModelSectionsTransport | unclaimed at inspection | Import only; no use of the changed aliases or law records. |
| Sheaf.Paper.PointInverseImageCoefficientTower | unclaimed at inspection | Import only; no use of the changed aliases or law records. |

Both unchanged consumer sources compile against the final repaired item
(compile 92a76f88a5fb8b8a7fcf442c, exit 0). No consumer
adaptation is necessary.

Targets that transitively use these definitions require the usual statement review again;
the changes are definitionally equal presentations of the original formulas. No target
signature is edited.

## Status

landed 20261025T202213-L-2692230 2026-10-25 (merge of deliver/H6/Sheaf.Paper.PointDerivedTensorTowerCoherence)
