# Native total comparison projection APIs

## Reason

Repair C-25a68 A1 rebuilds this module on G6's current source. Every G6 retained
functor, cochainTensorComparison, totalSectionPullMonoidal and naturality theorem
is preserved verbatim. The canonical cochain structures stay in G6's shared
SectionCochainTensorComparison module. The original sectionTotalIso record and
all unit constructors are retained verbatim. Only four proved forward-projection
APIs are added. Their proofs unfold the original constructor and are reflexivity.

The oplax importer retains G6's cochainTensorComparison unfolding. Its two summand
proofs use forward projections, and its oplax laws use the native tensorator/unit
projection equations. The normalization consumer changes only its private
comparison proof to the same forward API and reflexive transport simplification.
Every signature and public import of these consumers remains unchanged.
Both adapted consumers are unclaimed. Target meanings are preserved; the
independent reader checks these definition APIs together with their consumers.

## Old

The original sectionTotalIso is retained unchanged:

```lean
def sectionTotalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (totalSectionPull Λ f).obj (P ⊗ Q) ≅
      (totalSectionPull Λ f).obj P ⊗ (totalSectionPull Λ f).obj Q where
  hom := Functor.OplaxMonoidal.δ (totalSectionPull Λ f) P Q
  inv := Functor.LaxMonoidal.μ (totalSectionPull Λ f) P Q
  hom_inv_id := Functor.Monoidal.δ_μ (totalSectionPull Λ f) P Q
  inv_hom_id := Functor.Monoidal.μ_δ (totalSectionPull Λ f) P Q


set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] totalComparison ordinaryTensorComparison ordinaryUnitComparison

section ExplicitConjugation

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  (F : A ⥤ B) (G : C ⥤ B) {x y : A} {u v : C} {w t : B}
  (p : x ≅ y) (r : G.obj u ≅ F.obj x) (i : u ≅ v) (c : G.obj v ≅ w) (e : w ≅ t)
```

The normalization consumer originally uses:

```lean
  unfold totalPullComparison sectionTotalIso
  rfl
```

## New

Four new proved theorems expose the existing maps:

```lean
theorem actualInternalTotalIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) :
    (actualInternalTotalIso Λ f P Q).hom =
      (letI := CondensedRing.monoidal_upperStar Λ f
       HomologicalComplex.mapBifunctorComparison
         (Functor.OplaxMonoidal.δNatTrans (CondensedRing.upperStar Λ f)) (.up ℤ) P Q) := by
  unfold actualInternalTotalIso
  rfl
```

```lean
theorem sectionTotalIso_δ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (sectionTotalIso Λ f P Q).hom = Functor.OplaxMonoidal.δ (totalSectionPull Λ f) P Q := by
  unfold sectionTotalIso
  rfl
```

```lean
theorem sectionTotalIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (sectionTotalIso Λ f P Q).hom =
      HomologicalComplex.mapBifunctorComparison
        (Functor.OplaxMonoidal.δNatTrans (pullback Λ f)) (.up ℤ) P Q := by
  unfold sectionTotalIso
  rfl
```

```lean
theorem sectionTotalUnit_η {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sectionTotalUnit Λ f = Functor.OplaxMonoidal.η (totalSectionPull Λ f) := by
  unfold sectionTotalUnit normalizationSectionUnit
  rfl
```

The normalization consumer uses:

```lean
  rw [sectionTotalIso_hom]
  unfold totalPullComparison
  simp only [eqToHom_refl, Functor.map_id, Category.id_comp, Category.comp_id]
```

## Users

Current source query: `tools/downstream.py
Sheaf.Paper.SectionTotalOplaxComparisonData --uses actualInternalTotalIso
sectionTotalIso sectionTotalUnit`. Additional rows include all adapted and
explicitly checked consumers. G6's current conjugation and component modules are
checked without changes; their source and declaration signatures are preserved.
Validation results are in report.md.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.BoundedFlatTensorContinuity | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionDerivedRealization | unclaimed | All declarations and bodies retained; synchronous elaboration. |
| Sheaf.Paper.SectionDerivedRepresentativeSquare | U3 | Proved square; predicate reflexivity checked against current originals. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | G6 import, parameters and all D7/G6 declarations retained; tensor transport shared. |
| Sheaf.Paper.SectionDerivedTensorNormalization | unclaimed | Private proof uses forward API; all signatures retained. |
| Sheaf.Paper.SectionKFlatTensorComparison | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionOplaxTotalComparison | unclaimed | G6 proof retained; projection APIs replace constructor unfolding. |
| Sheaf.Paper.SectionRepresentativeTensorArrow | unclaimed | Current G6 retained components; no adaptation. |
| Sheaf.Paper.SectionResolutionConjugationIdentities | unclaimed | Current G6 proof and retained interfaces; no adaptation. |
| Sheaf.Paper.SectionResolvingOplaxConstraintData | unclaimed | Same transported structure through shared constant; signatures retained. |
| Sheaf.Paper.SectionResolvingOplaxConstraintDiagrams | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionTensorRightComputation | unclaimed | Same mathematical data; no consumer adaptation required. |
| Sheaf.Paper.SectionTotalOplaxComparisonData | unclaimed | All G6 constructions retained verbatim; four proved projection APIs added. |

## Validation

The edited modules and all six requested consumers compile through lcompile.py.
The four full representative predicates were compared with current originals by
private rfl proofs; all checks passed. The theorem signature is verbatim.
Current G6 component and conjugation modules compile unchanged. See report.md
for the exact validation scope and existing warnings.

## Status

landed 20261026T222800-L-695347 2026-10-26 (merge of deliver/U3/Sheaf.Paper.SectionDerivedRepresentativeSquare)
