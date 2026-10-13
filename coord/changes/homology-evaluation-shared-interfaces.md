# Homology evaluation shared interfaces

## Reason

Extract the existing definitions and the proved zero-morphism lemma unchanged into a shared module so three independent proof-step modules can use them without importing the theorem they are to prove. This changes declaration location, not mathematical data or types. The original module publicly re-exports the definitions and retains the original public API through the shared module and its KInjective import.

## Old

Declared in `Sheaf.Algebra.Homology.HomologyEvaluation`, verbatim:

```lean
/-- Restriction to an open scheme followed by an over site preserves zero morphisms.
Source: Stacks Project, Tag 08DL, termwise restriction.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
theorem moduleOpenOver_preservesZeroMorphisms (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens) :
    (Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext A x
  rfl

/-- Termwise restriction to an open scheme followed by an over site.
Source: Stacks Project, Tag 08DL, termwise restriction.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
noncomputable def moduleOpenOverComplexFunctor (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens) :
    CochainComplex X.Modules ℤ ⥤
      CochainComplex (SheafOfModules.{u} (V.toScheme.ringCatSheaf.over W)) ℤ :=
  letI := moduleOpenOver_preservesZeroMorphisms X V W
  (Scheme.Modules.restrictFunctor V.ι ⋙
    SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- A complex admits a finite free, zero-differential model by a quasi-isomorphism roof.
Source: Stacks Project, Tag 0BQY, zero-differential Koszul calculation.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
def HasFiniteFreeZeroModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (T : CochainComplex (SheafOfModules.{u} R) ℤ) : Prop :=
  ∃ (E L : CochainComplex (SheafOfModules.{u} R) ℤ)
    (q : L ⟶ T) (p : L ⟶ E),
    QuasiIso q ∧ QuasiIso p ∧
      (∀ a b : ℤ, E.d a b = 0) ∧
      (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k)) ∧
      (∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
        SheafOfModules.free (R := R) (ULift.{u} (Fin r))))

/-- The degree component used to evaluate a Hom cocycle on a cycle.
Source: Stacks Project, Tag 0A8X, product definition of the Hom complex.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
noncomputable def homologyEvaluationProjection (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    (homComplex (R := X.sheaf) T J).X n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.X (-n)) (J.X 0) :=
  (Classical.choose (homComplex_projections_exists.{u, u, u, u}
    (R := X.sheaf))) T J n (-n) 0 (by omega)

/-- Characterization of evaluation on classes by its action on local cycle representatives.
Source: Stacks Project, Tags 0A8X and 08DH, evaluation of the Hom complex.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
def IsHomologyEvaluation (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0)) : Prop :=
  let P := homComplex (R := X.sheaf) T J
  ∀ (U : X.Opens)
    (φ : (P.cycles n).val.obj (op U))
    (z : (T.cycles (-n)).val.obj (op U)) (b : (J.cycles 0).val.obj (op U)),
    (J.iCycles 0).val.app (op U) b =
      ((homologyEvaluationProjection X T J n).val.app (op U)
        ((P.iCycles n).val.app (op U) φ)).app
          (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z) →
    (e.val.app (op U)
      ((P.homologyπ n).val.app (op U) φ)).app
        (op (Over.mk (𝟙 U))) ((T.homologyπ (-n)).val.app (op U) z) =
      (J.homologyπ 0).val.app (op U) b
```

## New

Declared in `Sheaf.Algebra.Homology.HomologyEvaluationDefinitions`, verbatim:

```lean
/-- Restriction to an open scheme followed by an over site preserves zero morphisms.
Source: Stacks Project, Tag 08DL, termwise restriction.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
theorem moduleOpenOver_preservesZeroMorphisms (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens) :
    (Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext A x
  rfl

/-- Termwise restriction to an open scheme followed by an over site.
Source: Stacks Project, Tag 08DL, termwise restriction.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
noncomputable def moduleOpenOverComplexFunctor (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens) :
    CochainComplex X.Modules ℤ ⥤
      CochainComplex (SheafOfModules.{u} (V.toScheme.ringCatSheaf.over W)) ℤ :=
  letI := moduleOpenOver_preservesZeroMorphisms X V W
  (Scheme.Modules.restrictFunctor V.ι ⋙
    SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- A complex admits a finite free, zero-differential model by a quasi-isomorphism roof.
Source: Stacks Project, Tag 0BQY, zero-differential Koszul calculation.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
def HasFiniteFreeZeroModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (T : CochainComplex (SheafOfModules.{u} R) ℤ) : Prop :=
  ∃ (E L : CochainComplex (SheafOfModules.{u} R) ℤ)
    (q : L ⟶ T) (p : L ⟶ E),
    QuasiIso q ∧ QuasiIso p ∧
      (∀ a b : ℤ, E.d a b = 0) ∧
      (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k)) ∧
      (∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
        SheafOfModules.free (R := R) (ULift.{u} (Fin r))))

/-- The degree component used to evaluate a Hom cocycle on a cycle.
Source: Stacks Project, Tag 0A8X, product definition of the Hom complex.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
noncomputable def homologyEvaluationProjection (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    (homComplex (R := X.sheaf) T J).X n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.X (-n)) (J.X 0) :=
  (Classical.choose (homComplex_projections_exists.{u, u, u, u}
    (R := X.sheaf))) T J n (-n) 0 (by omega)

/-- Characterization of evaluation on classes by its action on local cycle representatives.
Source: Stacks Project, Tags 0A8X and 08DH, evaluation of the Hom complex.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/
def IsHomologyEvaluation (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0)) : Prop :=
  let P := homComplex (R := X.sheaf) T J
  ∀ (U : X.Opens)
    (φ : (P.cycles n).val.obj (op U))
    (z : (T.cycles (-n)).val.obj (op U)) (b : (J.cycles 0).val.obj (op U)),
    (J.iCycles 0).val.app (op U) b =
      ((homologyEvaluationProjection X T J n).val.app (op U)
        ((P.iCycles n).val.app (op U) φ)).app
          (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z) →
    (e.val.app (op U)
      ((P.homologyπ n).val.app (op U) φ)).app
        (op (Over.mk (𝟙 U))) ((T.homologyπ (-n)).val.app (op U) z) =
      (J.homologyπ 0).val.app (op U) b
```

The item publicly re-exports the shared module. Its former direct imports of
HomComplexProjections and Modules.Sheaf are supplied by that public re-export.
KInjective stays public in the item and LocalIso because their signatures use it;
the shared definitions instead import the smaller Mathlib QuasiIso module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.HomologyEvaluation | B2 | Uses the publicly imported identical definitions. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel | unclaimed | Its existing import still exposes the same names and bodies; no adaptation required. |

All 342 transitive importers retain the original public imports and declarations. Textual --uses inspection finds only SelfExtTorResolutionModel directly mentioning the moved definitions. No target meaning changes; no downstream proof or statement is adapted.

## Status

landed 20261013T172650-L-2097516 2026-10-13 (merge of deliver/B2/Sheaf.Algebra.Homology.HomologyEvaluation)
