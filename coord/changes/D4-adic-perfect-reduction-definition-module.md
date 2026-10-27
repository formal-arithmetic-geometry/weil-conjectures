# adicPerfectLocalComplex and the ordinary quotient model definitions

## Reason

The two proof obligations need separately importable modules. Move the existing
ordinary-complex definitions and the proved cone equation into a definitions-only
module, avoiding an import cycle between the assigned theorem and its new lemmas.
This is a relocation for proof access, not a change of mathematical data. The
assigned module publicly reexports the definitions module, retaining all old
names, signatures, bodies, visibility and public imports transitively.

## Old

The following block was in `Sheaf.Paper.AdicPerfectReductionModels`:

```lean
/-- The actual termwise completed constant complex restricted to the slice.
Source: Stacks Tag 09C6.
(blueprint: def-sfb-adic-perfect-reduction-model-complexes). -/
def adicPerfectLocalComplex (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U) :=
  let F := SheafOfModules.strictPerfectConstantSheaf
      (coefficientProEtaleModelTopology.{u, v} X) A ⋙
    SheafOfModules.restrictScalars
      (constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
    change (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J) ⋙
    SheafOfModules.overFunctor _ U
  (F.mapHomologicalComplex (.up ℤ)).obj P

attribute [local irreducible] adicPerfectLocalComplex

/-- Ordinary termwise reduction, before derived localization.
Source: Stacks Tags 09C6 and 06YY.
(blueprint: def-sfb-adic-perfect-reduction-model-complexes). -/
def adicPerfectQuotientComplex (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (n : ℕ) :
    Cx ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) :=
  ((change (adicResidueLocalProjection.{u, v} X J U n)).mapHomologicalComplex (.up ℤ)).obj
    (adicPerfectLocalComplex.{u, v} X J U P)

/-- The ring map used for the ordinary successor reduction on the slice.
Source: Stacks Tags 09C6 and 099M.
(blueprint: def-sfb-adic-perfect-reduction-model-complexes). -/
def adicPerfectQuotientScalarStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    (finite (coefficientProEtaleModelTopology.{u, v} X) A J (n + 1)).over U ⟶
      (finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U :=
  ((coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U).map
    (transition (coefficientProEtaleModelTopology.{u, v} X) A J n)

/-- The actual cone equation after restriction to the slice.
Source: Stacks Tag 099M.
(blueprint: def-sfb-adic-perfect-reduction-model-complexes).
Proof: restrict the limit cone equation at the successor arrow. -/
theorem adicPerfectQuotientScalarStep_comp (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    adicResidueLocalProjection.{u, v} X J U (n + 1) ≫ adicPerfectQuotientScalarStep.{u, v} X J U n =
      adicResidueLocalProjection.{u, v} X J U n := by
  let V := (coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U
  dsimp only [adicResidueLocalProjection, adicPerfectQuotientScalarStep]
  rw [← V.map_comp]
  congr 1
  simpa only [completed, projection, finiteSystem, Functor.ofOpSequence_map_homOfLE_succ] using
    (limit.w (finiteSystem (coefficientProEtaleModelTopology.{u, v} X) A J)
      (homOfLE (Nat.le_succ n)).op)

attribute [local irreducible] derivedExtension extend change

/-- Ordinary successor reassociation, fixed by scalar balancing on pure tensors.
Source: Stacks Tags 06YY and 09C6.
(blueprint: def-sfb-adic-perfect-reduction-model-complexes). -/
def adicPerfectQuotientStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (n : ℕ) :
    ((change (adicPerfectQuotientScalarStep.{u, v} X J U n)).mapHomologicalComplex (.up ℤ)).obj
        (adicPerfectQuotientComplex.{u, v} X J U P (n + 1)) ≅
      adicPerfectQuotientComplex.{u, v} X J U P n :=
  (Functor.mapHomologicalComplexCompIso
    (adicFiniteChangeComp (adicResidueLocalProjection.{u, v} X J U (n + 1))
      (adicPerfectQuotientScalarStep.{u, v} X J U n) ≪≫
        eqToIso (congrArg change (adicPerfectQuotientScalarStep_comp.{u, v} X J U n)))
    (.up ℤ)).app (adicPerfectLocalComplex.{u, v} X J U P)

attribute [local irreducible] adicPerfectQuotientComplex adicPerfectQuotientStep

/-- The existing derived balancing isomorphism, with its functors explicitly typed.
The explicit type prevents elaboration from expanding the full construction of
successive derived scalar extensions when using a component of this isomorphism.
Source: Stacks Tags 06YY and 09C6.
(blueprint: def-sfb-adic-perfect-reduction-model-complexes). -/
abbrev adicPerfectDerivedQuotientStep (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    adicResidueLocalReduction.{u, v} X J U (n + 1) ⋙
        extend (adicPerfectQuotientScalarStep.{u, v} X J U n) ≅
      adicResidueLocalReduction.{u, v} X J U n :=
  adicResidueLocalReductionStep.{u, v} X J U n
```

## New

The identical block is in `Sheaf.Paper.AdicPerfectReductionModelComplexes`.
The assigned module has:

```lean
public import Sheaf.Paper.AdicPerfectReductionModelComplexes
```

No existing declaration's signature or body changes in this block. No target
statement or definition meaning changes. The old public imports remain public
through the reexport, and the two new proof lemmas are imported privately.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPerfectReductionModels | D4 | Public reexport; theorem uses the new proof modules. |
| Sheaf.Paper.AdicPerfectHomCohomologyComparison | unclaimed (landed P4) | Names and definitional equalities remain available through the public reexport; no adaptation. |
| Sheaf.Paper.AdicPerfectModelHomCohomology | unclaimed | Names and definitional equalities remain available through the public reexport; no adaptation. |

These are all textual consumers of the moved declarations. Other transitive
importers see the same public declarations. No held module is adapted.

## Status

landed 20261026T065433-L-2969140 2026-10-26 (merge of deliver/D4/Sheaf.Paper.AdicPerfectReductionModels)
