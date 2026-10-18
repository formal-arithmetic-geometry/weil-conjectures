# CategoryTheory.constantModule_section_properties

## Reason

The proof needs private finite-limit, exactness, linearity and finite-presentation
tensor helpers. Its proof scopes introduce `open Limits`, section variables and local
instance registrations. This record documents the scope-command change detected by
preflight. Every auxiliary declaration is private. The three instance properties are
proved as private theorems and registered with `[local instance]`; no global instance
is added. The existing theorem signature and public imports are unchanged.

## Old

The module placed its public section before the universe and namespace commands:

```lean
@[expose] public section

universe u

open CategoryTheory Opposite TensorProduct

namespace CategoryTheory
```

There were no proof helpers, local instance registrations or `TensorComparison` section.
The existing theorem's entire proof was `by sorry`.

## New

The private proof preamble starts with these commands:

```lean
universe u

open CategoryTheory Opposite TensorProduct

namespace CategoryTheory

open Limits

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Type u) [CommRing R]
```

The private instance-property theorems are registered only for this proof scope:

```lean
attribute [local instance] section_preservesFiniteLimits
attribute [local instance] section_linear
attribute [local instance] section_preservesFiniteColimits
```

The finite-presentation comparison uses the following local proof section:

```lean
section TensorComparison

variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [Functor.Linear R F]
```

That section closes before `@[expose] public section`, which now immediately precedes
the existing theorem and closes before `end CategoryTheory`. The theorem has exactly
its old textual signature and a complete proof. The proof's added imports are private;
no public import or existing data definition changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConstantModuleSectionProperties | T3 | private proof scopes only; theorem signature unchanged |
| Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy | Q2 | transitive importer; no statement or definition change |
| Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre | G1 | direct proof importer; no adaptation needed |
| Sheaf.Paper.FiniteCtfTriangulated | G1 | transitive importer; no statement or definition change |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | G2 | transitive importer; no statement or definition change |
| Sheaf.Paper.FiniteTorsionConstructibility | unclaimed | transitive importer; no statement or definition change |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | unclaimed | transitive importer; no statement or definition change |
| Sheaf.Paper.LocallyConstantTensor | N1 | transitive importer; no statement or definition change |
| Sheaf.Paper.NilpotentReductionLissity | N2 | transitive importer; no statement or definition change |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | U2 | transitive importer; no statement or definition change |
| Sheaf.Paper.ProEtaleResidueTorTest | G3 | transitive importer; no statement or definition change |
| Sheaf.Paper.SiteBoundedConstantModel | P3 | transitive importer; no statement or definition change |

`tools/downstream.py Sheaf.Paper.ConstantModuleSectionProperties --uses
constantModule_section_properties` lists these 11 importers and finds no textual
use of the declaration outside its own module. No consumer file is changed, no
existing definition changes meaning, and no target statement review is reopened.
The direct importer `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre` compiled
unchanged against the delivered module in a scratch overlay (6.0 seconds).

## Status

landed 20261018T062918-L-679716 2026-10-18 (merge of deliver/T3/Sheaf.Paper.ConstantModuleSectionProperties)
