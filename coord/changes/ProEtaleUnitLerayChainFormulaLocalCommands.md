# AlgebraicGeometry.Scheme.proEtaleUnitLeraySections

## Reason

Record the file-local elaboration commands and scoped variables introduced by the proof
of `proEtale_unit_leray_chain_formula`. The preflight conservatively classifies additions
of `variable` and `attribute` commands as a possible importer-visible change and requests
this record. There is no changed public signature, definition body, public import, instance,
or exported attribute. No consumer adaptation is required.

Profiling the concrete calculation exposed expensive unfolding of the realization
inverse and terminal comparison. The categorical calculation is now expressed in three
proved private helpers for arbitrary additive functors. Local irreducibility prevents
elaboration from expanding those concrete constructions during specialization. All helper
variables are enclosed in `section Categorical`/`end Categorical`; the attributes are
explicitly local. The existing public theorem is then a direct specialization of the
private generic chain formula. The resulting file compiles under the normal 60-second
limit without profiler or heartbeat overrides.

## Old

The existing sections definition, retained verbatim:

```lean
noncomputable def proEtaleUnitLeraySections (X : Scheme.{u}) :=
  (sfIntrinsicModuleEquivalence X A).inverse ⋙
    Sheaf.Γ (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
```

There were no additional local irreducibility commands or categorical-helper section.

## New

The definition is unchanged:

```lean
noncomputable def proEtaleUnitLeraySections (X : Scheme.{u}) :=
  (sfIntrinsicModuleEquivalence X A).inverse ⋙
    Sheaf.Γ (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
```

After all the existing definitions, and before the private categorical helpers:

```lean
attribute [local irreducible] proEtaleUnitLeraySections proEtaleUnitLerayTerminalIso

universe uC uD uE vC vD vE

section Categorical

variable {C : Type uC} {D : Type uD} {E : Type uE}
  [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  (L : C ⥤ D) (F : D ⥤ C) (G : C ⥤ E) (H : D ⥤ E)
  [L.Additive] [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [F.PreservesKInjectiveComplexes] (a : L ⊣ F) (e : F ⋙ G ≅ H)
```

The section ends before the unchanged public theorem signature. Its three new
private declarations are fully proved. `proEtaleUnitLerayTerminalIso` and every
other pre-existing definition retain their bodies and elaborated signatures.

## Users

Read-only `tools/downstream.py` reports zero downstream Lean modules. Its usage
searches for `proEtaleUnitLeraySections`, `proEtaleUnitLerayTerminalIso`, and
`proEtale_unit_leray_chain_formula` find only the item itself. The module and node
are retained for the DAG parents whose proofs are still unfinished. There is no
withdrawal or dependency change in a parent. No target statement or definition
used by a target changes meaning.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula | G9 | Theorem proof filled; proved private helpers and file-local commands added; all existing public definitions and signatures unchanged. |

## Status

landed 20261020T174757-L-795374 2026-10-20 (merge of deliver/G9/Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula)
