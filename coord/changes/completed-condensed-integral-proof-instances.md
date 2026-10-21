# Completed condensed integral proof instances

## Reason

The new proofs require multiplicativity and unitality instances for two private,
explicitly constructed comparison isomorphisms. Both instances have complete proofs.
The helper block also uses the existing elaborator transparency settings so that
categorical expressions with definitionally equal sheaf presentations elaborate
without repeatedly unfolding the coefficient constructions. Preflight classifies
these commands and registrations as an interface change requiring this record.
No existing declaration signature, visibility, attribute, public import, or
non-theorem body changes. No target definition or statement changes meaning.

## Old

The helper isomorphisms, their two instances, and these option commands were absent.

## New

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private instance completedFinitePointIso_isMonHom (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R] [Finite R] :
    IsMonHom (completedFinitePointIso.{u} R).hom := by
  dsimp only [completedFinitePointIso, Iso.trans_hom, asIso_hom]
  infer_instance

private instance completedConstantPresentationIso_isMonHom (X : Scheme.{u})
    (R : Type) [Ring R] : IsMonHom (completedConstantPresentationIso X R).hom := by
  dsimp only [completedConstantPresentationIso, Iso.trans_hom, asIso_hom]
  infer_instance
```

The new helpers and instances remain private. Their conclusions concern only the
specified private comparison maps; they add no generic competing instance for an
existing public construction. The elaboration options govern subsequent proofs
in this module and do not alter an existing mathematical interface.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.CompletedCondensedCoefficients` | K1 | Uses the two proved instances to lift the explicit finite comparison to a ring-object isomorphism. Compiles cleanly. |

`tools/downstream.py Sheaf.Paper.CompletedCondensedCoefficients --uses
completedFinitePointIso_isMonHom completedConstantPresentationIso_isMonHom` checks
the complete downstream import closure. No existing module can refer to these new
private names; no consumer adaptation is required. All existing public signatures
and definition bodies are retained verbatim, so target statement review is not
reopened by a definition change.

## Status

landed 20261021T190519-L-3625615 2026-10-21 (merge of deliver/K1/Sheaf.Paper.CompletedCondensedCoefficients)
