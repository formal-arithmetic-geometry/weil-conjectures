# Module.finite_flat_restriction_projective

## Reason

The human-authorized retirement row in coord/retire-items.tsv assigns this Sheaf copy
for replacement by WeilConjectures.Algebra.FiniteFlatRestrictionProjective.
The upstream theorem has the identical statement under the canonical name
Module.finitePresentation_and_projective_of_flat. No current Lean module imports
the copy or uses its theorem, including the quarantined source modules.

## Old

In Sheaf.Algebra.FiniteFlatRestrictionProjective:

```lean
theorem finite_flat_restriction_projective
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite A B] [Algebra.FinitePresentation A B] [Module.Flat A B]
    [Module.FinitePresentation B M] [Module.Projective B M] :
    Module.FinitePresentation A M ∧ Module.Projective A M
```

## New

Withdraw lean/Sheaf/Algebra/FiniteFlatRestrictionProjective.lean through deleted.txt.
Reattach lem-pc-finite-flat-restriction-projective to the existing proved upstream
theorem without editing any upstream source:

```lean
theorem finitePresentation_and_projective_of_flat
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite A B] [Algebra.FinitePresentation A B] [Module.Flat A B]
    [Module.FinitePresentation B M] [Module.Projective B M] :
    Module.FinitePresentation A M ∧ Module.Projective A M
```

A separate scratch file imports only the upstream module and proves the entire
old signature by applying the canonical theorem, with independent universes u, v, w.
Its axiom check reports exactly propext, Classical.choice and Quot.sound.
No hypotheses, conclusions or definitions change, including for the zero ring or
zero module; no nontriviality assumptions are introduced.

## Users

The downstream tool reports zero downstream modules and only the defining module
as a user of the old qualified name. Scans of lean/Sheaf, lean/WeilConjectures and
quarantine find no external use or importer. No consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.FiniteFlatRestrictionProjective | B3 | duplicate withdrawn |

The DAG parent lem-pc-finite-flat-pushforward-locally-free retains its dependency
on lem-pc-finite-flat-restriction-projective: that node now points at the identical
upstream statement. The unit sk-the-hilbert-functor--definition-1 has no realized
steps using the copy. The mathematical route and all dependency nodes stay intact.
No target definition or interpretation changes.

## Status

landed 20261020T144236-L-2257931 2026-10-20 (merge of deliver/B3/Sheaf.Algebra.FiniteFlatRestrictionProjective)
