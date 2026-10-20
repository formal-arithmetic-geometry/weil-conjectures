# CochainComplex.boundedProjective_nonpositiveModel

## Reason

The Sheaf module has zero holes and zero importers. It duplicates a public name already
proved in WeilConjectures, whose stronger conclusion supplies a quasi-isomorphism.
The only actual caller, StrictPerfectClosedPushforwardStalkResolution in WeilConjectures,
already uses the upstream version. Withdraw the unused Sheaf copy under brief step 8d
and attach its DAG node to the upstream declaration. No source-library file changes.

## Old

In Sheaf.Algebra.Homology.BoundedProjectiveNonpositiveModel:

```lean
theorem boundedProjective_nonpositiveModel
    {C : Type u} [Category.{v} C] [Abelian C]
    (L : CochainComplex C ℤ)
    (hbound : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (L.X j))
    (hproj : ∀ j : ℤ, Projective (L.X j))
    (hexact : ∀ j : ℤ, 0 < j → IsZero (L.homology j)) :
    ∃ Q : CochainComplex C ℤ, ∃ a : ℤ,
      (∀ j : ℤ, j < a → IsZero (Q.X j)) ∧
      (∀ j : ℤ, Projective (Q.X j)) ∧
      (∀ j : ℤ, 0 < j → IsZero (Q.X j)) ∧
      (∀ j : ℤ, Nonempty (Q.homology j ≅ L.homology j))
```

## New

The existing, unchanged declaration in
WeilConjectures.Algebra.Homology.BoundedProjectiveNonpositiveModel:

```lean
theorem boundedProjective_nonpositiveModel
    {C : Type u} [Category.{v} C] [Abelian C]
    (L : CochainComplex C ℤ)
    (hbound : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (L.X j))
    (hproj : ∀ j : ℤ, Projective (L.X j))
    (hexact : ∀ j : ℤ, 0 < j → IsZero (L.homology j)) :
    ∃ Q : CochainComplex C ℤ, ∃ a : ℤ,
      (∀ j : ℤ, j < a → IsZero (Q.X j)) ∧
      (∀ j : ℤ, Projective (Q.X j)) ∧
      (∀ j : ℤ, 0 < j → IsZero (Q.X j)) ∧
      ∃ ι : Q ⟶ L, QuasiIso ι
```

The Sheaf module is withdrawn with deleted.txt. The DAG statement is strengthened to
record the actual quasi-isomorphism already used by the existing caller. The exact old
conclusion follows by taking asIso of HomologicalComplex.homologyMap in every degree;
this implication was separately compiled in the sandbox verification directory.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.BoundedProjectiveNonpositiveModel
--uses CochainComplex.boundedProjective_nonpositiveModel` reports zero downstream
modules and only the declaration's own file as a textual use. A full Lean import scan
also finds no importer of the Sheaf module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.BoundedProjectiveNonpositiveModel | X8 | Withdraw unused duplicate. |
| WeilConjectures.Algebra.Homology.BoundedProjectiveNonpositiveModel | not adapted | Preserved verbatim; canonical node attachment; independently compiled. |
| WeilConjectures.AlgebraicGeometry.StrictPerfectClosedPushforwardStalkResolution | not adapted | Already uses the stronger theorem; independently compiled unchanged. |
| WeilConjectures | not adapted | Already publicly imports the canonical upstream module; unchanged. |

The sole DAG citer is lem-sc-strict-perfect-closed-pushforward-stalk-resolution; its
proof text now explicitly mentions the homology maps, following the existing Lean.
No target definitions or statements change, and no target semantic review is reopened.

## Status

landed 20261020T144311-L-2264102 2026-10-20 (merge of deliver/X8/Sheaf.Algebra.Homology.BoundedProjectiveNonpositiveModel)
