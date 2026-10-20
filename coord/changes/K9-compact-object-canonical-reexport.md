# CategoryTheory.IsCompactObject

## Reason

The assigned module has zero holes and duplicates the same fully qualified definition in
`WeilConjectures.CategoryTheory.CompactObject`. The twin-retirement inventory records it as
SUPERSET, postponed because a consumer was in a pending landing. The upstream module has the
identical definition plus the proved Brown representability equivalence. Keeping both local
implementations causes a duplicate-declaration error when their import environments meet.
The retirement withdraws the Sheaf copy and redirects consumers to the canonical upstream module.

## Old

In `namespace CategoryTheory`, with `universe w v u` and the original three public Mathlib
imports (Preadditive.Basic, Limits.Shapes.Products, Algebra.DirectSum.Basic):

```lean
open Classical in
/-- (blueprint: def-pc-compact-object) Let `C` be an additive category with arbitrary coproducts.
An object `K` of `C` is *compact* if, for every set `I` and family `E : I → C`, the canonical map
`⨁ᵢ Hom(K, E i) → Hom(K, ⨁ᵢ E i)`, sending `f` in the `i`-th summand to `f ≫ Sigma.ι E i`, is
bijective (Stacks, Tag 09SM). The direct sum is taken with the classical decidable equality
on `I`. -/
def IsCompactObject {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (K : C) :
    Prop :=
  ∀ (I : Type w) (E : I → C),
    Function.Bijective
      (DirectSum.toAddMonoid (fun i : I => Preadditive.rightComp K (Sigma.ι E i)) :
        (⨁ i : I, (K ⟶ E i)) →+ (K ⟶ ∐ E))

```

## New

The Sheaf copy is withdrawn (listed in deleted.txt), without a compatibility re-export.
All five live consumers replace `public import Sheaf.CategoryTheory.CompactObject` with
`public import WeilConjectures.CategoryTheory.CompactObject`. Their declarations, signatures,
proofs and remaining imports are byte-for-byte unchanged. The upstream definition has the
same fully qualified name, universes, hypotheses and direct-sum comparison body. Its three
Mathlib public imports preserve the old public environment; the additional Brown
representability import and equivalence are canonical upstream API.

The existing DAG node def-pc-compact-object attaches to the upstream module and file.
Its statement, proof dependencies and unit route do not change. No upstream source or target
statement changes. No proof is replaced by sorry and no definition is hollowed, so no failure
note needs to be appended to retire-sheaf-twins-20261020.md.

## Users

A fresh scan of the current Lean sources finds exactly these five consumers. The longer
consumer inventory in the hand-off is historical; its other entries no longer import the
copy. Only the import line is adapted in each consumer, preserving its public visibility.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CompactObject | K9 | Withdraw the duplicate module. |
| Sheaf.CategoryTheory.DerivedModuleRankOneCompact | unclaimed | Redirect public import to twin. |
| Sheaf.CategoryTheory.DerivedModuleRankOneCompactInjective | unclaimed | Redirect public import to twin. |
| Sheaf.CategoryTheory.DerivedModuleRankOneCompactSurjective | unclaimed | Redirect public import to twin. |
| Sheaf.CategoryTheory.DerivedModuleRankOneProperties | unclaimed | Redirect public import to twin. |
| Sheaf.Paper.PurEtaleLisseStratumCompact | unclaimed | Redirect public import to twin. |

The five adapted files are compiled together in dependency order with lcompile.py.

## Status

landed 20261020T144254-L-2260541 2026-10-20 (merge of deliver/K9/Sheaf.CategoryTheory.CompactObject)
