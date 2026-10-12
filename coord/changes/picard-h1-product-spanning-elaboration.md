# AlgebraicGeometry.Scheme.picard_h1_product_spanning elaboration commands

## Reason

The preflight conservatively records changed top-level commands as an interface change.
This delivery adds tensor/direct-sum notation scopes, a namespace-local irreducibility
attribute on scalarCohomology, and options scoped to this theorem. They support its
proof without changing any declaration type, definition, public import, or downstream
elaboration setting. The local attribute expires at the end of the namespace. The
statement still has precisely the original elaborated type. No target definition
review is reopened and no other module needs adaptation.

## Old

The unchanged signature is:

```lean
theorem picard_h1_product_spanning (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))] [IsProper (Y ↘ Spec (CommRingCat.of k))]
    (hX : Function.Bijective (globalSectionsRingHom k (X := X)))
    (hY : Function.Bijective (globalSectionsRingHom k (X := Y))) :
    ∀ c : Sheaf.H (structureSheafAb
      (pullback (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k)))) 1,
      ∃ a : Sheaf.H (structureSheafAb X) 1,
        ∃ b : Sheaf.H (structureSheafAb Y) 1,
          structureSheafCohomologyPullback
              (pullback.fst (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k))) 1 a +
            structureSheafCohomologyPullback
              (pullback.snd (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k))) 1 b =
              c
```

The original file has only `open CategoryTheory CategoryTheory.Limits` and no local
scalarCohomology irreducibility attribute or theorem-scoped elaboration options.

## New

The signature above is preserved verbatim. Added commands:

```lean
open scoped TensorProduct DirectSum
attribute [local irreducible] Modules.scalarCohomology structureSheafAb
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
```

The three options apply only to the theorem. Tensor/direct-sum scopes apply only while
reading this file. All new imports are proof imports; both old public imports stay.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.PicardH1ProductSpanning --uses
picard_h1_product_spanning` finds the assigned module and one direct declaration user.
It also lists 155 transitive module importers; their statements and definitions are
unaffected because no exported declaration or import changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | U3 | Proof replaced; type preserved. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | Its application uses the identical theorem type; no adaptation. |

## Status

landed 20261012T225334-L-1814390 2026-10-12 (merge of deliver/U3/Sheaf.AlgebraicGeometry.PicardH1ProductSpanning)
