# ContAction.nonempty_forget_iso_of_exact_finite

## Reason

The proof establishes the Galois-category and fibre-functor hypotheses with private
helper instances. Two elaborator compatibility options are enabled for this module.
The static interface scanner classifies added commands as a possible interface change
and therefore requires this record. No existing public signature or public import changes.
No target statement or definition changes meaning.

## Old

There are no elaborator-option commands between `open scoped FintypeCatDiscrete` and
`namespace ContAction`. The public theorem has the following signature:

```lean
theorem nonempty_forget_iso_of_exact_finite {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ContAction FintypeCat.{u} G ⥤ Type u)
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [∀ X : ContAction FintypeCat.{u} G, Finite (H.obj X)] :
    Nonempty ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl) ≅ H)
```

## New

The theorem signature above is unchanged, with its proof supplied. The added commands are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
```

These options control elaboration of this file; they do not export declarations or
change the meaning of existing declarations. The new helpers, including every new
instance, are explicitly `private`. Their types and proofs support the theorem within
this module. No new public instance is declared. The dry run compiled the file and its
axiom probe before the static scanner requested this record.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Galois.ExactFiniteGsetsForgetful | F3 | item; theorem proof completed; private helpers and elaborator options added |
| Sheaf.Paper.FibreFunctorBasepointTransport | A3 | sole downstream importer; unchanged public theorem signature and public imports; no adaptation needed |

`tools/downstream.py` lists the latter as the only downstream module. Its `--uses`
search lists only the item itself as a textual user of the theorem; the downstream
module currently imports this item without referring to the theorem by name.
No consumer file is edited and no target review is reopened.

## Status

landed 20261019T132228-L-1204169 2026-10-19 (merge of deliver/F3/Sheaf.CategoryTheory.Galois.ExactFiniteGsetsForgetful)
