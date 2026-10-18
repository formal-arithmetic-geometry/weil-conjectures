# DerivedCategory.isPerfect_and_tensor_homology_vanish_of_maximal_fibres

## Reason

The proof now uses ordinary scalar-extension and tensor comparisons on cochain complexes.
Its statement does not use the sheaf derived-change-of-rings interface. Remove the unused
public import of that interface, together with unused private proof imports. Existing
names, signatures, definitions, and target statements are unchanged.

## Old

```lean
public import Sheaf.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Defs
```

## New

```lean
public import Sheaf.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.RingTheory.Ideal.Quotient.Defs
```

The theorem's original signature is unchanged. This record concerns only the public
import that disappears; new proof dependencies are private imports.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.RlimPerfectComplete | unclaimed | The only downstream module. It already publicly imports `Sheaf.Algebra.Homology.DerivedChangeOfRings` itself. Its original source compiled unchanged against the delivered modules in 5.0 seconds. No adaptation or signature change is needed. |

`tools/downstream.py` lists exactly this downstream module. Its `--uses` search finds no
consumer use of the proved theorem's name outside its own declaration. There is no changed
definition on which a target statement depends, so no target statement review is reopened.

## Status

landed 20261018T062707-L-633788 2026-10-18 (merge of deliver/C1/Sheaf.RingTheory.PseudoCoherentMaximalFibrePerfect)
