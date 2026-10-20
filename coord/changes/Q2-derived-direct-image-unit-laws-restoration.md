# AlgebraicGeometry.derivedDirectImageComposition_unit_laws

## Reason

Restore the assigned module from its quarantine archive after the upstream module-system
sync. Its statement uses Scheme, sheaves of modules, and the derived functors imported
privately by the archived file; the rework entry records the resulting unknown identifiers.
The statement needs a public import of SchemeDerivedDirectImage, which already publicly
imports DerivedCategory. The theorem signature is byte-for-byte unchanged. Its sole proof
hole is now filled. All new helpers are private and proved, with no change to source-library
modules or to shared definitions.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
```

Only SchemeDerivedDirectImage is public; the other imports supply private proofs.
The private identity comparison uses the natural-isomorphism action of derivation rather
than transporting an entire derived functor through an equality. Its defining construction
is irreducible, with a proved factorization API. No existing definition is changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnitLaws | Q2 | Restored, visibility fixed, theorem proved with unchanged signature. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition | No current holder in shared claim records; quarantined | Its existing application of derivedDirectImageComposition_unit_laws remains valid with the unchanged signature; no adaptation. |

The read-only downstream tool reports the assigned module as unknown because it is absent
from lean/. A search including quarantine/ finds the parent above, whose call at line 141
uses this theorem with the existing c0 and hc0. The parent remains quarantined for its own
separate rework assignment and is not withdrawn or modified here. There are no current
Lean importers in the live source tree. The original quarantine archive is retained.

## Status

landed 20261020T153019-L-2863809 2026-10-20 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnitLaws)
