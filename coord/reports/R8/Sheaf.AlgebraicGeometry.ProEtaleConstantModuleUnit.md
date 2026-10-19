## What changed

Replaced `AlgebraicGeometry.Scheme.proEtaleConstantModuleUnit_existsUnique`'s hole
by the associated-module-sheaf construction from the existing Mathlib APIs.
Private helpers restrict the coefficient-ring unit module to fixed scalars, extend
the constant scalar map by fixed-scalar sheafification, and prove that extension
is an isomorphism using local injectivity and local surjectivity. The module
sheafification adjunction then gives the intrinsic isomorphism. Its unit identity
proves the required normalization, and fixed-scalar sheafification extensionality
proves uniqueness from the normalization on constants.

All existing declaration signatures and public definitions are unchanged.
No imports were added. The existing node now records the three steps of the
implemented sheafification argument and their dependencies. The zero ring and empty scheme require no exceptional
choices: all constructions and universal properties apply to them as stated.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.proEtaleConstantModuleUnit_existsUnique`
(node `def-pur-proetale-constant-module-unit`). One original hole, zero remaining
holes in the item module, zero holes added and zero split off.

Validation: the item compiles through `lcompile.py` with no errors or warnings
(6.0 seconds). The retained attempt needed an explicit universe on module
sheafification and explicit natural-transformation, module-map and linear-map
extensionality in the uniqueness argument. Delivery preflight is checked below
by the delivery tool.

## No longer needed

None. All three original public imports remain necessary for the public
statements or definitions. No planned dependency has been bypassed and no
module is withdrawn. No new intermediate obligations were introduced.

## Where the brief, the DAG or earlier work was wrong

The node had no numbered proof steps or proof dependencies; this delivery fills
those records with the actual argument. The existing
normalization docstring supplies the argument; Mathlib already provides both
sheafification universal properties and the local-bijectivity criterion, so no
new mathematical statements are needed.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
