# Private proof context for graph geometric base change

## Reason

The complete graph-transfer proof needs auxiliary adjunctions, categorical diagrams,
functor exactness instances, and component formulas. These are private declarations in
an enclosing section before the original public section. The static interface check
records the added section, namespace, variable, option and attribute commands as a
command-context change. This record documents those commands and the private instances
for independent review. There is no change to a public definition or theorem signature.

## Old

The module had its two public imports, two proof imports, and the following public
context immediately before its one theorem, whose proof was `by sorry`:

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
```

## New

The two public imports and the original public theorem signature stay identical.
The two redundant proof imports are replaced by four private proof imports. A section
before the original public context contains explicitly private auxiliary declarations
and their namespace, universe and variable commands. The section closes before the
original public section. All auxiliary theorems have complete proofs; all auxiliary
data are explicit constructions from existing functors, isomorphisms and adjunctions.

Local irreducibility attributes on existing categorical functors, adjunctions and
factorization isomorphisms keep their concrete implementations out of diagram proofs.
These attributes use `[local irreducible]` and end with the surrounding section or
namespace. Options for elaboration, recursion, heartbeats and linters are likewise
scoped to the section or an individual declaration. No global attribute on an existing
public declaration is changed.

Private instances supply graph geometry, the clopen adjunction unit isomorphism, proper
exchange invertibility, and cached exactness and localization properties. The large
functor and sheaf cache instances are explicitly deregistered before the section ends.
All other added instance declarations are also explicitly private and precede the
public section. No new public instance or declaration is exposed to importers.
The original public theorem now has a complete proof using this private context.

## Users

`Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` (C4) is the only
module using the new private declarations and proof-context commands. The static
interface difference lists only `(commands such as variable, open, notation or attribute)`;
it lists no changed public declaration. Downstream modules cannot name the private
helpers through this import. Existing consumers keep the identical public theorem and
its two unchanged public imports, so no consumer adaptation is necessary. No target's
statement or underlying definitions change.

## Status

landed 20261022T022944-L-766292 2026-10-22 (merge of deliver/C4/Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange)
