# AlgebraicGeometry.Scheme.pbcRationalScalarHom_exists

Module: `Sheaf.Paper.PbcScalarExtension` (held by X5, this delivery's own item).

## Reason

The scalar Hom proof needs the intended tensor-product module instances, and
elaboration must avoid repeatedly expanding the chosen fraction-field equivalence.
These are local proof elaboration changes, not changes to public signatures.

## Old

The file had no local irreducibility attribute for
`AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv`. The theorem
`pbcRationalScalarHom_exists` had its original signature and proof `:= by sorry`,
without a surrounding section that disabled `ULift.module`.

## New

The new local commands are:

```lean
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
```

and, around the rational scalar Hom theorem only,

```lean
section
attribute [-instance] ULift.module
-- The original theorem signature, with its completed proof.
end
```

The proof of `AlgebraicGeometry.Scheme.pbcRationalScalarHom_exists` uses a new
local `section` containing `attribute [-instance] ULift.module`. This removes
an ambiguous scalar action while elaborating tensor products over the lifted
valuation rings. The section ends immediately after the theorem. The file
already uses the same scoped command for its other tensor-Hom proofs.

The canonical `pbcRationalCoefficientEquiv` is also marked locally irreducible
while elaborating this module. Its existing definition is unchanged; the proof of
its integral-coefficient formula explicitly unfolds it once. Subsequent proofs use
its ring-equivalence API, avoiding repeated expansion of its chosen construction.

New private helper proofs use local transparency options. Two ordinary pullback
coherence theorems are moved before their direct-image consequences, which now
follow by mates. Their signatures and proof holes are unchanged. The finite
constant-comparison private helpers are placed before both proofs that use them.

All existing public declaration signatures, definitions, instance declarations,
public imports, module-level instance commands and their scopes are preserved.
There is no new public declaration, statement change or definition change, and no
consumer requires adaptation. New proof imports remain private. The full module
compiled without warnings through lcompile.py in 51.9 seconds.

The static preflight requests this record because it detects the extra local
section/attribute commands. This record documents proof elaboration only; it
does not authorize any change to the targets or their meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PbcScalarExtension | X5 | Local proof elaboration and five completed proofs; public interface unchanged. |

`tools/downstream.py Sheaf.Paper.PbcScalarExtension --uses
pbcRationalScalarHom_exists` lists only this module as a declaration user.
The new commands are local and expire with their scopes. Importers receive the
same public signatures, definitions and instances, so no consumer adaptation is
required. No module held by another group is edited.

## Status

landed 20261021T233808-L-863486 2026-10-21 (merge of deliver/X5/Sheaf.Paper.PbcScalarExtension)
