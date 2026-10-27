# AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_zero proof context

## Reason

The proof needs ordinary etale APIs inside a pro-etale namespace, and comparisons
whose endpoints use the cached ordinary category instance of the ordered-data file.
The new namespace, opens, private helpers, local instance priorities and local
transparency attributes guide proof elaboration. They change no public signature,
public definition body, public import or exported attribute. This record documents
the command-level proof context; no target statement or meaning changes.

## Old

The original scope commands are:

```lean
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite
```

The only theorem is `ordinary_counit_zero`, with its original signature and a `sorry`
body. There are no local attributes or auxiliary declarations in this module.

## New

The theorem signature is byte-identical and its proof is complete. The proof adds
private lemmas in the auxiliary namespace
`AlgebraicGeometry.Etale.AffineOrderedCounitZeroAux` and in the theorem's namespace.
It opens categorical limits, the monoidal namespace, the functor scope and the
auxiliary namespace. It raises only the instance-synthesis size bound to 2048,
as the ordered-data module does. Local instance priorities select the existing
ordinary derived-category, inverse-image and sheaf-braiding instance proofs. Local irreducibility
keeps large derived-functor constructions from expanding during endpoint inference.
Local `implicit_reducible` attributes expose the small coordinate and category
wrappers needed by the proof. Transparency checking stays enabled. All these
commands are scoped locally; no instance data or public attributes are introduced.
The exact final commands are in the delivered module.

The three proof imports provide the existing general affine-counit normalization,
the proved comparison of source descents, and the proved naturality of the actual canonical compact-support projection. The original
public import is retained verbatim. Every new helper has a complete proof and is
private; none occurs in a public signature or definition body.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AffineOrderedCounitZero | H5 | Private proof context and proof of the original theorem. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | H1 | Sole direct importer; identical exported signatures, definitions and public imports. |

There are no external users of the new private names. No downstream adaptation is
required because the exported interface is unchanged.

## Status

landed 20261027T012843-L-2339826 2026-10-27 (merge of deliver/H5/Sheaf.Paper.AffineOrderedCounitZero)
