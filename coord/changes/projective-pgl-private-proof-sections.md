# AlgebraicGeometry.PGLLinearization.projective_pgl_stable_quotient

## Reason

The proof needs private helpers for Proj comparison, finite generation and restriction
of stability. The interface scanner detects their scoped namespace and variable commands.
They are confined to closed sections and introduce no public signature, instance,
notation or attribute. Existing declaration signatures and definitions are unchanged.

## Old

```lean
namespace AlgebraicGeometry.PGLLinearization
variable {k : Type u} [Field k] {J Z : Over (Spec (.of k))}
```

The original module has no local helper sections between closureInclusion and the theorem.

## New

```lean
namespace AlgebraicGeometry
private theorem coefficient_proj ...
namespace PGLLinearization
variable {k : Type u} [Field k] {J Z : Over (Spec (.of k))}
section
variable {r : ℕ} {X : Over (Spec (.of k))} {L : X.left.Modules} [L.IsInvertible]
private theorem finiteGeneration ...
end
section
variable {r : ℕ} {X : Over (Spec (.of k))} {L : Z.left.Modules}
private theorem stable_restriction ...
end
```

The snippets describe proof scopes, not a changed public declaration. All public
signatures, including closureOver, closureInclusion, and the item theorem, are verbatim.
The new imports are proof-only imports. They are documented in report.md and the DAG.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectivePGLStableQuotient | T6 | Proof replaced; public signatures identical. |

`tools/downstream.py Sheaf.AlgebraicGeometry.ProjectivePGLStableQuotient --uses
AlgebraicGeometry.PGLLinearization.projective_pgl_stable_quotient` reports zero
importers and only the declaration itself as a textual use. The DAG parent
lem-sfb-unpointed-stable-coarse-projective still needs this theorem; its statement and
unit route are unchanged. No adaptation of another group's module is needed.

## Status

landed 20261023T135420-L-2886120 2026-10-23 (merge of deliver/T6/Sheaf.AlgebraicGeometry.ProjectivePGLStableQuotient)
