## What changed

The upstream review #1428 duplicate repair is verified. The canonical declaration
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf` remains in
`Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf`; the companion
`TorsorEquivariantPresheafSheaf` module is only a public compatibility import and
contains no duplicate declaration or copied gluing proof. I clarified the retained
theorem's docstring to identify it as the canonical implementation. The proof and
signature are unchanged and compile successfully.

The existing landed change record is
`coord/changes/equivariantModulePresheafSheaf-duplicate.md`. Downstream callers use
the retained theorem, and no additional declarations or imports are needed.

## Proved and sorry left

Holes closed: none (0 of 0 direct sorries). Holes added: none. The retained theorem
has a complete proof and the assigned module contains no `sorry`.

## No longer needed

The duplicate scalar-restricted theorem and its private copy-pasted gluing
implementation are no longer needed and were removed by the landed repair. No
additional nodes or imports are pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The repair was already landed before this worker started, so the substantive source
change was present in the repository. The verification tool nevertheless requires a
changed assigned module for a delivery; the docstring clarification supplies that
minimal source change without altering any interface or theorem statement. The
prescribed dry run succeeds except for the expected missing second-reading section,
which is written by the independent reader.

## Second reading by X3

1. I compared the delivered module with the repository version. The theorem signature,
all private helper signatures, imports, and definitions are unchanged; the only source
change is a clarifying docstring sentence. The companion duplicate-removal change is
documented by `coord/changes/equivariantModulePresheafSheaf-duplicate.md`.

2. I compiled the sandbox module with `lcompile.py`. It compiles without errors or
warnings, contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`, and `#print axioms` for the target reports only `propext`,
`Classical.choice`, and `Quot.sound`.

3. The retained declaration has the exact node statement and no new split-off
statements were added. The existing proof is a direct construction through the
continuous-function sheaf, the equivariance subfunctor, and the module forgetful
functor; no duplicate declaration or restatement was introduced. Searches recorded by
the delivery found no existing torsor-specific theorem that could replace it.

4. The proof follows the node's three stated steps and keeps the unit route: continuous
functions after etale pullback, local equivariance, then natural-isomorphism transport
and reflection through the module forgetful functor. The import remains the required
`TorsorAssociatedModule`; there are no unused imports or prunable proof dependencies.

5. The node's `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof, and
the unit's `realized` fields are unchanged. No target statement or definition changed.

I changed only the canonical theorem's docstring to identify the retained implementation
explicitly, then verified compilation and axioms as above. No holes were closed or added,
and no modules or nodes were pruned.
