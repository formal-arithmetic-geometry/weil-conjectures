## What changed

Preserved the complete existing signature and docstring of
`AlgebraicGeometry.Scheme.Modules.moduleCech_resolution_columns`.
Replaced its sorry by a degreewise proof: degree zero uses the augmentation
identification; positive degrees use zero source homology and zero column homology,
combined through Mathlib's `quasiIso_iff`, `quasiIsoAt_iff_isIso_homologyMap`,
`HomologicalComplex.isZero_single_obj_homology`, and `IsZero.isIso`.
Added two modules, `ModuleCechResolutionColumnZero` and
`ModuleCechResolutionColumnPositive`, containing the two strictly partial claims.
All added proof imports are plain imports. No definition, instance, or existing
public signature was changed.

## Proved and sorry left

Hole closed:
`AlgebraicGeometry.Scheme.Modules.moduleCech_resolution_columns`
(node `lem-sc-module-cech-resolution-columns`).

Holes added, each the whole proof of a public named theorem:

- `AlgebraicGeometry.Scheme.Modules.moduleCech_resolution_column_zero`
  (node `lem-sc-module-cech-resolution-column-zero`): ONLY degree-zero homology,
  with no cohomology-vanishing assumption.
- `AlgebraicGeometry.Scheme.Modules.moduleCech_resolution_column_positive`
  (node `lem-sc-module-cech-resolution-column-positive`): ONLY the target column's
  homology in one positive degree, using only vanishing at that degree and tuple length.

This is a decomposition, not a completed proof of column acyclicity. One original
hole closed and two new holes added: raw net -1 in this delivery. No global ledger
progress is claimed; the maintainer's pinned-baseline ledger determines it.
The abandoned `moduleCech_resolution_column` restatement is not delivered.

## No longer needed

Removed the proof import `Sheaf.Topology.RestrictInjectiveResolution` and its old
proof dependency `lem-sc-ringed-space-restrict-injective-resolution`.
Open cohomology is defined directly as the right derived functor of open sections,
so the positive-degree intermediate computes with the supplied resolution directly.
The old `def-sc-module-cech-comparison` dependency remains: the proof uses its
column construction and augmentation. The restriction module may have other users;
this delivery makes no claim that it leaves the whole targets' import closure.
Removed the proposed new restatement module `ModuleCechResolutionColumn` before delivery.
A scratch compile also confirmed the explicit `Mathlib.Algebra.Homology.SingleHomology`
import was redundant through existing public imports, so it was removed before delivery.

## Where the brief, the DAG or earlier work was wrong

The first proof was only `dsimp; intro ha n; exact moduleCech_resolution_column ...`.
Its helper had the same mathematical content with n moved into the parameters:
this was a restatement, not a strict subargument. Its proposed DAG node was absent.
The first report incorrectly called that a strict substatement and omitted the
new-hole accounting. Both faults are repaired by an actual zero/positive degree split.
The original planned restriction theorem is unnecessary because
`openModuleCohomology` is already the right derived functor of open sections.
The unit `sk-thm-picard-duality` has empty `realized` bindings on the base; this
pre-existing bookkeeping gap is reported, not filled or bypassed by this delivery.

## New nodes

`lem-sc-module-cech-resolution-column-zero` states degree-zero augmentation only;
its complete proof explains the kernel of the injective-resolution differential,
left exactness of sections, restriction of scalars, and products of kernels.
It lives in `Sheaf.AlgebraicGeometry.ModuleCechResolutionColumnZero`.

`lem-sc-module-cech-resolution-column-positive` states target homology vanishing
in one positive degree only; its complete proof computes open-section cohomology
with the given resolution, then chooses coordinate preimages in a product.
It lives in `Sheaf.AlgebraicGeometry.ModuleCechResolutionColumnPositive`.
Both nodes inherit the item's chapter, unit, and blueprint ancestor. Real searches
by LeanFinder, Loogle, grep, and LeanSearch are recorded; LeanSearch was unavailable.
No change records are needed: existing statements and definitions remain identical.

## Second reading by E2

1. Compared the original and delivered module using diff, and checked the theorem
   signature byte for byte from `theorem` to `:=`: identical. Existing docstring,
   universes, namespace, public imports, definitions and instances are unchanged.
   Only the proof and plain proof imports differ. PASS.
2. Compiled all delivered modules with the authorized lcompile launcher. A scratch
   copy with `#print axioms` checks the original theorem and both intermediates;
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` occur. The two
   reported whole-theorem sorries are the only delivered sorries. No axiom, unsafe,
   opaque, implemented_by, extern, or hollow definition occurs. PASS with the two
   explicitly open intermediates.
3. Removed the invalid all-column restatement. Each replacement is a genuine part
   of the proof. Degree zero does not assume vanishing; the positive lemma assumes
   vanishing only for its single degree and tuple length, and says nothing about
   the augmentation. Checked empty indexing type (no tuples, zero products),
   singleton indexing type (one intersection section complex), empty opens (zero
   sections), n=0, p=1, and the trivial resolution of an injective object. The p>0
   hypothesis excludes the false degree-zero version of the positive claim.
   Read Stacks 01EQ, 01ET and 01DZ, and searched Mathlib and both library roots with
   different kernel, product, homology, and right-derived queries. Existing
   `cechComplexFunctor_homology` concerns AddCommGrpCat presheaves; existing
   sheaf-column results concern abelian sheaves, not this module-valued
   resolution. Neither directly supplies these statements. No immediate closure
   of an intermediate was found. PASS.
4. The upper proof splits homological degree, uses Mathlib to close the positive
   source and maps between zero objects, and leaves only the two genuine column
   computations. Public imports provide signature data; all other imports are
   proof-only and used. The No longer needed section accounts for every old
   proof dependency, including the retained comparison definition. The unit route
   is unchanged: both new nodes refine the same column argument below the unit
   level. Empty realized bindings on the base are noted above. PASS.
5. Original node statement and lean signature are unchanged; its proof, proof_deps,
   and proof_origin now describe the degreewise argument exactly. Both new nodes
   include their precise Lean signatures, named theorem, source, complete proof,
   union-of-step proof_deps, searches, creation record, and blueprint ancestry.
   Checked there are no dangling references or new import cycles. PASS.

Second reading changed: removed the restatement and its unused import, introduced
zero-degree and positive-degree intermediate theorems with complete matching nodes,
wrote the actual degreewise reduction, removed the restriction-resolution import,
removed a redundant SingleHomology import, and corrected the report's decomposition accounting.
