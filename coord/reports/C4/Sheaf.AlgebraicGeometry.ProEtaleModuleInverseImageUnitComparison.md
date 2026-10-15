## What changed

The item theorem now chooses the canonical module adjunction supplied by the new
canonical-unit intermediate theorem.  It proves the arbitrary-adjunction case by the
left-adjoint uniqueness isomorphism and the naturality of the abelian hom equivalence.
The canonical intermediate theorem is stated in
`lean/Sheaf/AlgebraicGeometry/ProEtaleModuleInverseImageCanonicalUnit.lean` and imported by
the item module.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.proEtaleModuleInverseImage_unitComparison_isIso`.
The new theorem `AlgebraicGeometry.Scheme.proEtaleModuleInverseImage_canonicalUnitComparison`
remains `sorry`; it is the strict AsSmall transport and canonical unit comparison split
off from the arbitrary-adjunction uniqueness argument.  Its node is
`new-lem-weil-pbc-proetale-module-canonical-unit`.

## No longer needed

No imports or existing DAG nodes were removed.  The item proof uses all three original
proof dependencies, plus the new canonical-unit node.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the strict AsSmall canonical adjunction construction and
the separate arbitrary-adjunction uniqueness argument into one hole.  The latter is a
short complete category-theoretic reduction; the former is recorded as the named
intermediate theorem above.

## New nodes

`new-lem-weil-pbc-proetale-module-canonical-unit`: canonical adjunction and invertible
underlying unit mate, with source and proof plan recorded in its node file.

## Earlier second reading (a previous round; superseded)

The canonical-unit split is a strict intermediate statement: it fixes the canonical adjunction and supplies only its underlying mate isomorphism. The item proof combines it with the independently proved adjunction uniqueness identity; no target signature is changed.

## Second reading by C4

1. **Signatures and visibility.** Compared the item module with the repository version. The
   target theorem's declaration is byte-for-byte unchanged; the only interface addition is the
   separately named canonical-unit theorem and its matching node. The canonical theorem is
   placed in a new module with the required module/import/section structure.
2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py`; both compile without
   errors or warnings. The item theorem contains no `sorry`, and the only remaining `sorry` is
   the named canonical-unit theorem, recorded by
   `new-lem-weil-pbc-proetale-module-canonical-unit`. No forbidden declaration or hollow
   definition was added. The item proof uses the canonical mate, adjunction uniqueness, and
   hom-equivalence naturality to show the arbitrary supplied unit is invertible.
3. **Statements and split.** The canonical-unit statement is a true, strictly smaller
   intermediate assertion: it fixes one adjunction and asserts only the componentwise
   invertibility needed by the item proof. Its docstring, node, source, proof plan, and
   dependencies identify the strict AsSmall/module-action construction that remains open.
   No existing Mathlib or Sheaf declaration duplicates it.
4. **Pruning and route.** Removed the target's now-unused proof-only imports of
   `ProEtaleModelRingPresentation` and `ModuleInverseImageAdjunction`; the canonical-unit module
   retains those imports for its stated construction. Removed the corresponding old proof
   dependencies from the item node, while retaining them transitively through the canonical-unit
   node. The unit route is preserved through the canonical-unit intermediate node.
5. **DAG agreement.** The item node's proof steps now use exactly the canonical-unit node, and
   its proof origin records the uniqueness/naturality route implemented in Lean. The new node's
   Lean declaration and statement agree with its JSON record.

Changed the target imports, item-node proof route/dependencies, and this report only; no target
statement or existing declaration signature was changed.
