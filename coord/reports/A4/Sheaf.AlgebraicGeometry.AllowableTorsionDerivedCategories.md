## What changed

Proved all four theorem instances in
`Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`, with every existing
statement, definition, universe and visibility unchanged. Four fully proved private
instances establish subobject closure, quotient closure, zero membership and extension
closure of allowable-torsion sheaves. Exact geometric stalks reduce these to elementary
abelian-group arguments. For extensions the annihilator is the product of the two
positive allowable annihilators.

Replaced the public import of
`Sheaf.Paper.CohomologyInWeakSerreSubcategory` by its already-proved source interface,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`, which the
public definitions need. Added the proof-only import
`Mathlib.Algebra.Homology.ShortComplex.Ab` for elementwise exactness. Kept the
skyscraper proof import for stalk exactness. Updated the item's node proof and
proof dependencies to match the actual argument; no new nodes or modules were added.
The import-interface record is
`coord/changes/allowable-torsion-derived-imports.md`.
The downstream import-pruning check passes and no downstream source uses the
removed wrapper theorem.

## Proved and sorry left

Closed the four original holes, all in node
`sbc-def-derived-categories-with-allowable-torsion`:

- `AlgebraicGeometry.Etale.allowableTorsionPlusProperty_isClosedUnderIsomorphisms`.
- `AlgebraicGeometry.Etale.allowableTorsionBoundedProperty_isClosedUnderIsomorphisms`.
- `AlgebraicGeometry.Etale.allowableTorsionPlusProperty_isTriangulated`.
- `AlgebraicGeometry.Etale.allowableTorsionBoundedProperty_isTriangulated`.

No sorry remains in the item, and no sorry was added elsewhere. This is a proof,
not a decomposition. Single-file compilation succeeds. Separate `#print axioms`
checks of all four declarations report exactly `propext`, `Classical.choice` and
`Quot.sound`; none depends on `sorryAx`. All Lean lines have at most 100 characters.
The zero-object argument uses annihilator 1, so the empty set of allowable primes
is covered; nonprime members of the set never enter the argument.

## No longer needed

Removed import/module `Sheaf.Paper.CohomologyInWeakSerreSubcategory` and its
statement-only theorem `CategoryTheory.cohomology_in_weak_serre_subcategory`, node
`lem-sbc-cohomology-in-weak-serre-subcategory`, from this proof's dependencies.
The source theorem `DerivedCategory.homologyProperty_isTriangulated` already proves
the required generic fact without sorry. This pruning is local to this item;
other library modules may still use the wrapper. The node's unchanged statement
continues to cite the mathematical criterion, but its revised proof dependencies
record the implementation actually used. No further original imports or planned
helper nodes are needed or removed.

## Where the brief, the DAG or earlier work was wrong

The duplicate generic criterion was recorded as a statement-only wrapper even
though its complete implementation already exists in the source library. Its
source declaration is attached to `prop-constructible-derived-subcategory`; only
that generic declaration is used, with no constructibility assumption. The item's
original proof array was empty; its split-report well-definedness argument supplied
the proof now formalized. There is no false statement or signature correction.
Stalk finite-limit inference needs the AB5 instance shrunk from the abelian-group
universe to the site universe. The unit `sk-rem-rest` has no realized proof steps
to bypass. No target or downstream module was changed.

## Second reading by A4

1. **Signatures and accidental changes.** I diffed the delivered module against the
   repository version. The existing public definitions, theorem signatures, abbreviations,
   universes and visibility are unchanged byte for byte. The only interface changes are the
   declared import pruning and proof-only imports in
   `coord/changes/allowable-torsion-derived-imports.md`; downstream modules do not use the
   removed wrapper declaration.

2. **Proof and axioms.** The delivered module compiles with
   `python3 /home/ubuntu/weil-launcher/lcompile.py --all` and contains no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The four public
   theorem instances have been checked with `#print axioms`; each uses only `propext`,
   `Classical.choice`, and `Quot.sound`. The private closure instances are concrete
   stalkwise proofs, and the empty-prime-set and nonprime-member edge cases are covered.

3. **Statements and proof dependencies.** The node statement is unchanged and the four
   theorem proofs establish exactly the closure and triangulated structures required by that
   statement. The node's `proof`, `proof_deps`, and `proof_origin` now follow the Lean proof:
   exact geometric stalks, the generic derived homology-property theorem, and the derived
   category definitions. No split-off statement or new node was added, and no existing
   library theorem duplicates a delivered declaration.

4. **Pruning and imports.** The old statement-only weak-Serre wrapper is not used. Its public
   import was replaced by the source module that supplies `DerivedCategory.homologyProperty`
   and its generic instances; the short-complex exactness import is proof-only. The removed
   import and node are listed under `## No longer needed`, and the change record lists every
   downstream importer and confirms that no adaptation is required.

5. **Unit route.** The unit `sk-rem-rest` has no realized statement or proof steps, so there
   is no route step to bypass. The delivered construction follows the item's well-definedness
   argument: stalk closure under subobjects, quotients, zero and extensions, then the generic
   homology-property and t-structure instances. The unit and chapter fields in the node are
   unchanged.

The second reading found no mathematical or process defect requiring a repair.
