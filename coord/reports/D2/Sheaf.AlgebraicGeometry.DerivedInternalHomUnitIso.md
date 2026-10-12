## What changed

Proved `AlgebraicGeometry.derivedInternalHom_unit_iso` without changing its signature.
The proof curries `derivedInternalHom_comparison` at the single unit complex, combines
its comparison with the unit Hom-complex isomorphism and the localized resolution
natural isomorphism, and descends the result using fully faithful precomposition by Q.
The associators, unitors, resolution naturality, and descent are complete Lean proofs.
Updated the existing node to match this argument. Added one simpler intermediate
module, `Sheaf.Algebra.Homology.HomComplexUnitIso`, containing the complex-level step.

## Proved and sorry left

Closed: `AlgebraicGeometry.derivedInternalHom_unit_iso` (1 original hole).
Added: `CategoryTheory.homComplex_unit_iso`, the sole remaining named sorry in this
delivery (node `lem-sc-hom-complex-unit-iso`). It asserts an underived isomorphism of
complex functors on any small ringed site, with no derived category or injective
resolution assumption. This is a decomposition: 1 hole closed and 1 hole added,
net zero holes. The existing `derivedInternalHom_comparison` remains an imported
planned dependency; no additional sorry is added there. Both delivered files compile
cleanly through lcompile.py.

## No longer needed

Removed the direct proof imports `Sheaf.Algebra.Homology.HomComplex` and
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom` from the item.
The first is replaced by `Sheaf.Algebra.Homology.HomComplexUnitIso`; both remain
transitively needed, so no whole module is pruned. The old direct proof edges to
`def-pur-hom-complex` and `def-pur-sheaf-hom` move to the new intermediate node;
neither node is obsolete. The new module publicly imports HomComplex, SingleFunctors, and the upstream
Sheaf.Abelian module for the zero-object instance needed by the single complex.
Evaluation at one is already proved by `SheafOfModules.homObjUnitIso` in the
source's InternalHomFree module, now imported only privately for the proof API. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original steps 1-2 described a true complex-level calculation but had no named
interface for it. This delivery isolates exactly that calculation, rather than
restating the derived conclusion. An attempted direct proof confirmed the sheaf
evaluation naturality and the product argument for a family with just one nonzero
factor; elaborating the chosen Hom-complex projections and their differential
compatibilities remains for the lower item. Those experiments are not delivered.
The existing HomComplex is a real construction, with homComplex_exists proved.
No existing statement or definition was changed. Edge cases checked for the new
statement: zero complex, empty site, zero coefficients, and arbitrary shifts of
the target; every construction is degreewise, so none requires boundedness.
LeanFinder, Loogle, and grep searches found no exact derived or complex-level
unit theorem. LeanSearch was attempted and returned Internal Server Error;
its unavailability is recorded without a verdict in the new node.

## New nodes

`lem-sc-hom-complex-unit-iso`, in
`dag/nodes/sec-picard-framework/lem-sc-hom-complex-unit-iso.json`, is the original
steps 1-2: evaluation at one as a natural chain isomorphism. Its module is
`lean/Sheaf/Algebra/Homology/HomComplexUnitIso.lean`, with source and a complete
four-step natural-language proof in its docstring. The new statement is strictly
below the derived localization and resolution argument. No change records needed.


## Second reading by D2

1. Compared the item's entire module with the repository using diff. PASS:
   the existing declaration's signature and docstring are byte for byte
   unchanged; only its proof and private proof imports change. No definition
   is changed, and no change record is required.
2. Compiled both delivered modules in import order through lcompile.py. PASS:
   the only textual sorry is CategoryTheory.homComplex_unit_iso, exactly the
   whole proof of a public named theorem with source, complete proof docstring,
   and matching node. No axiom, unsafe, opaque, implemented_by, extern, or hollow
   definition is introduced. Scratch #print axioms checks for both declarations
   show only propext, Classical.choice, Quot.sound, and sorryAx, the last from
   the documented open dependency and split statement. The derived theorem is
   a completed reduction, not an axiom-free closure.
3. Read the split statement against homComplex_exists and homObjUnitIso. PASS:
   all nonzero source degrees give zero internal Hom factors; projection to
   zero and evaluation at one are inverse to the specified family construction.
   The source differential is zero, so the target differential and every chain
   map commute with evaluation. The zero target, empty site, zero ring, and
   arbitrary shifts of the target introduce no exception or boundedness need.
   The split theorem has neither derived localization nor injective replacement,
   so it is strictly a part of the original argument. Independent LeanFinder,
   Loogle, and grep searches, plus repository searches, found no duplicate.
   Mathlib's fromSingleEquiv concerns external cochains and does not supply this
   sheaf-valued chain isomorphism. Closing the split theorem requires the product
   projection and chain-compatibility construction; it is not a few-minute fix.
4. Checked the proof from the top, its curry/whiskering isomorphisms, resolution
   naturality and fully faithful localization descent. PASS: it uses the planned
   derivedInternalHom_comparison and the split complex-level step, with genuine
   Lean proofs of the glue. No shorter existing theorem was found. The report
   accounts for all old proof_deps: def-pur-derived-internal-hom remains, while
   def-pur-hom-complex and def-pur-sheaf-hom move below the new node and are not
   obsolete. No whole module is pruned. sk-thm-picard-duality.json has empty
   realized statement and step lists; its route and records are unchanged.
5. Compared both node records with the Lean modules. PASS: the existing node
   changes only proof, proof_deps and proof_origin; its steps and dependency
   union match the delivered proof. The new node has source, full argument,
   statement dependencies, proof dependencies, blueprint ancestry, creation
   record, status split, and the exact Lean statement and module record.

Changed the new module's imports: use the upstream Sheaf.Abelian infrastructure
publicly and make InternalHomFree a plain proof import. Mathlib's smaller
Sheaf.Abelian import alone did not provide the required zero-object instance;
that trial was reverted. Added independent search evidence to the new node and
corrected the import account in this report. No proof or statement was rewritten.
The delivery remains a decomposition: one original hole closed, one lower hole
added, net zero; no whole module pruned.
