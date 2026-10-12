## What changed

Closed `CategoryTheory.brownHomRepresentabilityLocallySmall` without changing its signature.
Both categories are replaced by their Mathlib `ShrinkHoms` models. Two new, fully proved
transport lemmas construct triangulated structures and preserve compact generation. The
existing `brownRepresentabilityRightAdjoint` is applied in universe w. Mathlib adjunction
transport cancels the equivalences and supplies the requested objectwise representation.
The two new modules are proof-only imports of the original module.

## Proved and sorry left

Closed the item's one hole: `CategoryTheory.brownHomRepresentabilityLocallySmall`.
Also proved the new declarations `CategoryTheory.triangulatedEquivalenceTransfer` and
`CategoryTheory.compactGenerationEquivalence`. No holes added and no sorry left in any
of the three delivered modules. The existing Brown right-adjoint theorem's dependencies
remain as before; this delivery proves the upper statement from that existing theorem.
All three modules compile without warnings using lcompile.py.

## No longer needed

No original imports removed and no DAG nodes pruned. The new compact-generation module
uses the narrower public `Mathlib.CategoryTheory.Shift.CommShift` import in place of
`Mathlib.CategoryTheory.Triangulated.Functor`. The old direct proof dependencies
`def-pc-compactly-generated` and `def-weil-triangulated-category` are now used through
the transport lemmas; their definitions and modules remain required for the statements. The existing Brown right-adjoint dependency
remains required. The original proof plan's manual transport of natural Hom bijections is
handled by Mathlib's adjunction and equivalence tools; no additional lemma is needed for it.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original DAG plan did not name declarations implementing
structure transfer and compact-generation transfer across equivalences. These two steps
are now stated and fully proved. The unit route is unchanged.

## New nodes

`lem-pc-triangulated-equivalence-transfer` records the fully proved transport theorem in
`Sheaf.CategoryTheory.TriangulatedEquivalenceTransfer`. It constructs the additive structure
via full faithfulness, the shift by conjugation, and the distinguished triangles via
Mathlib localization at isomorphisms. No data comes from an unproved existence theorem.

`lem-pc-compact-generation-equivalence` records the fully proved theorem in
`Sheaf.CategoryTheory.CompactGenerationEquivalence`. Additive Hom bijections give a
commuting square between the two canonical direct-sum maps. Weak generation follows from
preservation of zero objects, faithfulness, the coproduct comparison, and shift compatibility.
The proof does not choose an index, so the empty generating-family case is covered.

## Second reading by H1

1. Unchanged interface: PASS. Diffed the item against the repository. Its existing
   declaration signature and docstring are byte-for-byte unchanged; only proof-only
   imports and the proof body were added. The other two modules are new. No definition
   or target statement changed and no change record is needed.
2. Proof and trust: PASS. Compiled all three modules in import order with lcompile.py,
   without errors or warnings. There is no sorry in the delivered code and no forbidden
   declaration or hollow definition. Scratch copies with `#print axioms` show only
   propext, Classical.choice and Quot.sound for both helpers. The item additionally
   depends on sorryAx through existing Brown representability dependencies, not a new
   hole. The transferred structures are explicitly constructed using full faithfulness,
   induced shifts and localization at isomorphisms; no arbitrary object is selected from
   an unproved existence theorem.
3. New statements: PASS. Both new theorems are completely proved, not split-off holes
   or restatements of Brown representability. Read the Stacks definitions of triangulated
   categories, compact objects, generators and compact generation and proposition-brown
   in the local derived.tex source. Structure transport uses the unit to conjugate shifts,
   completes triangle maps for the isomorphism system, and obtains the inverse's exactness
   from the unit isomorphism. Compact transport identifies the direct-sum map via additive
   Hom bijections and the preserved-coproduct comparison; faithful additive functors and
   invertible comparisons preserve the nonzero generator map. Checked empty indexing
   families (no index is selected), the zero category, identity equivalences, and unrelated
   object/Hom universes. Repeated LeanFinder, Loogle and grep searches with transport and
   additive-equivalence queries, and searched Mathlib, upstream and lean/Sheaf. Mathlib's
   Equivalence.IsTriangulated constructors assume pre-existing triangulations; they do
   not construct the transported structure. Its generators predicates do not replace
   the project's direct-sum compact-generation predicate. No duplicate theorem found.
4. Route and pruning: PASS after report repair. The proof starts at the item, constructs
   small-Hom models, applies the existing Brown right-adjoint theorem in universe w,
   and cancels equivalences using Mathlib adjunction lemmas. All project imports remain
   needed. Narrowed the new compact-generation module's public triangulated-functor import
   to Shift.CommShift, which its statement actually uses. The old definition dependencies
   are now mediated by the proved helpers, not pruned from the import closure; recorded
   both explicitly under No longer needed. The unit's realized record is untouched
   (this item is below its statement and steps), and no unit route is bypassed.
5. DAG agreement: PASS after metadata repair. The item records structure transport,
   compact-generation transport, Brown and adjunction cancellation in the same order as
   Lean. Its proof_deps are exactly the two helpers and Brown. New nodes have sources,
   creation records, searches, parent provenance, chapter/unit and matching declarations.
   Replaced both new lean.statement records with the actual verbatim signatures; notably
   the structure-transfer record now retains the newline terminating its `let` expression.

Second reading changed the compact-generation import, both new nodes' verbatim signature
records, and the pruning explanation above. No proof body or existing statement changed.
One original hole closed, zero holes added; this is a proof from existing open dependencies,
not a decomposition into new holes. No modules pruned.
