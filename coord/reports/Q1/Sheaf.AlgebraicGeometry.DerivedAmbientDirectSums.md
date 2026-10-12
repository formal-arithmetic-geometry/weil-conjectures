## What changed

Kept the signature of `AlgebraicGeometry.derivedAmbientDirectSums` byte for byte and
proved its conjunction from two strict intermediate clauses in new modules.
The second reading proved `derivedAmbientDirectSumsHomology` completely by exact
coproducts, short-complex homology, and the localization homology comparison.
`derivedAmbientDirectSumsCofan` retains the K-injective universal-property obligation.
Both new modules use public imports only for their signatures and plain imports for
proof infrastructure. Removed the unused proof import of DirectImage.Basic from the item.

## Proved and sorry left

`AlgebraicGeometry.derivedAmbientDirectSums` has a complete reduction proof, but still
uses `sorryAx` through its coproduct universal-property clause.
`AlgebraicGeometry.derivedAmbientDirectSumsHomology` is fully proved; its two private
exact-colimit helpers are fully proved as well.
The only sorry delivered is `AlgebraicGeometry.derivedAmbientDirectSumsCofan`, node
`lem-pc-derived-ambient-direct-sums-cofan`, with source and full proof in its docstring.
Thus 1 of 1 original obligations is reduced, 1 of 2 new public obligations is closed,
and 1 remains split off. This is not a sorry-free proof of the original theorem.

## No longer needed

Removed the item's unused proof import
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`.
The item's original direct proof edge to `lem-pc-scheme-modules-grothendieck-abelian`
is replaced by the two intermediate nodes. That prerequisite remains needed below both
clauses: the homology proof directly uses `SheafOfModules.isGrothendieckAbelian` from
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`, the underlying
upstream theorem used by `Scheme.Modules.isGrothendieckAbelian`.
No node or module in the transitive proof route is pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker claimed there was no usable homology-colimit proof in the library.
A second search found private exact-colimit helpers in
`Sheaf.AlgebraicGeometry.FiniteEtaleCechFilteredColimit`; adapting that proof closes
the homology clause, without an additional open statement.
The new cofan node had reversed the direction of its legs in prose; repaired it to
`E_i → Q(∐ K_i)`. Both new docstrings originally lacked proofs in words; repaired them.
The first report claimed the original proof import was removed, although it remained;
it is now actually removed. The source of 08DT is Derived Categories of Schemes,
not Perfect Complexes; verified against https://stacks.math.columbia.edu/tag/08DT.
Existing node statement/source fields were preserved; its proof_origin now points to
the verified tag. No existing declaration, definition, or target statement changed.

## New nodes

`lem-pc-derived-ambient-direct-sums-cofan` states only the coproduct universal property,
a strict part of the original target, supported by Stacks 07D9 (1)-(2). It remains open.

`lem-pc-derived-ambient-direct-sums-homology` states only the cohomology comparison,
a strict part of the original target, supported by the proof of Stacks 08DT. It is proved.
Both have complete node records and their Lean signatures recorded verbatim.
No change records are necessary.

## Second reading by Q1

1. Compared every delivered module with the repository. The sole existing module changes
   only a proof and proof-only imports. Its signature is byte for byte unchanged; no
   definitions or target statements changed. The two other modules are new.
2. All three files compile locally without errors or warnings. The sole sorry is exactly
   the named public cofan theorem. No axiom, unsafe, opaque, implemented_by, extern, hollow
   definition, or anonymous sorry occurs. Scratch #print axioms checks confirm the
   homology theorem uses only the permitted standard axioms, while the item and cofan
   theorem additionally use sorryAx through the explicitly reported open obligation.
3. Read each split statement against its source: Stacks 07D9 and 08DT. Empty/singleton
   index families, arbitrary representatives, zero complexes, and all integer degrees
   satisfy the argument. Neither clause repeats the whole target. Repeated searches
   with leanfinder, loogle and grep, plus rg across the upstream and Sheaf trees. No
   public exact duplicate was found; DerivedModuleDirectSums is for ModuleCat, not
   module sheaves. Found and adapted the private exact-colimit proof to close homology.
4. The item first reduces to its two independent clauses. Homology now takes the shorter
   proved upstream/exact-colimit route. Its public imports supply its signature, while
   additional proof imports are plain. Removed the unused item proof import and listed
   its original dependency edge above; no transitive node is pruned. Read the unit
   sk-thm-picard-duality and its realized fields: neither the unit nor its route changes,
   and the original direct-sums node remains the point used by its ancestors.
5. Read all three node records with the Lean. The item's proof and proof_deps name
   exactly the two clauses it applies. New nodes retain the Grothendieck prerequisite
   and describe the actual homology proof or the remaining K-injective argument.
   Corrected the prose leg direction, completed the proof explanations, repeated search
   records, recorded exact signatures, and removed accidental changes to fields of
   the existing node that stage 3 does not own.

Changes by this reading: proved the homology split; repaired missing docstring proofs,
cofan arrow direction, source attribution, node proof descriptions and signatures;
removed the unused item proof import and corrected the report's pruning claim.
