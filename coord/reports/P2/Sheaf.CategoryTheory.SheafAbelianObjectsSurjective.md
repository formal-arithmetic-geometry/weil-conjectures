## What changed

Completed `CategoryTheory.sheafAbelianObjects_surjective` in
`Sheaf.CategoryTheory.SheafAbelianObjectsSurjective` without changing its signature,
visibility, universes, or imports. Private helpers explicitly construct the additive
commutative groups on the original section types, the additive restriction maps, and
the resulting sheaf. The underlying sheaf is definitionally the original one.
Multiplication compatibility and Mathlib's `MonObj.ext` and `GrpObj.ext` then give
actual equality of internal commutative group objects, not merely an isomorphism.

Updated the existing node's proof and proof origin to describe these checked steps.
The unit `sk-def-exchange` has no realized proof steps affected by this argument.
The construction follows the quadruples in Stacks
[Section 00YR](https://stacks.math.columbia.edu/tag/00YR), preceding Proposition 00YV.

## Proved and sorry left

Closed one original hole: `CategoryTheory.sheafAbelianObjects_surjective`
(node `lem-weil-pbc-sheaf-abelian-objects-bijective-surjective`).
Added zero holes; zero `sorry`s remain in the delivered module. This is a complete
proof, not a decomposition. All five private helpers are complete, and all constructed
data are explicit. No existence theorem is used to choose data.

The module compiles through `lcompile.py` without warnings. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivery dry run
performs the final axiom and preflight checks. No global library build was run.

## No longer needed

No imports removed and no existing nodes or modules pruned: all four original
Mathlib imports support the unchanged statement or the reconstruction proof.
No `Sheaf` or `WeilConjectures` proof dependencies are needed. The unit route is kept.

Discarded the previous sandbox attempt's unused
`sheafAbelianObjects_sectionwise_mul` helper and
`sheafAbelianObjects_reconstruction_core` restatement, and their two unlanded node
files. These are not existing library nodes and do not count as pruning the library.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's reconstruction core merely replaced the conjunction of three
compatibilities with three separate hypotheses and repeated the entire original
conclusion. That was a restatement, not a strict reduction, and its extraction helper
was unused. Both have been removed, together with the earlier claimed review text.

The original docstring included an injectivity argument, although this item concerns
surjectivity. It now describes only the complete proof delivered here. Multiplication
compatibility suffices for the final equality because Mathlib's internal monoid and
group extensionality lemmas recover the unit and inverse; the supplied unit and
inverse hypotheses are retained unchanged.

The local clone does not contain `literature/stacks-project/sites.tex`; the cited
Stacks tags were read on the official Stacks website. No mathematical disagreement
or statement change was needed.

## Second reading by P2

1. Compared the delivered module with the repository version. The theorem signature, visibility,
universes, and imports are unchanged. The changes are the docstring, proof body, and five
private reconstruction/extensionality helpers; no existing definition was altered.
Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds without warnings or `sorry`. The proof
uses explicit reconstruction data and contains no forbidden declarations or hollow definitions.
A scratch-copy `#print axioms CategoryTheory.sheafAbelianObjects_surjective` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.
Verdict: pass; the target hole is closed and no holes were added.

3. Checked the existing node and searched the library for duplicate declarations. The target
statement is unchanged, and no split-off statement or duplicate helper node was delivered.
Verdict: pass.

4. Read the proof from the target downward. It reconstructs the additive sheaf explicitly,
uses the stated section multiplication compatibility, and finishes with internal extensionality.
No proof-dependency imports were removed, and the unit route remains unchanged.
The limits import supplies the forgetful-functor sheaf-composition instance in the signature,
so it is appropriately public. The other imports supply sheaves, composition, and internal
commutative group objects used in the signature.
Verdict: pass.

5. The node's Lean declaration and statement match the module. Its proof metadata records the
sectionwise reconstruction and extensionality route; no new nodes or change records are needed.
Verdict: pass.

Changed after this reading: appended this review only; no Lean or DAG changes were necessary.
