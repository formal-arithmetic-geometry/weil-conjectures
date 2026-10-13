## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage` to the two
individual tensor-transport compatibility squares in new modules
`Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageFirst` and
`Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond`. Both imports are proof-only.
The original signature, public imports and definitions are unchanged. The main
proof expands the Yoneda cup, transports composition, applies the second square,
reassociates, and applies the first square. Its DAG proof now follows this Lean proof.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage` (node
`lem-sc-scalar-ext-cup-inverse-image`). No sorry remains in the item's module.
Added two named holes:

- `AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage_first`, node
  `lem-sc-scalar-ext-cup-inverse-image-first`.
- `AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage_second`, node
  `lem-sc-scalar-ext-cup-inverse-image-second`.

This is a decomposition: one upper hole closed, two lower holes added, net -1.
The first statement has only a degree-p class and no second factor class; the
second has only a degree-q class and no first factor class. Neither is a renaming
or repackaging of the cup-product theorem. Their combination is a complete Lean
proof using composition preservation and four associativity rewrites.
All three files compiled locally; the delivery dry run supplies the final checks.

## No longer needed

No imports removed and no existing nodes or modules pruned. The original only
public import supplies the scalar sheaf and operation interfaces used in the
unchanged statement. The proof keeps both tensor transports of the existing plan.
`def-sc-field-linear-module-cohomology-operations` leaves the original
node's direct `proof_deps` but stays a statement dependency and is used by both
split-off nodes; its module remains required by the unchanged signature.
No stronger result such as invertibility of the tensor comparison is required
for the second square; naturality alone suffices there.

## Where the brief, the DAG or earlier work was wrong

The previous node provided one long natural-language step and only the definitions
node as a dependency. It did not provide Lean statements of the two transport
squares it invokes. Those are now isolated rather than leaving hidden holes in the
main proof. No mathematical statement error or unit-route departure was found.
The unit record `sk-prop-av-cube` has empty realization lists; this decomposition
changes no unit statement or step and retains the existing node's argument.

Loogle returned `Ext.comp_mapExactFunctor` and
`Ext.mapExactFunctor_comp_mk₀_natTransApp`, but neither is available in the pinned
Mathlib source/compiler. LeanFinder found ordinary tensor naturality, Tor maps and
scalar transport, not either Ext identity. LeanSearch was unavailable (HTTP 500).
The existing exactFunctorCompositionComparison handles natural isomorphisms,
while these factor equations also need general coefficient morphisms.

WANTED: the local `literature/stacks-project/cohomology.tex` checkout is absent.
The official pages for Tags 01FD, 07MB and 0FKV were read. These give resolution
comparison and tensor-pairing context, not verbatim versions of the new equations;
the specialized shifted-morphism/coherence arguments are marked agent-written.
No source file or project tooling was changed.

Edge cases: at p=0 the first equation is the ordinary tensor/unit coherence square;
at q=0 the second is ordinary oplax naturality followed by cancellation of the unit
isomorphism. Zero coefficient sheaves and empty schemes introduce no extra
hypothesis: the same morphism identities hold. The second equation needs only that
u is an isomorphism; the first additionally checks that the particular u agrees
with the adjunction's oplax unit, as spelled out in its proof docstring.

## New nodes

`lem-sc-scalar-ext-cup-inverse-image-first` records the first tensor transport,
including its initial unit/unitor comparison. Its new module is
`lean/Sheaf/AlgebraicGeometry/ScalarExtCupInverseImageFirst.lean`. The docstring
specifies the transformation, its localization, the unit coherence identity, and
how arbitrary φ enters. It has source, proof steps, three executed search kinds,
and the original blueprint ancestor and unit.

`lem-sc-scalar-ext-cup-inverse-image-second` records the second transport under
oplax tensor naturality, followed by φ and ψ and insertion of the inverse unit
maps. Its new module is
`lean/Sheaf/AlgebraicGeometry/ScalarExtCupInverseImageSecond.lean`. It has the same
source context, complete natural-language argument and executed search kinds.
No statement or definition change record is needed.

## Second reading by S2

1. I compared the delivered main module with the repository version. The target
   theorem signature, its public import, and all existing declarations are
   unchanged; only proof-only imports and the proof body were added. Verdict:
   pass.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile
   without errors, and the only remaining `sorry`s are the two named split-off
   theorems, each with a docstring and matching DAG node. No definitions contain
   `sorry`, and no forbidden declarations were introduced. Scratch-copy
   `#print axioms` for all three declarations showed exactly `propext`,
   `Classical.choice`, `Quot.sound`, and the expected `sorryAx`. Verdict: pass.
3. The two split-off statements are independent first- and second-factor
   transport identities, strictly simpler than the original cup identity. Their
   degree-zero and zero-object edge cases are covered by the same coherence
   equations described in their docstrings. Searches recorded in `searches.jsonl`
   found no existing declaration. Independent LeanFinder search for natural
   transformation compatibility of Yoneda Ext transport returned only transport
   definitions and related coefficient formulas; repository searches also found
   no factor formula. Verdict: pass.
4. The proof follows the two transport squares, composition preservation, and
   associativity in the existing unit route. Both new modules are imported only
   for the proof, and no unused import or obsolete proof dependency was found.
   Verdict: pass.
5. The existing node's proof and `proof_deps` now match the Lean proof, and both
   new nodes carry the exact Lean statements, sources, searches, blueprint,
   chapter, and unit metadata. Verdict: pass.

I changed only the report during second reading; no Lean source or DAG content
required repair.
