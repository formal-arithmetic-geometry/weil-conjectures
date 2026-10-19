## What changed

Proved `IsDiscreteValuationRing.exists_tame_galois_sequence` in
`Sheaf.FieldTheory.HenselianDVRTameSequence` from the existing canonical
strictly henselian tame-character theorem and the compatible-root product theorem.
The theorem signature, public imports and existing docstrings are unchanged.

Private, fully proved helpers identify tame root limits over two fields equipped
with compatible primitive roots. Mathlib's `IsPrimitiveRoot.zmodEquivZPowers`
gives the finite group equivalences. The helpers prove compatibility with power
transitions, construct inverse maps coordinatewise, and prove continuity for the
actual initial topologies. This works in mixed characteristic without a field
embedding between the coefficient field and the residue field.

The main proof makes R strictly henselian, applies the canonical character with
coefficient field `AlgebraicClosure Fsep`, transports its root limit to the residue
field, and composes with the adic-product equivalence. Injectivity preserves the
actual kernel and its finite-quotient assertion. The kernel is closed in the
Hausdorff target; the quotient equivalence is a homeomorphism by compactness of
the absolute Galois group. Its value on every quotient representative is proved.

The node's `proof`, `proof_deps` and `proof_origin` describe this route. Its
maintainer-approved canonical-character tool use is preserved, and the obsolete
finite-over-henselian approval is removed. No statement, public definition or
consumer changes; no change record is required. Earlier proposed new modules are
retained only in scratchpad and are excluded from delivery.

## Proved and sorry left

Closed one of one original holes:
`IsDiscreteValuationRing.exists_tame_galois_sequence`
(node `lem-exc-henselian-dvr-tame-sequence`).
Added zero holes; zero statements split off. No sorry remains in the delivered
module. All private helpers are fully proved. The imported
`IsDiscreteValuationRing.exists_canonical_tame_character` remains a separate
existing proof item; this delivery does not claim to close its inherited sorry.
`TameRoots.compatible_roots_product` has since been proved in the shared library.

Source checks confirm identical theorem signature and public imports, zero sorry
tokens and no Lean line longer than 100 characters. Earlier remote single-file
compiles passed. The fresh required `deliver3.py --no-push` succeeded with
exit code zero: commit `7e9a8d759d` compiles and passes preflight, classified
`CODEX: changes a node file`. Nothing was pushed by that dry run.

## No longer needed

Removed proof imports:
`Sheaf.RingTheory.FiniteOverHenselianLocalProduct`,
`Mathlib.Algebra.Algebra.Pi`, `Mathlib.RingTheory.LocalRing.ResidueField.Basic`,
`Sheaf.FieldTheory.FiniteDVRTameInertia`,
`Sheaf.FieldTheory.FiniteTameCharacterTower`,
`Sheaf.FieldTheory.TameRootExtension`,
`Sheaf.GroupTheory.InfiniteTameInverseLimit`, and
`WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct`.

The proof no longer directly uses nodes `lem-exc-finite-dvr-tame-inertia`,
`lem-weil-pbc-finite-over-henselian-local-product`,
`lem-exc-finite-tame-character-tower`, `lem-exc-galois-krull-finite-limit`,
`lem-exc-tame-root-extension`, or `lem-exc-infinite-tame-inverse-limit`.
Their finite-level assembly is supplied by the existing canonical-character
interface. Some remain dependencies of that interface, so no claim of their
removal from the entire targets' closure is made.

The proposed scratchpad modules `HenselianDVRFiniteTameSystem` and
`CofinalTameRootDiagram` and their proposed nodes are not needed or delivered.
No existing library module is withdrawn. The Mathlib Galois profinite import
remains for compactness. The obsolete direct finite-over-henselian entry is
removed from this node's `tool_uses`; the canonical-character approval stays.

## Where the brief, the DAG or earlier work was wrong

The original plan is sound but longer than necessary given the existing
canonical tame-character interface. The earlier attempt's finite-system split
was unnecessary. The retained proof follows the same tame ramification argument
through the stronger existing interface, with explicit root-limit transport.
The unit `sk-prop-a1-kummer` has no realized step replaced by this reuse.

Earlier delivery attempts were rejected because the route-pivot inventory
listed the canonical-character module. Maintainer resolution
`coord/repair-notes/Sheaf.FieldTheory.HenselianDVRTameSequence.json`
removes this ordinary algebraic tool and its characteristic-zero DVR helper
from the dropped inventory and approves its tool use on this item. This
resolution explicitly instructs retaining the existing E5 proof and delivering
normally. No launcher script, gate or shared source was changed by this worker.

Sources checked: Stacks `pione.tex`, Tag 0BUB,
`lemma-structure-decomposition-separable-closure`; current blueprint
`lem-exc-dvr-galois.proof.md`, first two paragraphs; both dependency statements
and nodes; Mathlib primitive-root equivalences and quotient APIs.
Edge cases checked: order one, exponent zero in the product theorem, p = 2,
independent field universes, and mixed characteristic. All existential choices
are inside theorem proofs; no data is defined by choosing an arbitrary witness
of an unproved existence theorem.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
