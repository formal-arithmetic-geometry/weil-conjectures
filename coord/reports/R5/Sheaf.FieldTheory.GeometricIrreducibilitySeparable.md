## What changed

Proved `AlgebraicGeometry.geometricallyIrreducible_iff_separableElements_mem` in
`lean/Sheaf/FieldTheory/GeometricIrreducibilitySeparable.lean`, preserving its signature.
The forward implication follows the stated simple-subextension, subalgebra descent and
finite-separable tensor decomposition argument. A proved private helper uses primality of the
nilradical to show that an irreducible spectrum of a product of fields forces its index type
to be subsingleton. Mathlib then turns uniqueness of embeddings into pure inseparability and,
with separability, surjectivity of the base-field map.

The converse uses the relative algebraic closure, Mathlib's transitivity of integrality, the
stated algebraically-closed-in-extension geometric irreducibility lemma, the defining purely
inseparable criterion, the existing proved universal homeomorphism instance, and Mathlib's
composition theorem. The node's proof, dependencies and proof origin now follow this code.
The source is Stacks Algebra Tag 0G33, with its universal homeomorphism step supplied by the
proved scheme API. All added imports are proof imports. No public signature or definition changed.

Validation: the complete proof compiles with lcompile.py, with no warnings after import
cleanup. The resumed preflight's file-level interface diagnostic was repaired by keeping the
additional algebra instance proof-local and preserving the original file-level commands.
After a delivery compile exceeded 60 seconds, profiling compiled the same proof in 9.8 seconds
(tactics 1.18 seconds, typeclass inference 2.48 seconds, kernel checking 354 milliseconds),
with no slow definition identified. Profiling options were removed. The final dry run passed:
commit 6c3b5b5641 compiles and passes preflight; review class CODEX for the changed node file.
The theorem signature is textually unchanged, all Lean lines are at most 100 characters,
and the node's proof dependencies equal the union of its proof-step uses.

## Proved and sorry left

Closed 1 of the original 1 holes:
`AlgebraicGeometry.geometricallyIrreducible_iff_separableElements_mem`
(node `lem-zl-geometric-irreducibility-separable`).

Zero textual sorry remain in the item; zero holes added and zero statements split off.
The private helper `subsingleton_of_irreducible_pi` is fully proved. The proof uses the existing
stated declarations `Algebra.separable_tensor_algebraicallyClosed_equiv_pi`,
`AlgebraicGeometry.geometricallyIrreducible_spec_of_injective`, and
`AlgebraicGeometry.geometricallyIrreducible_of_isAlgebraic_mem`, whose existing holes remain
in their own modules. This delivery closes the item from those declared dependencies; it does
not claim the entire transitive proof closure is sorry-free.

## No longer needed

Removed proof imports from the original item:

- `Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism`: replaced by the proved purely
  inseparable universal homeomorphism instance in
  `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra`.
- `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`: available through the needed
  transcendence-basis import.
- `Mathlib.FieldTheory.PurelyInseparable.Basic` and `Mathlib.FieldTheory.SeparableClosure`:
  available through the needed universal homeomorphism import; no separate separable-closure
  construction is used.
- `WeilConjectures.FieldTheory.SeparableExtension`: publicly imported by the needed
  `Sheaf.FieldTheory.SeparableTensorAlgebraicClosure`.

The temporary draft's direct `Mathlib.AlgebraicGeometry.Pullbacks` import was also removed;
its API is publicly imported by the universal homeomorphism module. The final proof keeps
`Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis` and the algebraic-closure import.

Pruned direct node dependencies:

- `def-weil-pbc-relative-separable-closure`: simple-adjoin separability is proved directly by
  Mathlib's adjoin criterion.
- `lem-weil-pbc-algebraic-generators-finite-extension`: transitivity of integrality handles
  algebraic closedness of the relative algebraic closure directly.
- `lem-weil-pbc-separable-first-purely-inseparable`: use the defining criterion for pure
  inseparability directly.
- `lem-pur-power-generated-spectrum-homeomorphism` and its obsolete top-level `tool_uses`
  entry: the existing proved purely inseparable instance handles all characteristics.

These are removals from this item's route, not claims that no other target branch uses them.
No unit statement or realized proof step is bypassed; this node is below the unit level.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy or mathematical error was found. The original plan expanded several
steps that Mathlib or the proved scheme library already supplies. The preserved draft had one
API argument-order error: `Algebra.IsSeparable.of_algHom` needs the base field before its
codomain and algebra homomorphism. This is repaired. The previous compile-service outage has
cleared; the current proof was checked successfully. The resumed preflight detected added
file-level open/instance commands; these were replaced by qualified names and a proof-local
algebra instance, preserving the original file-level interface. No change record is needed because no
statement, definition, or exported import changed.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
