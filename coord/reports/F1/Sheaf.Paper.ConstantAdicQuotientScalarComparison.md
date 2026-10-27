## What changed

Prove `AlgebraicGeometry.Scheme.constantAdicQuotientScalarComparison` without
changing its statement or any existing definition. Construct the ordinary
comparison from restriction composition, the proved constant-module comparison,
and finite-coefficient transport. Prove uniqueness on constant sections. The
completion quotient map is bijective by the finitely generated power-kernel
formula and evaluation, including the zero-ring case.

Prove the scalar assertion by pasting the three localized coefficient squares
and then the inverse-image square. The supplied arbitrary module adjunction is
used throughout. The inverse-image scalar mate is invertible by the existing
ring-sheaf-change adjunct identity and iterated mates. This argument imposes no
boundedness, scheme finiteness, or nontriviality hypothesis.

Add the proved generic tool `CategoryTheory.derivedScalarMatePasting` in
`Sheaf.CategoryTheory.ExactScalarMatePasting`. Its proof uses the existing exact
square localization/composition theorem and Mathlib's mate-pasting identity.
All additional imports of the item are private proof imports. Existing public
imports, declaration signatures, and definition bodies are preserved.

Validation: both modules compiled through `lcompile.py --all`; the completed
item compiled in 48.3 seconds, within the 60-second limit.

## Proved and sorry left

Close the one original hole:
`AlgebraicGeometry.Scheme.constantAdicQuotientScalarComparison`
(node `lem-weil-pbc-constant-adic-quotient-scalar-comparison`).

The new theorem `CategoryTheory.derivedScalarMatePasting` is proved, with no
holes. The item and the new module contain zero `sorry`s. Holes closed: 1;
holes added: 0; split-off obligations: 0. Previously proved dependencies are
reused rather than adding another assumed scalar-comparison theorem.

## No longer needed

The proof does not use the planned dependency
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
(`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`): canonical
ring-sheaf-change adjunction compatibility and elementary iterated mates give
exactly the inverse-image scalar comparison needed here. Remove it from this
node's proof dependencies; no claim is made that other consumers can drop it.

The direct planned dependency `def-weil-pbc-bounded-constructible-tower` is
unnecessary for this argument: neither a tower object nor a constructibility
hypothesis is used. Definitions needed by the theorem remain available through
its unchanged statement imports. No existing public import or module is removed.

## Where the brief, the DAG or earlier work was wrong

The statement is valid as written. The planned flat-term calculation need not be
repeated: `adicLisseConstantModules` is definitionally the constant-module
functor already treated by the proved generic scalar-extension theorem. The
remaining work is coherence with the specified quotient/finite-coefficient and
inverse-image squares. That coherence is proved by exact localization and
adjunction mate pasting. No shared definition repair or forced adaptation is
needed, and the unit's realized statements and route are preserved.

## New nodes

`lem-weil-pbc-exact-scalar-mate-pasting`, attached to the fully proved theorem
`CategoryTheory.derivedScalarMatePasting`, states that the inverse scalar mate
of a specified paste of exact coefficient squares is invertible when its two
constituent mates are invertible. It is a general two-square composition tool,
not a restatement of the assigned completion-quotient assertion. Its source,
complete proof, searches, and exact Lean signature are recorded in the node.
No change records are needed because no existing interface is changed.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
