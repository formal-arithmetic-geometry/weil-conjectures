## What changed

Proved `isOpen_regularLocus_of_residueField_finite_models` without changing its
signature. Added the fully proved domain implication in
`Sheaf.RingTheory.JTwoDomainResidueModel`, corresponding to Stacks 07PC (4) implies (2).
The main proof applies that result to every prime quotient and then uses the existing
regular-locus criterion (07P9).

The domain proof constructs the residue-field embedding into `FractionRing S`, applies
`Algebra.exists_finite_purelyInseparable_separable_extension`, and constructs the image
of `B ⊗[R] S` inside the auxiliary field. Both inclusions are proved injective, and their
finite type instances are constructed. Four proved private helpers transport the
separability predicate along field equivalences and injective algebra maps. They let
the proof apply the existing separable ascent and finite type descent declarations
with exactly their specified fraction-field algebra structure. No new unproved
intermediate statement or data definition is introduced.

The original seven-step route is retained: steps 1–5 are the fully proved domain
lemma, and steps 6–7 remain in the main theorem. The DAG records this separation.
Neither node realizes a unit statement or a unit proof step in `sk-prop-a1-kummer`;
the containing unit route and all existing signatures and public imports are retained.

## Proved and sorry left

Closed 1 of 1 original holes:
`isOpen_regularLocus_of_residueField_finite_models`
(`lem-exc-j2-residue-field-criterion`).

Added 0 holes. The new theorem
`exists_nonempty_regular_open_of_residueField_finite_models_domain`
(`lem-exc-j2-residue-field-criterion-domain`) and all four private helpers are proved.
There are zero textual `sorry`s in either delivered Lean module. This is a proof from
existing declared dependencies, not a decomposition into new holes. The existing
separable ascent, finite type descent, and prime-quotient regular-locus criterion
remain dependencies; this delivery does not claim those existing holes are closed.

Both files compile through `lcompile.py --all`; the final delivery preflight also
checks their declarations and axioms.

## No longer needed

Removed the direct proof imports
`WeilConjectures.FieldTheory.MakeSeparable` (including its duplicate),
`WeilConjectures.FieldTheory.SeparableExtension` (including its duplicate),
`Sheaf.RingTheory.NonemptyRegularOpenSeparableAscent`, and
`Sheaf.RingTheory.JZeroFiniteTypeDomainDescent` from the main module. These dependencies
are used by the domain module instead. `SeparableExtension` is already publicly
imported by `MakeSeparable`, so no separate direct import is needed there.
Removed the unused candidate import `Mathlib.Algebra.Algebra.Subalgebra.Tower` from
the new module. The actual remaining imports provide the statements, essential finite
type/finitely generated intermediate field API, transcendence-basis transport, tensor
base-change finiteness, and Noetherian permanence.

No existing node or module is pruned from the combined proof closure. The main node's
old direct dependencies for its domain argument are now dependencies of the new node.
Its obsolete top-level `tool_uses` entry `lem-weil-pbc-make-separable` is removed because
the main node no longer invokes it directly. The new domain node uses that same
field-theory theorem as the same generic tool below the unit level; independent
review should record that approval. It produces the auxiliary separable field square;
no theorem of the containing unit supplies this generic algebra tool.

## Where the brief, the DAG or earlier work was wrong

No new statement defect was found. The already documented source assertion that the
tensor-image fraction field is the whole auxiliary field is not needed: the proof
embeds the fraction field in that auxiliary field and restricts separability. The DAG's
existing correction to the compositum is respected. Finite type over S suffices for
descent, so the code does not separately establish the stronger module-finiteness of
the tensor image over S. Finite type follows from finite type over R and restriction
of scalars.

Checked the source proof in `literature/stacks-project/more-algebra.tex`, lemma-J-2,
and the signatures of all recorded proof dependencies. Searches recorded in
`searches.jsonl` used LeanFinder, Loogle, grep, and LeanSearch; none supplies this
criterion directly. A blueprint search for J-2 returned no imported duplicate.
The zero base ring admits no domain algebra and no prime; the main proof still
handles the zero target algebra through the vacuous prime-quotient criterion.
Field bases, identity field extensions, and zero transcendence degree need no
additional hypotheses in the domain construction or separability transport.

## New nodes

`lem-exc-j2-residue-field-criterion-domain`, in
`dag/nodes/sec-smooth-purity/lem-exc-j2-residue-field-criterion-domain.json`, records
Stacks 07PC (4) implies (2), the separately identified domain implication. Its module
is `Sheaf.RingTheory.JTwoDomainResidueModel`. It is proved in this delivery, introduces
no hole, and retains the original source and dependency route. The parent node's
proof is updated to use it for prime quotients. No existing statement or definition
changes, no consumer adaptations, and no change record are needed.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
