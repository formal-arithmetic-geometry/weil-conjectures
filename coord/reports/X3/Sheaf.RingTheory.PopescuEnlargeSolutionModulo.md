## What changed

Replaced the sorry in `Algebra.exists_essentiallySmooth_artinian_enlargement` by a
complete Lean proof from two strictly smaller construction statements, in new modules
`Sheaf.RingTheory.ArtinianSeparableResidueLift` and
`Sheaf.RingTheory.ArtinianTranscendentalLocalization`.
The original theorem's signature, universes and public imports are unchanged.

The assigned module proves three private helpers using Mathlib only:
`pow_eq_of_residue_eq` kills a residue-congruence error by Frobenius and nilpotence;
`exists_separable_pow` finds a separable p-power of an algebraic element by applying
separable-first/purely-inseparable to its simple intermediate field;
`essentiallySmooth_of_smooth` uses localization at the bottom submonoid.
The final proof splits on algebraicity, applies the appropriate construction statement,
uses an actual preimage `d^(p^f)` in the algebraic case, and checks the positive exponent
and the displayed quotient image. There is no sorry in these helpers or in the assembly.

The new transcendental statement fixes its ring explicitly as the universe lift of
`D[t]` localized at the inverse image of the target maximal ideal. Defining this ring
needs no witness of an unproved existence theorem. Its construction avoids identifying
`D[x]` with a polynomial algebra and thereby removes the basis-lifting dependency.
The new separable statement captures a specified separable residue element by a finite
étale extension; it asserts no power-image result or exact lift-image result.

Updated the parent node's proof, proof dependencies and proof origin; added nodes for
both construction statements, with their source, complete proofs in words and real
Mathlib-search records. LeanSearch returned HTTP 500, recorded as unavailable; semantic
search, Loogle and source grep ran successfully and found no exact construction theorem.
Blueprint searches found no duplicate. The unit and chapter routes are untouched.

All three modules compile together through `lcompile.py --all`, without warnings.
The unused-variable linter is disabled only on the original theorem: its fixed interface
has extra background assumptions that this proof legitimately does not need.
No statement, definition or visibility changes and no forced adaptations.

## Proved and sorry left

Closed the original hole in `Algebra.exists_essentiallySmooth_artinian_enlargement`
(node `lem-weil-pbc-popescu-enlarge-solution-modulo`). The assigned module contains zero
sorries. Its three private helpers are proved from Mathlib without construction holes.

Added exactly two holes, each in a named public theorem whose body is `:= by sorry`:

- `Algebra.exists_finiteEtale_artinian_residue_lift`, node
  `lem-weil-pbc-artinian-separable-residue-lift`, module
  `Sheaf.RingTheory.ArtinianSeparableResidueLift`.
- `Algebra.artinian_transcendental_polynomial_localization`, node
  `lem-weil-pbc-artinian-transcendental-localization`, module
  `Sheaf.RingTheory.ArtinianTranscendentalLocalization`.

This is a decomposition: one upper hole closed and two lower holes added, not a complete
sorry-free proof of the enlargement theorem. Both new statements are parts of Stacks
07FI's construction and strictly smaller than the delivered theorem. The first is
restricted to an already separable residue element, with no Frobenius conclusion; the
second is restricted to the transcendental case and concerns a fixed, explicit ring.
The proof combines them with separable-power reduction and nilpotent-error elimination.
The ledger, rather than this report, determines the net after pruning.

Edge cases checked against the statements: a separable residue element equal to zero
or already in the source field is handled by the identity extension (with a universe
lift); neither construction needs positive characteristic. The transcendental hypothesis
excludes zero and elements of the source residue field. When the target is a field, the
Frobenius congruence proof still works (the maximal ideal is zero). Arbitrary nilpotent
images of `l` also satisfy the assembled argument; the existing unit assumption is kept.

## No longer needed

Pruned from this proof route: node `lem-weil-pbc-local-artinian-basis-when-flat` and module
`Sheaf.RingTheory.BasisIffBasisQuotientOfNilpotent`. No new construction module imports it.
The transcendental argument localizes the polynomial ring directly, so injectivity of
evaluation and a lifted module basis are unnecessary. This is a route-local pruning;
other targets may still reach that module.

Removed all seven old direct proof imports from the assigned module:

- `Sheaf.RingTheory.BasisIffBasisQuotientOfNilpotent` (genuinely pruned).
- `Sheaf.RingTheory.EssentiallySmooth` (available through the unchanged public statement
  import and the new construction interface; its definition remains used).
- `Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian` (used in both new construction plans).
- `Sheaf.RingTheory.HenselianEtaleRetraction` (used in the separable construction plan).
- `Sheaf.RingTheory.HenselianFiniteEtaleEquivalence` (same).
- `Sheaf.RingTheory.LocalDimensionZeroHenselian` (same).
- `WeilConjectures.Mathlib.RingTheory.Etale.Field` (same).

The last five dependencies have moved below the construction statements; they are not
claimed as globally pruned. Other old DAG dependencies concerning noetherianity,
localizations, Artinian rings, flatness, étale base change and separability remain in the
new nodes where used. No unit statement or realized unit step was bypassed.

The complete list of old direct `proof_deps` removed from the parent is the following.
Only the basis lemma is absent from the new construction plans; all the other entries
move below the new construction statements:

- `def-weil-pbc-flat-ring-map`;
- `lem-weil-pbc-artinian-local-unique-prime`;
- `lem-weil-pbc-criterion-flatness-fibre-noetherian`;
- `lem-weil-pbc-etale-ring-base-change`;
- `lem-weil-pbc-finite-separable-extension-etale`;
- `lem-weil-pbc-finite-type-algebra-noetherian`;
- `lem-weil-pbc-henselian-etale-retraction`;
- `lem-weil-pbc-henselian-finite-etale-equivalence`;
- `lem-weil-pbc-local-artinian-basis-when-flat`;
- `lem-weil-pbc-local-dimension-zero-henselian`;
- `lem-weil-pbc-localization-noetherian`;
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`;
- `lem-weil-pbc-polynomial-ring-smooth`.

The second reader also removed redundant proof imports
`Mathlib.Algebra.CharP.Lemmas` and `Mathlib.Algebra.CharP.Algebra`, already supplied
by `Mathlib.FieldTheory.PurelyInseparable.Basic`. In the two new modules,
`public import Mathlib.RingTheory.Artinian.Module` was narrowed to
`public import Mathlib.RingTheory.Artinian.Defs`: their public interfaces need the
Artinian predicate, not that module's ring structure theorems.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The former DAG's polynomial-subring identification and
basis-lifting step are unnecessary: localizing `D[t]` at the contracted prime works
without first proving evaluation injective. The source's phrase “q divisible by p”
had already been corrected in the original node to a sufficiently large p-power;
the delivered Lean proof uses exactly that valid Frobenius argument.

The original theorem's long docstring still presents the source's older, valid detailed
plan; the updated DAG and the proof body describe the shorter implementation.
The source text was read from the local literature mirror at
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/smoothing.tex`, since the project
clone does not contain the untracked literature files.

## New nodes

`lem-weil-pbc-artinian-separable-residue-lift` captures only the finite étale, henselian
factorization and flatness part of parent steps 8–10. Its statement introduces arbitrary
local Artinian rings and an already separable target residue element. Its node is at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-artinian-separable-residue-lift.json`.

`lem-weil-pbc-artinian-transcendental-localization` captures parent steps 4–6 using the
concrete polynomial localization, with no lifted-basis or subring-identification step.
Its node is at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-artinian-transcendental-localization.json`.

No change record is needed: existing interfaces and definitions are unchanged.

## Second reading by X3

1. **Existing interfaces: pass.** Compared every delivered module with the repository.
   The only existing module is `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`;
   its original theorem signature is byte-for-byte identical, and its public import,
   universes, visibility and original docstring are unchanged. Added helpers are private
   theorems. The new modules add statements without changing existing definitions.
   No arbitrary existence witness is used to define data: the separable extension is
   eliminated inside a proof of an existential proposition; the transcendental ring is
   explicitly a universe lift of a polynomial localization.
2. **Proof and axioms: pass as a decomposition.** Compiled all three modules through
   `lcompile.py --all` without errors or warnings. Scratch copies with `#print axioms`
   checked all six declarations. Each private helper uses only `propext`,
   `Classical.choice`, `Quot.sound`; the parent and the two new construction theorems
   additionally use `sorryAx`. The only two sorry bodies are exactly the named public
   construction theorems listed above. There are no definitions or prohibited axioms,
   unsafe declarations, opaque declarations or external implementations in this delivery.
3. **Split statements: pass.** Read the Stacks 07FI proof in the local literature mirror
   and both complete construction docstrings and nodes. The separable statement handles
   zero, elements already in the source residue field, and characteristic zero by the
   same finite étale construction (identity extension in the first two cases).
   In the transcendental statement, evaluation modulo the source maximal ideal is
   injective, so the contracted prime is precisely m_D[t]; its localization has
   nilpotent maximal ideal and residue field F(t). The Noetherian fibre criterion gives
   flatness in both constructions since the intermediate closed fibre is a field.
   Neither statement has the parent's positive power conclusion; both are strict parts
   of its argument. Independent searches used LeanFinder for lifting a finite separable
   residue extension, Loogle `IsArtinianRing, Polynomial`, Mathlib grep for residue-field
   étale and Artinian localization results, and repository grep for residue lifting and
   transcendental localization. Results included the universal factorization étale
   theorem, unramified residue-field results and Artinian localization results, but no
   theorem with either required construction. The upstream prescribed-residue-field
   étale results and `exists_flat_local_extension_given_residue_field` do not supply
   the required Artinian factorization into S. Neither remaining construction can be
   closed in a few minutes from these results.
4. **Route and pruning: pass after report repair.** Read the proof from its final
   assembly through separable-power reduction and nilpotent-error elimination. Both
   helpers are Mathlib proofs, and the essentially-smooth conversion localizes at the
   bottom submonoid. All proof-only imports are private. Checked `sk-thm-p1.json`:
   neither the parent nor the removed basis lemma realizes a unit step, and the unit
   route is preserved. Expanded `## No longer needed` to enumerate all thirteen removed
   parent dependencies, distinguishing the basis pruning from dependencies moved below
   the new construction statements. Removed two redundant characteristic imports and
   narrowed the new modules' Artinian public imports to the definitions module.
5. **DAG agreement: pass.** The parent JSON differs from the repository only in `proof`,
   `proof_deps`, and `proof_origin`. Its five steps follow the actual assembly. For all
   three nodes, `proof_deps` is exactly the union of step `uses`. Both new nodes have
   self-contained statements, verbatim Lean signatures, sources, proof steps, searches,
   origin, creation, chapter, unit and blueprint fields. No unit or chapter file changed.

Second-reading changes: import pruning/narrowing, trailing whitespace cleanup in one
private proof, and the report's complete removed-dependency list and review evidence.
No proof argument, theorem signature, definition or DAG field required repair.
