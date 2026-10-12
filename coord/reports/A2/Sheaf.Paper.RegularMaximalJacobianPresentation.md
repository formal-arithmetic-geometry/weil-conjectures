## What changed

Proved `Algebra.exists_jacobian_unit_presentation_of_regularAtMaximal` in
`Sheaf.Paper.RegularMaximalJacobianPresentation`, with its signature and public imports unchanged.
Reused the independent, already proved source theorem
`Algebra.IsSmoothAt.of_isRegularLocalRing_of_isAlgClosed`, then Mathlib's
`Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`. Extracted a finite submersive
presentation, enumerated variables by `Fin n`, ordered relation indices by their selected
variables, and enumerated that order by `Fin c`. This makes the selected variables strictly
increasing. Transported its unit Jacobian back along the quotient algebra equivalence and
used determinant transpose to obtain exactly the matrix in the statement.

Added proof-only imports `WeilConjectures.Mathlib.RingTheory.Smooth.Local` and
`Mathlib.Data.Fintype.Sort`. The standard smooth neighbourhood theorem is already
imported transitively by the source module; the second reader removed its redundant
direct `Mathlib.RingTheory.Smooth.StandardSmoothOfFree` import.
Updated the theorem docstring and the item's node proof, proof dependencies and proof origin.
The scoped unused-variable linter option preserves the original existential binder `e`,
whose type supplies the isomorphism but whose value is intentionally absent from the proposition.
No interface or definition changed; no adaptation is required.

Single-file compilation passes with no warnings. Explicit `#print axioms` on both the
source regular-point theorem and the completed theorem yields only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. The finite order and transpose
constructions require no nonempty index type, so zero equations and zero variables are
covered without a separate assumption. Maximality excludes the zero-ring point case.
The unit `sk-thm-p1`'s realized statements and steps are unchanged: this is a shorter
route strictly below them. `tools/import_direction.py may` confirms the source smoothness
module does not reach this item, so this does not invoke the dependent Sheaf smoothness
criterion in a circle.

## Proved and sorry left

Closed 1 of the original 1 holes:
`Algebra.exists_jacobian_unit_presentation_of_regularAtMaximal`
(node `lem-weil-pbc-regular-maximal-jacobian-presentation`).
No holes remain in the item, no holes were added, and no theorem was split off.
This is a proof, not a decomposition. The new node attaches the already proved source
`Algebra.IsSmoothAt.of_isRegularLocalRing_of_isAlgClosed`; it delivers no Lean module
and introduces no unproved declaration.

## No longer needed

Removed these proof-only imports:

- `Mathlib.RingTheory.RegularLocalRing.Polynomial`
- `Mathlib.RingTheory.Kaehler.Polynomial`
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
- `Sheaf.Paper.MaximalIdealDifferentialCotangentDimension`
- `Sheaf.LinearAlgebra.NonzeroMaximalMinorOfInjective`

The first three are still available transitively through the proved source route; this is
removal of redundant direct imports, not a claim that their whole modules disappear.
The two Sheaf modules are not needed on this item's proof branch. No separate Jacobian
minor selection, shrinking of the kernel quotient, or inverse-variable construction is
needed. Removing the maximal-minor branch also removes its imported Sheaf Cauchy--Binet
branch from this item (other targets may still use it).

These old direct proof dependency edges are replaced:

- `lem-weil-pbc-polynomial-ring-field-regular-ring`
- `lem-weil-pbc-localization-at-prime-of-quotient`
- `lem-weil-pbc-regular-local-quotient-independent-generators`
- `lem-weil-pbc-maximal-ideal-differential-cotangent-dimension`
- `lem-weil-pbc-jacobi-zariski-differential-maps`
- `lem-weil-pbc-kahler-differentials-localization`
- `lem-weil-pbc-polynomial-ring-kahler-basis`
- `lem-weil-pbc-zariski-lemma`
- `lem-weil-pbc-alg-closed-finite-extension-trivial`
- `lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `def-weil-ring-localization-away`
- `lem-weil-pbc-block-triangular-determinant`

The new source node retains the polynomial-regularity, independent-generators, Zariski-lemma,
and algebraically-closed-finite-extension results as dependencies documenting the source
proof. They are therefore not claimed as globally pruned. Localization-away remains in
the public statement. Finite type, determinant and polynomial differentiation remain in
the item's proof dependency list; standard smooth presentations are newly used.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but longer than necessary. The repository already contains
a fully proved regular-closed-point smoothness theorem in
`WeilConjectures.Mathlib.RingTheory.Smooth.Local:226`, independent of the Sheaf regular/smooth
chain. The plan did not record or use that theorem. Its reuse avoids both unproved
maximal-minor machinery and a new inverse-variable construction. No statement was false
or changed. The item's existing blueprint ancestor metadata is preserved.

The configured LeanSearch request returned an internal-server-error response; it is
recorded as unavailable. Loogle and Mathlib grep returned no regularity/smoothness match;
the exact proved theorem was found by searching and reading the source library.
Source texts 00TV and 00TS were checked on the Stacks website because the read-only clone
has no local `literature/stacks-project/algebra.tex`.

## New nodes

`lem-weil-pbc-regular-closed-point-smooth-source` records the exact already proved
`Algebra.IsSmoothAt.of_isRegularLocalRing_of_isAlgClosed` from the adopted source library.
It states smoothness at a regular maximal ideal over an algebraically closed field,
without asserting a presentation or a Jacobian minor. Its source is Stacks 00TV at a
closed point, equivalently the regular-to-smooth direction of 00TS. Its proof record
documents the source's regular-local independent-generator argument. The three search
kinds were run and are logged; LeanSearch was unavailable and the other two found no
Mathlib theorem. Whole-blueprint searches for `regular rational`, `regular smooth`, and
`00TV` found no matching blueprint statement (the one smooth-curve-regularity hit has
the opposite direction). This node adds no pending work or module. No change record is
needed because every existing signature, definition and visibility is preserved.

## Second reading by A2

1. Compared the entire delivered module with the repository using `diff`, and
   mechanically compared the existing theorem signature: byte-for-byte identical.
   All public imports, visibility and universe declarations are unchanged. No
   definition or statement changes, change records or forced adaptations are needed.
2. Compiled the module locally through `lcompile.py`, without errors or warnings.
   A scratch copy with `#print axioms` confirms that both the source regular-point
   theorem and the completed presentation theorem use only `propext`,
   `Classical.choice` and `Quot.sound`. There are no sorries, forbidden declarations
   or data definitions in the delivered Lean module. The existential presentation
   is extracted from proved results, so no arbitrary unproved witness is chosen.
3. No statement was split off. Read the already proved source theorem and its
   regular-local and cotangent argument. The new node records that existing theorem,
   not a duplicate Lean statement or a new hole. Independent Loogle search for
   `Algebra.SubmersivePresentation.reindex` and grep for `jacobiMatrix|monoEquivOfFin`
   confirm the existing presentation transport and finite sorting tools. Repository
   searches found no other node recording the exact source declaration. Empty
   relation sets have determinant one and vacuous strict monotonicity; empty variable
   sets force empty relation sets by injectivity. Maximal ideals exclude the zero ring.
4. The source theorem followed by Mathlib's standard smooth neighbourhood and
   reindexing is a short route below the unit level. Read the `sk-thm-p1` realized
   statements and steps: none is bypassed or modified. Checked all old dependency
   edges against the report's pruning list; it lists every removed edge and accurately
   distinguishes retained transitive source dependencies. Import-removal experiments
   show that `Mathlib.Data.Fintype.Sort` is needed (`monoEquivOfFin` becomes unknown),
   while `Mathlib.RingTheory.Smooth.StandardSmoothOfFree` is redundant. Removed the
   latter direct import; the modified module still compiles. Public statement imports
   stay unchanged.
5. Compared the existing node diff: only `proof`, `proof_deps`, and `proof_origin`
   changed. Their steps describe the actual local instances, ordered reindexing,
   quotient equivalence, unit transport and determinant transpose; the dependency
   list is exactly the union of the steps' `uses`. Checked the new node's source,
   self-contained statement, existing Lean declaration, creation record, blueprint,
   searches, chapter and unit. The source file path stays in `lean.note`: the
   delivery schema forbids `lean.file` for an existing declaration, since no source
   module is delivered.

Second reading changed only a redundant proof import, the report, and trailing
whitespace; the proof itself required no repair.
