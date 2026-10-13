## What changed

`Sheaf.RingTheory.StrictHenselizationNoetherian` now proves its original equivalence
by two actual faithful-flat descent arguments. The forward implication applies
`Algebra.strictHenselization_completion_noetherian_faithfullyFlat` and specializes
Mathlib's `Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat`
with M = C. The reverse implication applies the existing residue-triple
`AlgebraicGeometry.Scheme.strictHenselization_faithfullyFlat`, then the same
Mathlib descent theorem with M = R. In both cases `Algebra.TensorProduct.rid`
transports Noetherianity to the tensor product required by Mathlib.

The new proof-only import `Sheaf.RingTheory.StrictHenselizationTriplesPresentation`
states the missing comparison between the pointed-algebra predicate and the
residue-triple ring cocone, including compatibility with the original R-map.
That comparison is the only new open theorem. `Mathlib.RingTheory.Noetherian.Basic`
is a proof-only import for `isNoetherian_of_linearEquiv`.
All original public imports, existing declaration signatures, and definitions stay
unchanged. No arbitrary witness from an open existence theorem is used in a
definition: the comparison witness is eliminated only inside a proposition proof.

## Proved and sorry left

Hole closed: `Algebra.isNoetherianRing_iff_isStrictHenselization`
(node `lem-sc-strict-henselization-noetherian`), one of one original holes.

Hole added: `Algebra.IsStrictHenselization.triples_presentation`
(node `lem-sc-strict-henselization-triples-presentation`), in its own new module.
Its proof is exactly `by sorry`; its docstring and node give the full
kernel/residue-field, equivalence, and colimit-universal-property argument.

This is a decomposition: one original hole closed and one new hole added, net
zero before the ledger's import-closure accounting. It is not an axiom-free proof
of the equivalence: the existing completion theorem and the new comparison are
still open. There is no `sorry` in the item's module or in any definition.

Removed from the first worker's undelivered proposal:
`Algebra.isNoetherianRing_of_isNoetherianRing_strictHenselization` and
`Algebra.isNoetherianRing_strictHenselization_of_isNoetherianRing`, together with
`StrictHenselizationNoetherianDirections.lean` and their two new node files.
Neither directional hole is added to the library.

## No longer needed

No original import, original proof dependency, or original module is pruned.
Every original proof dependency is used: completion Noetherianity and faithful
flatness for ascent, faithful flatness of the residue-triple colimit for descent,
and Mathlib's faithful-flat Noetherian descent in both directions.
The first worker's proposed directional module and nodes are removed before
delivery; they were never library dependencies and are not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The first proposal merely assembled two new unproved directional clauses. It did
not try the explicitly documented Mathlib module-to-ring descent specialization.
Its ascent node also cited strict-henselization faithful flatness instead of the
completion theorem needed by its text. Both new nodes named the parent theorem
as a statement dependency, producing a cycle with the parent's new proof edges.

The original plan's reverse implication has an interface gap: its faithful-flatness
Lean declaration accepts a residue-triple cocone over a scheme residue field,
whereas the item hypothesis specifies a cocone of pointed R-algebras over R/m.
They are mathematically equivalent presentations, but are not interchangeable
Lean hypotheses. The new comparison records precisely this gap, without
replacing the Noetherianity argument by another name for its conclusion.

Sources read: [Stacks 06LJ](https://stacks.math.columbia.edu/tag/06LJ), the first,
completion, and final descent paragraphs; [Stacks 07QM](https://stacks.math.columbia.edu/tag/07QM),
part (1); [Stacks 04GW](https://stacks.math.columbia.edu/tag/04GW), the correspondence
between residue triples and maps of pointed etale algebras. The cited local TeX
files are absent on this machine, so these official online pages were read.

## New nodes

`lem-sc-strict-henselization-triples-presentation` states a ring-colimit
presentation with the same vertex C and structural map R → C. It introduces no
Noetherian hypothesis or conclusion. Its statement dependencies are the existing
ring predicate, residue triples, and scheme residue-field definition. Its proof
uses the existing affine residue-field identification and filteredness supplied
by the triples theorem. It inherits the item's chapter and unit. LeanSearch was
attempted and unavailable; LeanFinder, Loogle, Mathlib grep, the upstream library,
and the local Sheaf/DAG statements revealed no existing comparison declaration.
No change record is needed: no existing statement or definition changes.

## Second reading by W2

1. **Interfaces: pass after repair.** Compared the delivered item with the
repository file using `diff -u`. Its theorem signature is byte for byte identical;
its existing declaration docstring and public imports are restored unchanged.
Only proof imports and the theorem body differ. The new comparison has its own
module and node. No other existing module is delivered and no definition changes.

2. **Proof and axioms: pass with the recorded open comparison.** Both final
modules compile locally in import order through `lcompile.py`, without warnings
or errors. Read every proof body and scanned for forbidden declarations and
attributes. The item contains no sorry; the new module has only the single named
comparison theorem with proof `by sorry`. Scratch copies with `#print axioms`
check both declarations; only the three allowed axioms and `sorryAx` occur.
The latter is expected from the named open comparison and existing prerequisites.
No data definition uses an unproved existence witness.

3. **Split statement: pass after replacement.** The new statement preserves the
base ring, field, algebra structures, universe, vertex C, and map R → C. The
existential residue-field algebra is the transported one in its docstring proof;
no additional Noetherian or regularity assumption occurs. For a field R with
K separably closed and C = K, both presentations are the pointed etale colimit
at the zero maximal ideal. For a local ring already strictly henselian the
identity R-map is preserved. A zero base ring cannot satisfy the field/residue
algebra hypotheses, so no exceptional zero-ring witness is required. The
kernel construction works for nonreduced and non-Noetherian local rings as well.
Read the existing predicate, triples, and faithful-flatness statements and
searched the library with different terms before introducing this comparison.
It is a categorical presentation lemma, strictly part of the reverse argument,
and does not restate either Noetherianity implication. Its docstring proof
explains essential surjectivity and the ring colimit property explicitly.

4. **Shortest route, imports, and unit: pass after repair.** Used the existing
completion statement directly and Mathlib descent in both directions; no
Noetherian-direction lemmas remain. Removed a trial redundant TensorProduct.Maps
import after successful compilation without it. All original proof dependencies
remain actually used, so No longer needed lists no false pruning. Read
`dag/units/sk-thm-br.json`: its Brauer-group injection/Tsen route and existing
realized fields are untouched. This change is below that unit's route, within
the original boundary-stalk Noetherianity argument.

5. **Nodes: pass after repair.** The item retains every original proof dependency
and adds the comparison used before applying faithful flatness. Its descent and
completion steps still match the Lean proof and Stacks 06LJ. The new node's
signature is transcribed from Lean, its proof dependencies are exactly the union
of its steps, its source and proof origin identify 04GW, and its created,
blueprint, chapter, unit, search, status, and lean fields are present. The first
proposal's two cyclic clause nodes are absent. No node depends on the parent
Noetherianity statement in the repaired split.

Second reading changed: replaced two directional sorry wrappers with direct
completion/descent proofs and one precise presentation comparison; repaired the
DAG, restored the original imports and docstring, removed redundant imports,
and corrected the report's progress and pruning claims.
