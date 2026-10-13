## What changed

Proved `DerivedCategory.exists_unique_minimalFreeModel` in
`Sheaf.RingTheory.MinimalFreeModel`, with its signature and existing docstring unchanged.
The proof constructs the zero-differential residue complex explicitly, lifts it with
`DerivedCategory.exists_stablyFree_lift_mod_ideal`, recovers the prescribed ranks by
`Module.finrank_baseChange`, and proves uniqueness by a comparison followed by Nakayama.
No definition takes data from an unproved arbitrary-existence theorem.

Added two fully proved modules, imported privately by the item:
`Sheaf.RingTheory.ResidueCohomologySplit` and
`Sheaf.RingTheory.MinimalFreeComparison`. The first constructs a quasi-isomorphism
from a specified zero-differential complex into the original field complex by lifting
through the homology projection. The second uses K-projective derived-morphism
bijections to build homotopy equivalences, transports them by scalar extension,
forces zero reduced differentials using dimension inequalities, and proves the
comparison components are isomorphisms after reduction.

The item's private helpers prove that a finite free module has the asserted rank
from the rank of its reduction, and that an isomorphism after residue-field
extension lifts to an isomorphism. The latter uses Mathlib's
`IsLocalRing.split_injective_iff_lTensor_residueField_injective` twice.
The `noncomputable section` accommodates the chosen derived-category instance
for the residue field and its definitionally equal quotient-ring presentation.
All original public imports remain unchanged. Added the proof import
`Mathlib.RingTheory.LocalRing.Module`. Updated the item's DAG proof to match
this implementation and added nodes for the two proved intermediate statements.

## Proved and sorry left

Closed the only hole in the item:
`DerivedCategory.exists_unique_minimalFreeModel`
(node `lem-sc-perfect-local-pseudocoherent-free-model`).

Also proved, with no holes:
`CochainComplex.exists_quasiIso_from_zeroDifferential`
(node `lem-sc-residue-cohomology-zero-complex`) and
`DerivedCategory.exists_minimalFree_comparison_residue`
(node `lem-sc-minimal-free-comparison-residue`). All private helpers are proved.

Holes closed in the item: 1. Holes added: 0. No `sorry` remains in any delivered module.
This closes the item from an existing planned dependency; it does not claim to close
that dependency's hole. The existing imported declaration
`DerivedCategory.exists_stablyFree_lift_mod_ideal`
(node `lem-sc-pseudo-coherent-lift-stably-free-complex`) remains the proof's outstanding
library dependency.

The three modules compile together in import order without errors or warnings through
`lcompile.py --all`. The finite-dimensional argument covers zero ranks and vanishing
complexes; no positivity, Noetherian, or bounded-below assumption was introduced.
The original universes and target statement are preserved.

## No longer needed

Removed the item's private import `Sheaf.Algebra.Homology.BoundedFlatKFlat`.
Its node `lem-pc-module-bounded-flat-kflat` is no longer a direct proof dependency of
this theorem, and was removed from its `proof_deps`. The comparison with the chosen
finite free representative is a homotopy equivalence, preserved by additive scalar
extension, so computing and comparing reductions here needs no K-flat theorem.
This is pruning of the item's direct dependency; it is not a claim that the entire
module has left the targets' import closure, since other modules may still need it.

The existing derived-map representative node
`lem-pc-ring-derived-map-representative` is still needed, now in the proved comparison
module. The Nakayama node `lem-weil-pbc-nakayama-local-generators` remains needed via
Mathlib's split-injectivity consequence. The stably-free lifting node remains needed.
No other planned nodes or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

The proof steps marked elementary in the old DAG conceal substantial glue:
splitting a field complex into its cohomology, producing the comparison homotopy
equivalences, proving the reduced differentials vanish, and lifting component
isomorphisms. This delivery supplies that glue as complete Lean proofs rather than
leaving additional holes.

The old plan transports differentials to new displayed free modules after finding
the ranks. The statement only asks for termwise isomorphisms, so the lifted complex
itself already supplies the witness, without transporting any differential.
The old plan's K-flat invocation is unnecessary for this proof because all compared
representatives are bounded above and projective. Its original docstring and legacy
`tool_uses` metadata were preserved; only the permitted proof fields were updated.
The unit and chapter route were preserved.

The local checkout does not contain `literature/stacks-project/more-algebra.tex`.
Read the source directly on the official Stacks page
https://stacks.math.columbia.edu/tag/0BCC. Its current numbering is Lemma 15.77.6;
the stable tag is unchanged. The node proof origins mark the expanded Lean glue
as written by R2 from that source. LeanSearch was attempted for the new statements
but returned Internal Server Error; Loogle/LeanFinder and local Mathlib/DAG/blueprint
searches supplied the available search evidence.

## New nodes

`lem-sc-residue-cohomology-zero-complex`, in
`dag/nodes/sec-abelian-varieties/lem-sc-residue-cohomology-zero-complex.json`, records
`CochainComplex.exists_quasiIso_from_zeroDifferential` in
`Sheaf.RingTheory.ResidueCohomologySplit`. It is a general field-complex statement,
strictly the splitting step of the original proof, and is fully proved.

`lem-sc-minimal-free-comparison-residue`, in
`dag/nodes/sec-abelian-varieties/lem-sc-minimal-free-comparison-residue.json`, records
`DerivedCategory.exists_minimalFree_comparison_residue` in
`Sheaf.RingTheory.MinimalFreeComparison`. It gives a chain comparison whose residue
components are isomorphisms, stopping before the Nakayama argument. It is fully
proved from Mathlib and has no new unresolved dependencies.

Both nodes inherit the item's chapter and unit and trace the same blueprint ancestor.
No existing statement or definition changed, so no change record is needed.

## Second reading by R2

1. **Unchanged interface: PASS.** Compared the delivered item with the repository by
   `diff`, and checked its existing theorem signature byte for byte. Its statement,
   universes, hypotheses, conclusion, docstring and public imports are unchanged.
   The other two modules are new; no existing definition is changed. There are no
   adaptations or statement changes requiring a change record.
2. **Proof and axioms: PASS.** Compiled all three modules in import order with
   `lcompile.py --all`, without errors or warnings. Searched every delivered Lean
   source for `sorry` and forbidden declarations: none. Scratch copies with
   `#print axioms` verify the two new public theorems use only `propext`,
   `Classical.choice`, and `Quot.sound`. The item's theorem additionally uses
   `sorryAx` from the existing stably-free lifting theorem, reported above.
   The residue complex is explicitly constructed. All choices in helper constructions
   use proved facts; extracting the lifted complex occurs only inside a theorem proof,
   not a definition of data from an unproved arbitrary existence statement.
3. **New statements: PASS.** Read both proofs in full. They are strictly intermediate
   splitting and comparison results, and both are completely proved, not new holes.
   Checked zero-dimensional terms, the zero complex, and non-Noetherian local rings:
   no positivity, bounded-below, or Noetherian hypothesis is needed. Independent
   LeanFinder search for a chain complex over a field admitting a quasi-isomorphism
   from a zero-differential homology complex found no direct public theorem. Local
   searches found the related `exists_quasiIso_of_zero_differential` in
   `WeilConjectures.CategoryTheory.DerivedCategory.Perfect`, but it is private,
   chooses a different complex, and cannot be imported as a reusable declaration.
   Loogle's combined HomotopyEquiv/IsKProjective query yielded no usable match;
   local Mathlib searches confirm that the K-projective bijection already used is
   the relevant public API. No duplicate public statement was found.
4. **Route and pruning: PASS.** Checked the argument against Stacks Tag 0BCC
   (https://stacks.math.columbia.edu/tag/0BCC) and the unit's `realized` record.
   This proof changes only the algebraic implementation below the unit level.
   The old K-flat dependency is unnecessary for these reductions: additive extension
   of scalars preserves the explicitly obtained homotopy equivalences. The report
   lists the removed K-flat import and explains that the derived-map representative
   dependency remains transitively used by the comparison module. The lifting and
   Nakayama steps remain. Imports serve either statements or the proof APIs.
5. **DAG correspondence: PASS.** Compared original and delivered node JSON. Only
   permitted proof fields of the original node changed. Its proof dependencies are
   exactly the named splitting, lifting, comparison and Nakayama steps. The two new
   nodes contain source, complete proof steps, search evidence, creation information,
   blueprint ancestry, chapter/unit and matching Lean records. No split-off holes
   or restatements are hidden by these records.

Second-reading changes: narrowed the new splitting module's public import
`Mathlib.Algebra.Category.ModuleCat.Free` to
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat` and
`Mathlib.RingTheory.Finiteness.Defs`, which supply its public homology and finiteness
interface without exporting the unrelated free exact-sequence theorems. Recompiled
successfully. Added this review and recorded the independent duplicate searches.
The mathematical proofs were correct and were left unchanged.
