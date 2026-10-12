## What changed

Proved `WeilConjectures.DerivedTotalResolution.total_resolution_homology_injective`
from one strictly smaller remaining theorem, with its original signature unchanged.
Added proof-only imports of `Sheaf.Paper.DerivedTotalResolutionColumnZero`,
`Mathlib.Algebra.Homology.Homotopy`, and
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.

The private helpers `toCycles_naturality`, `lift_boundary`,
`homology_exact_of_boundary_lifting`, and `homology_exact_of_cycles_exact` are
fully proved. They implement the exactness of interior and augmented homology
rows from the given term and cycle conditions. The main proof constructs the
column-zero chain map and the explicit column-minus-one null-homotopy, then
uses homology row exactness to kill the kernel. No definitions or interfaces
of existing modules changed. The unused-variable linter is
scoped off for the original theorem to preserve its inherited unused `hp`
binder and negative-column augmentation hypothesis verbatim.

## Proved and sorry left

Closed the item's sole hole:
`WeilConjectures.DerivedTotalResolution.total_resolution_homology_injective`
(node `lem-pc-derived-total-resolution-homology-injective`).

Added one hole, in its own module:
`WeilConjectures.DerivedTotalResolution.total_resolution_column_zero_surjective`
(node `lem-pc-derived-total-resolution-column-zero`). This asserts only that exact
horizontal homology rows allow every total homology class to be represented in
column zero. It has no augmentation, target complex, or injectivity conclusion.
Its docstring and node give the finite-support induction in full.

This is a decomposition: one hole closed, one added, net zero. The exactness
chases, chain-map construction, null-homotopy, and final kernel argument are
proved in Lean. No sorry remains in the item's module or in a definition.

## No longer needed

Removed the first worker's redundant proof-only import of
`Mathlib.Algebra.Category.ModuleCat.Abelian`; compilation still passes without it.
No baseline import, node, or module is pruned. The initial module had no
proof-dependency imports. All four original public imports are retained to
preserve its public interface. The proof does not use the inherited
negative-column augmentation condition; its signature is nevertheless retained.

## Where the brief, the DAG or earlier work was wrong

The old node put exactness of homology rows, finite-support reduction and the
final kernel argument into one step marked elementary. The Lean delivery proves
the row chases and kernel argument, and exposes finite-support reduction as the
remaining task. The rule for the blueprint ancestor follows `created.item`, but
this node's `created.item` is a module name; `blueprint_refs.py ancestor` returned
None. Following the existing parent node's explicit blueprint chain instead
identifies `lem-pc-projection-formula`, used for the new node's provenance.

Read Stacks Homology, Tag 09IZ (`lemma-good-resolution-gives-qis`), including both
proof paragraphs, from the locally available copy of `homology.tex`. Searched
Mathlib via LeanFinder, Loogle, grep and LeanSearch; LeanSearch returned Internal
Server Error and is recorded as unavailable. Checked the new statement on zero
bicomplexes, bicomplexes supported only in column zero, and complexes with zero
vertical differential; the latter reduces to ordinary horizontal exactness.
There is no boundedness assumption on the vertical complexes.

## New nodes

`lem-pc-derived-total-resolution-column-zero`, module
`Sheaf.Paper.DerivedTotalResolutionColumnZero`, isolates the second paragraph of
Tag 09IZ from the first paragraph's homology-row exactness. The new statement
assumes precisely that row exactness and concludes surjectivity from column-zero
homology. No change record or forced adaptation is needed.

## Second reading by K1

1. **Interface preservation: pass.** Read the complete diff of the delivered
   `DerivedTotalResolutionHomologyInjective.lean` against the repository. The
   existing theorem signature, all its hypotheses, universes, conclusion and
   visibility are byte-for-byte unchanged; independently compared the text from
   `theorem total_resolution_homology_injective` to its `:=`. No existing
   definition changed. New helpers are private and fully proved. All added
   imports in the existing module are proof-only. No change record or forced
   adaptation is necessary. The rewritten proof docstring describes the actual
   reduction and does not alter the statement.

2. **Lean proof and axioms: pass as a decomposition.** Compiled both delivered
   modules in import order with `lcompile.py --all`; both passed without warnings.
   Recompiled the main file after removing its redundant Abelian import.
   Scratch copies with `#print axioms` for the four private helpers show only
   `propext`, `Classical.choice`, and `Quot.sound`. The main theorem and the new
   column-zero theorem additionally use `sorryAx`, exactly as expected from
   the one reported split-off hole. Read all proof bodies: the only delivered
   `sorry` is the named theorem `total_resolution_column_zero_surjective`.
   There is no forbidden axiom, unsafe declaration, external implementation,
   holed definition, or arbitrary data selected from an unproved existence
   theorem. The inclusion and null-homotopy are explicit constructions.

3. **Split-off theorem: pass.** Read Stacks Homology Tag 09IZ,
   `lemma-good-resolution-gives-qis`, both proof paragraphs, in the local copy
   `/home/ubuntu/work-bp/sheaf/literature/stacks-project/homology.tex`.
   The new theorem extracts precisely the finite-support paragraph after taking
   horizontal homology exactness as its hypothesis. It assumes no augmentation,
   term exactness, cycle exactness or target complex, and concludes surjectivity
   of the column-zero inclusion, so it is strictly part of the argument rather
   than a renaming of injectivity. For the largest occupied index r>0, exactness
   at A_r is the hypothesis p=-(r+1)<-1; a cycle in A_(r+1) has total degree n-1.
   Subtracting its boundary changes column r but creates no column r+1, and
   subtracting a primitive in A_r changes only columns r and r-1. Thus the
   induction strictly decreases r without a vertical boundedness assumption.
   Checked zero bicomplexes, support only in column zero, zero vertical
   differentials, and support in one strictly negative column: in the last case
   the row hypothesis forces that column's homology to vanish. The docstring
   supplies the construction, signs, base case and termination; its node records
   the same statement and source. Independent LeanFinder search with the query
   beginning "A bicomplex with exact horizontal cohomology" returned only
   support/exact-at and group-cohomology lemmas. Loogle
   `HomologicalComplex.homologyMap, Function.Exact` returned no match.
   The earlier total/Epi query had an unknown-identifier diagnostic and is not
   treated as evidence of absence. Grep searches of Mathlib, repository Sheaf,
   and upstream bicomplex modules found no existing equivalent theorem.

4. **Shortest route and pruning: pass after import repair.** Checked the proved
   boundary-lifting chases, including the separate p=-2 and p=-3 augmented
   cases. At column zero, term surjectivity lifts a boundary primitive directly;
   interior columns use the next exact cycle row. Read the explicit homotopy:
   the inclusion (-1,q) has degree q-1, the vertical sign is -1, and its
   differential cancels the source differential. Surjectivity of H(j), augmented
   homology exactness and this null-homotopy prove the final zero-kernel claim.
   The already proved augmentation-surjectivity theorem has the opposite map
   and does not provide H(j) surjectivity. Upstream
   `total.quasiIso_map_of_finitely_many_columns` requires two column bounds;
   `total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE` additionally imposes
   vertical bounds, unavailable here. Neither gives a shorter specialization.
   Removed only `Mathlib.Algebra.Category.ModuleCat.Abelian`, which was redundant.
   Homotopy and short-complex ModuleCat lemmas are used by the written proof.
   The original node's `proof_deps` is empty, so no old dependency was omitted
   from `No longer needed`. Read
   `dag/units/sk-thm-picard-f-representable.json`: its realized statement and step
   lists are empty on the baseline, and this delivery changes none of them and
   bypasses no existing unit realization. The good-total-resolution route stays.

5. **DAG agreement: pass.** Compared the original node JSON with its sandbox
   version: only `proof`, `proof_deps`, and `proof_origin` changed. The steps
   describe the proved chases, column-zero reduction, explicit null-homotopy
   and kernel argument; the sole proof dependency is the new column-zero node.
   Its source, created record, provenance, chapter/unit, actual logged searches,
   and verbatim Lean signature are present. Its proof-dependency list is empty:
   the finite-support induction is the remaining theorem to formalize, with
   its complete mathematical proof documented. The new statement agrees with
   its node hypothesis by hypothesis and conclusion by conclusion.

**Second-reader changes:** removed one redundant proof-only import and corrected
this report's import/pruning descriptions. Kept the correct proofs and all
statements unchanged. One original hole closed, one strictly smaller hole added,
net zero; this is a decomposition, not an axiom-free proof of the item.
