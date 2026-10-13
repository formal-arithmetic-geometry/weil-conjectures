## What changed

Replaced both complete `sorry` proofs in
`lean/Sheaf/RingTheory/FormalGlueingIsogeny.lean` without changing either signature.
The proofs now obtain algebraization and torsion from two smaller statements and prove
all four comparison clauses in Lean. Two private, proved helpers handle the unit
map on torsion modules, the flat tensor kernel equivalence, and the tensor quotient
equivalence (the latter two are combined in `torsion_map_comparisons`).

Added the proof imports `Mathlib.RingTheory.Flat.Equalizer`,
`Mathlib.LinearAlgebra.TensorProduct.Quotient`,
`Sheaf.RingTheory.FormalGlueingMapToAlgebraization`, and
`Sheaf.RingTheory.FormalGlueingMapFromAlgebraization`.
All three delivered modules compile without warnings using `lcompile.py --all`.
The required `deliver3.py --no-push` dry run passes, apart from the second reading
that the next worker writes; nothing was pushed.

Updated the original DAG node's proof and proof dependencies to match this reduction.
The two algebraization statements retain the formal-glueing-equivalence route of
steps 1--5; the unit sk-thm-p1 and all its realized statements and steps are retained.

## Proved and sorry left

Closed the original holes:

- `FormalGlueing.exists_map_to_of_torsion_baseChange`;
- `FormalGlueing.exists_map_from_of_torsion_baseChange`.

These are decompositions, not independent proofs of the entire formal-glueing result:
two holes closed and two smaller holes added, with net hole count zero. All four
comparison clauses in each original theorem, including the equations specifying
canonical maps, are proved using Mathlib and the existing torsion base-change theorem.
The original module contains no `sorry`.

New holes, each the whole proof of its named public theorem:

- `FormalGlueing.exists_map_to_algebraization`, node
  `lem-weil-pbc-formal-glueing-map-to-algebraization`, module
  `Sheaf.RingTheory.FormalGlueingMapToAlgebraization`;
- `FormalGlueing.exists_map_from_algebraization`, node
  `lem-weil-pbc-formal-glueing-map-from-algebraization`, module
  `Sheaf.RingTheory.FormalGlueingMapFromAlgebraization`.

Each new statement asserts only algebraization, factorization, and torsion. It omits
all four comparison equivalences and all their naturality equations. The original
proofs construct these omitted conclusions and transport them through beta explicitly;
neither original statement is simply renamed. Existing dependency holes, including
`RingTheory.torsionModule_flat_baseChange_bijective` and
`FormalGlueing.exists_canonical_equivalence`, were not edited.

## No longer needed

Removed direct proof imports from the original module:

- `Sheaf.RingTheory.FormalGlueingData`;
- `Sheaf.RingTheory.FormalGlueingEquivalence`.

Their nodes `def-weil-pbc-formal-glueing-data` and
`prop-weil-pbc-formal-glueing-equivalence`, together with
`def-weil-pbc-module-localization-away` and
`lem-weil-pbc-localization-module-exact`, are now needed only by the two new
algebraization nodes. They remain transitive dependencies; no entire module is claimed
pruned from the targets' closure. The new modules import FormalGlueingEquivalence;
its public import already provides FormalGlueingData, so a second direct import of
FormalGlueingData is unnecessary there. No original mathematical prerequisite has
been discarded from the algebraization plan. There are no globally pruned nodes.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The source TeX is absent in this read-only clone;
read the official source at https://stacks.math.columbia.edu/tag/0ALK instead.
The comparison clauses are available through Mathlib's tensor kernel and quotient
equivalences, so they need no new holed theorem. The existing torsion theorem uses
`M ⊗ S` with the action Module.compHom; the original module uses `S ⊗ M` with
the algebra action. The proof identifies those actions and applies tensor symmetry.
Its positive-exponent convention is handled by replacing n with n+1.

The original node's step 5 used sum e_i and its strict pigeonhole argument without
separately covering an empty generating family. The new docstrings and nodes use
1 + sum e_i, which works also when I = 0. For I = the unit ideal, the hypotheses
force the given map to be an isomorphism and the descended kernel and cokernel to
vanish. For I = 0 all modules are torsion and the quotient-map hypothesis is a ring
isomorphism. These edge cases agree with both new statements; no additional
hypothesis is imposed. Zero modules also satisfy the statements and all comparison
formulas. No data definition chooses an arbitrary witness from an unproved existence
statement: existential modules are unpacked only inside theorem proofs.

LeanSearch returned an internal-server error and is recorded as unavailable.
LeanFinder returned adic-completion lemmas rather than map algebraization. The logged
Mathlib grep found tensor kernel/range lemmas but no formal-glueing algebraization.
The repository and blueprint searches found no smaller existing declaration with
these algebraization conclusions. The original 0ALK node is the only matching
formal-glueing map statement.

## New nodes

`lem-weil-pbc-formal-glueing-map-to-algebraization` implements original steps 1--3
and 5 in a new single-theorem module. Its complete proof plan builds the modified
canonical datum, algebraizes the map by the equivalence, and detects torsion from
its finitely many isomorphic chart maps. It asserts no comparison equivalence.

`lem-weil-pbc-formal-glueing-map-from-algebraization` implements original steps 1,
4 and 5 with inverses in the comparison data, again asserting no comparison
equivalence. Both nodes inherit sec-proper-base-change and sk-thm-p1 and record the
three searches actually run. No definition, existing interface, target, or public
import was changed; no change record or forced adaptation is needed.

## Second reading by H2

1. Interface: read the whole diff against the repository and programmatically compared
   the text of each existing theorem from its name through `:= by`. Both
   `exists_map_to_of_torsion_baseChange` and
   `exists_map_from_of_torsion_baseChange` have byte-identical signatures. Their
   docstrings, public imports, scalar instances, universes and visibility are
   unchanged. No definition or statement changed. Verdict: pass.

2. Proof: independently compiled all three files in import order with `lcompile.py
   --all`, without errors or warnings. The only sorries are the two named public
   algebraization theorems listed above. No forbidden declaration or hollow
   definition occurs. A scratch copy with `#print axioms` checked both private
   helpers, both original theorems and both algebraization theorems: all six show
   only propext, Classical.choice, Quot.sound and sorryAx. The copy was removed.
   Thus this is conditional on open dependencies, not an axiom-free completion.
   Read the helpers: increasing n to n+1 preserves annihilation; equality of module
   actions justifies tensor symmetry; flatness supplies tensorKerEquiv; lTensor_range
   gives exactly the quotient identification. In the map-to proof beta inverse
   restricts to the kernel and beta surjectivity equates ranges. In the map-from
   proof beta injectivity identifies kernels and range_comp transports the range.
   The pure-tensor equations give all eight comparison clauses, including their
   specified values on representatives. Verdict: pass.

3. Split statements: read both new modules and nodes against Stacks
   [0ALK](https://stacks.math.columbia.edu/tag/0ALK),
   [05EL](https://stacks.math.columbia.edu/tag/05EL) and
   [05ER](https://stacks.math.columbia.edu/tag/05ER). Flatness, finite generation,
   quotient-map bijectivity, restricted scalar torsion, both map orientations,
   beta's direction and factorization agree hypothesis by hypothesis. Neither
   split asserts a comparison equivalence; the original module derives those.
   For the map-to node, step 1 uses exact localization to invert phi locally;
   step 2 uses the canonical datum's square to form the modified datum and its
   morphism; step 3 uses exactly essential surjectivity and fullness of
   exists_canonical_equivalence; step 4 uses exact localization and the fraction
   criterion to detect torsion. For the map-from node, step 2 uses localized
   inverses, checks the square by precomposition with a bijection, and algebraizes
   the opposite morphism; steps 1 and 3 give localization and torsion detection.
   Read Data and Hom to check the compatibility equations and components used.
   The finite monomial argument with 1 + sum e_i covers the empty generating family:
   I = 0 and exponent 1. At I = 0 the quotient hypothesis makes R -> S an
   isomorphism. At I = top the torsion hypotheses force phi to be an isomorphism,
   and T = P with psi the identity works. Zero modules and annihilating exponent
   zero cause no exception. Existential witnesses occur only inside theorem proofs.
   Independently searched msearch LeanFinder for algebraization of module
   homomorphisms modulo an ideal, Loogle for `"glue"`, and grep for
   `algebraization|algebraisation|Isogeny|Glueing|Gluing`, plus lean/Sheaf,
   lean/WeilConjectures, upstream WeilConjectures and the upstream name table.
   Results concern flatness, unrelated gluing, or the original theorem and its
   consumers; none supplies the smaller statements. Each new hole has its source,
   full docstring proof and matching node. Verdict: pass.

4. Route and pruning: Mathlib tensorKerEquiv and tensorQuotientEquiv with the existing
   torsion base-change theorem already give the shortest comparison route found.
   Neither algebraization hole closes by a quick application: it requires the
   modified datum, categorical algebraization and torsion detection. Proof-only
   imports are plain imports. FormalGlueingEquivalence is retained in the split
   modules for their proof route and publicly provides Data. Compared old and new
   proof_deps: the four removed direct dependencies are Data, localization-away,
   exact localization and the equivalence. All are listed under No longer needed
   and retained in the new nodes. No module is pruned from the targets' closure.
   Read dag/units/sk-thm-p1.json; no realized statement or step is bypassed or
   changed. Verdict: pass; two holes closed and two added is net-zero decomposition.

5. DAG: the existing node changes only proof, proof_deps and proof_origin. Its four
   steps match algebraization, torsion base change, tensor comparisons and beta
   transport. For all three nodes proof_deps equals the union of step uses. Both
   new nodes have self-contained statements, source, full proof steps, actual
   search records, split status, creator, blueprint provenance, chapter, unit and
   verbatim Lean statements. No proof edge returns to the item; the blueprint via
   chain is provenance. Verdict: pass.

Second reading changed only this report, adding the independent review and explicit
axiom results. No Lean proof, statement, import or node repair was needed.
