## What changed

The existing theorem `AlgebraicGeometry.Scheme.exists_finiteFreeResidueModel` keeps its
signature and docstring byte for byte. Its proof takes the strictly perfect neighbourhood
at the prescribed point from `hE x`, applies two intermediate results, and combines their
conclusions. The two new modules state those strictly smaller results: fibre finiteness
and bounded support from a local strictly perfect representative; and spreading a minimal
free model, given that representative and the fibre data. Both are still open.

The second reader repaired the missing perfectness assumption in the new existence lemma.
Both helpers now take an explicit local strictly perfect representative, rather than
assuming that finiteness at a single fibre implies perfectness nearby. New helper docstrings
contain complete natural-language proofs, sources, and their own matching blueprint ids.
New node signatures, statements, searches, proof plans, and ancestry were repaired. The
existing node's proof and proof dependencies now describe the actual reduction.

Six unused proof imports were removed from the item. Four of these are retained as plain
proof imports of the spreading lemma. Its public imports are only PerfectComplex and
DerivedFiberBetti, needed to express its statement; it no longer publicly imports the
fibre-finiteness helper. No definition, instance, existing signature or public import was
changed, and no change record or forced adaptation is needed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.exists_finiteFreeResidueModel`
(node `lem-sc-perfect-finite-free-residue-model`). Its Lean proof is complete, conditional
on the two new intermediate statements.

Holes added and left:

- `AlgebraicGeometry.Scheme.finiteFiberData`
  (`lem-sc-perfect-finite-free-residue-model-data`), in
  `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModelData`.
- `AlgebraicGeometry.Scheme.finiteFreeModel_of_fiberData`
  (`lem-sc-perfect-finite-free-residue-model-existence`), in
  `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModelExistence`.

This is a decomposition, not an axiom-free proof of the item: one upper hole is replaced
by two lower holes (local hole delta -1). No net progress in the targets' import closure
is claimed; the pinned sorry ledger determines that figure after landing. Every remaining
sorry is the whole proof of one public named theorem, not part of a definition. Scratch
`#print axioms` checks allow only the three standard axioms and `sorryAx` for these holes.
No arbitrary object is defined by choosing a witness from either open theorem.

## No longer needed

Removed direct imports from the item:

- `Sheaf.Algebra.Homology.AffinePerfectColimitDescent`
- `Sheaf.AlgebraicGeometry.AffinePerfectHomColimit`
- `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`
- `Sheaf.CategoryTheory.DerivedCategory.PerfectScalarExtension`
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`
- `Sheaf.RingTheory.MinimalFreeModel`

Old proof dependencies no longer used directly by the item's written proof:

- `lem-sc-perfect-pullback-perfect-residue`
- `lem-sc-perfect-local-pseudocoherent-free-model`
- `def-pur-pseudo-coherent-complex`
- `lem-pc-affine-perfect-colimit-descent`
- `lem-pc-affine-perfect-hom-colimit`
- `lem-weil-pbc-finite-projective-standard-free-cover`

`def-pc-perfect-complex` remains used. The local model, colimit descent, Hom colimit,
and standard free cover dependencies remain in the new spreading lemma and its imports;
they have been relocated, not removed from this item's transitive proof route. The scheme
pseudo-coherence definition and separate ring scalar-extension theorem are not needed by
the new route: fibre finiteness follows by termwise pullback of the bounded local flat
representative, while local pseudo-coherence follows from its finite free localized terms.
No claim is made that any module becomes unreachable from all targets.

## Where the brief, the DAG or earlier work was wrong

The first worker's `finiteFreeModel_of_fiberData` was false: its assumptions did not assert
perfectness, pseudo-coherence, or a local finite presentation of E. Counterexample:
on Spec Z let E be the degree-zero quasi-coherent sheaf associated to the direct sum of
Z/q over all odd primes q, and take x = (2). Derived tensor with F_2 is zero, since every
summand has zero tensor and Tor with F_2 and tensor commutes with direct sums. Thus all
fibre cohomology and Betti numbers are zero and both given fibre hypotheses hold. Every
principal open containing (2) inverts an odd integer f and leaves infinitely many summands
nonzero (only finitely many prime q divide f). Hence E is nonzero on every neighbourhood
of x. The claimed model would have all terms free of rank zero, so would force E to vanish
on some such neighbourhood, a contradiction. The unreleased helper was repaired; no false
statement is delivered. The original theorem itself is unchanged and has the required
perfectness assumption.

The earlier docstrings only said "the corresponding step" and were not complete proofs.
Both also carried the original item's blueprint id instead of their own node ids. The
existence node's Lean statement was prose rather than its signature, and both proof plans
and dependency lists were placeholders. Searches recorded by the first worker were not
accepted as evidence: the second reader performed new searches and recorded their results.
The report's earlier claim "None" under pruning was incomplete.

Sources checked directly: [Stacks Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
for fibre finiteness and spreading; [Stacks Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
for the local minimal free model. The revised docstrings expand the original node's
spreading argument, including descent of the isomorphism, its inverse, and both identities.

## New nodes

`lem-sc-perfect-finite-free-residue-model-data` states just fibre finiteness and support,
from a strictly perfect neighbourhood of the prescribed point. It does not produce any
new neighbourhood or free model. Its proof computes the fibre by a bounded flat complex
and uses finite-dimensional subquotients over the residue field.

`lem-sc-perfect-finite-free-residue-model-existence` assumes that local representative and
the fibre data and states just the existence of the prescribed-rank model. Its proof uses
the existing local-ring minimal model and descent declarations, followed by a finite
standard free cover and sheafification. Neither helper restates the conjunction of the
original theorem; each is a distinct part of its argument. Both nodes have self-contained
statements, definition dependencies, complete proof plans, matching verbatim signatures,
the required search kinds (LeanSearch was unavailable), creation records, and the original chapter/unit and ancestry.

## Second reading by B3

1. Compared the original and delivered item with `diff` and checked the theorem signature
   by literal string equality. Verdict: the sole existing declaration's signature and
   docstring are unchanged byte for byte. All statement repairs concern new unreleased
   helpers. No target, definition, existing public import, or other module was changed.
2. Compiled all three delivered modules locally in import order with `lcompile.py`.
   Verdict: no errors or warnings. There are precisely the two listed named theorem
   holes; no axiom, unsafe, opaque, implemented_by, extern, or holed definition. Scratch
   axiom prints confirm only standard axioms plus sorryAx from the two open lemmas.
3. Read both new statements from hypotheses to conclusions and checked zero complexes,
   empty schemes (no point), negative/shifted degrees, and zero fibre ranks. Verdict:
   the first version of the spreading statement was false, as above; the repaired version
   is true. The helpers are strictly parts of the original argument. Complete proofs in
   words and matching nodes now accompany them. Fresh LeanFinder, Loogle and Mathlib grep
   searches plus `rg` over both source roots found no duplicate scheme statements. The
   existing ring minimal-model theorem and finite standard free cover are used in the
   spreading plan; t-structure representatives from Mathlib do not give free terms or
   residue rank control. Neither open helper can be closed by a short application of
   those results: the sheaf/ring and derived-fibre comparison bridges remain substantial.
4. Read the item top down and examined the imported dependencies and shortest available
   routes. Verdict: the reduction uses the perfectness witness at x explicitly; no unit
   route is bypassed. `dag/units/sk-prop-av-cube.json` has empty realized lists and an
   unchanged cube-theorem step. This refinement stays below that unit and keeps the local
   minimal-model/descent argument. Removed unused direct imports and listed every old
   proof dependency no longer directly used, distinguishing relocation from global pruning.
5. Read the original and new nodes with the Lean open. Verdict: the original proof record
   now lists the two helper applications and local perfectness. Each new statement and
   recorded Lean signature agree; proof_deps is the union of proof-step uses, and the
   source, origin, searches, creation, blueprint ancestry, chapter and unit are supplied.
   LeanSearch was attempted for each helper but returned Internal Server Error; this is
   recorded as unavailable with no no-match verdict. Independent LeanFinder, Loogle and
   source grep supplied the usable searches. New blueprint tags are the new ids. Node metadata no longer contains placeholder proof
   descriptions or a prose Lean signature.

Changes made by this reading: repaired false spreading hypothesis using a local strictly
perfect model in both helper interfaces and both applications; expanded proof docstrings;
corrected blueprint tags; pruned direct imports and a redundant public helper import;
repaired all three proof-node records and search evidence; replaced the misleading report
with an explicit decomposition and hole accounting.
