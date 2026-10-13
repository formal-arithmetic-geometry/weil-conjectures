## What changed

Replaced the sorry in
`AlgebraicGeometry.exists_constant_fibre_dimension_neighbourhood_of_stalk_dimension_zero`
with a complete Lean proof from the existing restricted-fibre Noetherianity theorem,
the already proved depth-support bound, and two new geometric intermediate theorems.
The original signature and visibility are unchanged. All four proof dependencies
have ordinary, non-public imports. No other existing module is changed.

The proof first makes the fibre stalk Noetherian, applies
`IsLocalRing.depth_le_supportDim` and `Module.supportDim_self_eq_ringKrullDim`, and
uses nonnegativity of depth and the dimension-zero hypothesis to prove the exact
Cohen-Macaulay depth equality. It constructs the open Cohen-Macaulay locus from
its set and the openness theorem. The partition theorem provides dimension pieces;
`Opens.mem_iSup` selects the piece containing x and proves that each of its points
lies over U. This is an existential theorem proof, with no new data definition or
choice of data from an unproved existence theorem.

Two new modules state the unformalized geometric steps, one theorem per module:
`Sheaf.AlgebraicGeometry.RestrictedFibreCohenMacaulayLocus` and
`Sheaf.AlgebraicGeometry.CohenMacaulayFibreDimensionDecomposition`.
Both use the existing `IsLocalRing.depth`; no second Cohen-Macaulay definition is
introduced. Their docstrings include sources and the restriction, local-ring,
and local-dimension transports needed to prove their statements.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.exists_constant_fibre_dimension_neighbourhood_of_stalk_dimension_zero`
(node `lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk`).
The item has no sorry left. Its proof depends on the following two new holes, so
this delivery is a decomposition, not an unconditional proof of the geometric result:

- `AlgebraicGeometry.isOpen_fibre_depth_eq_ringKrullDim_over_restrict`
  (node `lem-sbc-restricted-fibre-cohen-macaulay-locus-open`), in
  `Sheaf.AlgebraicGeometry.RestrictedFibreCohenMacaulayLocus`.
- `AlgebraicGeometry.exists_fibre_dimension_open_partition_of_depth_eq_ringKrullDim`
  (node `lem-sbc-cohen-macaulay-fibre-dimension-decomposition`), in
  `Sheaf.AlgebraicGeometry.CohenMacaulayFibreDimensionDecomposition`.

Each has proof exactly `:= by sorry`. Neither restates the original theorem: the
first only proves openness of a locus and does not assert dimension constancy;
the second partitions an entire open with Cohen-Macaulay fibres and assumes no
chosen point or dimension-zero stalk. The combination and the depth-zero argument
are proved in the item's module. Holes closed: 1. Holes added: 2. Net: -1.

Local compilation of the delivered modules in import order passed without warnings.
The delivery dry run supplies the declaration/axiom checks and preflight result.

## No longer needed

None: no existing import, node or module of the planned route is pruned.
`Sheaf.AlgebraicGeometry.RestrictedFibreLocallyNoetherian` remains necessary for the
Noetherian hypothesis of the depth bound. The Artinian-ring detour in the informal
argument is unnecessary: the existing depth bound proves the Cohen-Macaulay
criterion directly. This detour had no separate node or module to prune.

## Where the brief, the DAG or earlier work was wrong

The existing node's second and third steps cite no declarations: the library has
neither the Cohen-Macaulay locus openness statement of Tag 045U nor the relative
dimension decomposition of Tag 02NM. The two new nodes make these steps actionable.
The first step's proposed empty-regular-sequence argument needs an upper bound to
establish depth zero; the existing, already proved depth-support bound supplies it.
No statement is disputed or changed.

Read the sources at https://stacks.math.columbia.edu/tag/045U (1), (2),
https://stacks.math.columbia.edu/tag/02NM,
https://stacks.math.columbia.edu/tag/02NJ, and
https://stacks.math.columbia.edu/tag/0A21 (3), (5).
Tag 02NJ is a definition of relative dimension, not by itself a theorem relating
it to the infimum of neighbourhood dimensions. Tag 0A21 (5) gives the latter for
locally algebraic schemes. The new partition node includes this missing source.
The unit record `sk-prop-normal-form` has empty realized lists; the existing
Cohen-Macaulay/relative-dimension route is preserved rather than bypassed.

Checked edge cases before stating the new lemmas: empty X, empty U and empty W
give an empty locus and the all-empty partition. No assertion is imposed on empty
fibres. For an affine line over a field the fibre stalk at the generic point has
ring dimension zero but the piece has local topological dimension one, so no
incorrect zero-dimensional conclusion is made. For a fat point over a field the
Artinian local ring has depth and dimension zero and belongs to the dimension-zero
piece; no reducedness or regularity hypothesis is needed. A disjoint union of
Cohen-Macaulay components of different dimensions lies in different pieces, so the
partition does not incorrectly impose a single global dimension. Flatness and
local finite presentation are assumed only over U, with all pieces inside its
inverse image. These checks do not formalize the two remaining geometric proofs.

## New nodes

`lem-sbc-restricted-fibre-cohen-macaulay-locus-open` records Tag 045U (1), (2) in
terms of the existing depth definition and the original fibre stalks over U.
Its new module is `Sheaf.AlgebraicGeometry.RestrictedFibreCohenMacaulayLocus`.
Its statement is openness only, and its proof explains identification with the
restricted morphism's Cohen-Macaulay locus and mapping that open back into X.

`lem-sbc-cohen-macaulay-fibre-dimension-decomposition` records the clopen relative
dimension decomposition of Tag 02NM in terms of opens of X, together with local
fibre dimension transport from Tags 02NJ and 0A21 (3), (5).
Its new module is `Sheaf.AlgebraicGeometry.CohenMacaulayFibreDimensionDecomposition`.
The family covers W and is pairwise disjoint; these are a global decomposition
statement, independent of the zero-dimensional point in the item.

For both nodes LeanSearch was attempted but returned an Internal Server Error;
LeanFinder and Mathlib grep found no matching theorem. Searches of the entire
library and DAG found no existing Cohen-Macaulay locus or dimension-decomposition
node; the blueprint search for Cohen-Macaulay returned zero matches. Supporting
flatness, smooth-locus openness and depth bounds do not prove these statements.
No change record is required because existing statements and definitions are
unchanged. The item's proof, proof_deps and proof_origin now follow its Lean proof.

## Second reading by C3

1. **Unchanged interfaces: PASS.** Read all three delivered modules and diffed the
   existing module and its node against the repository. The existing theorem's
   universe, binders, instance hypotheses, dimension-zero assumption and complete
   existential conclusion are byte-for-byte unchanged. Changes there are three
   ordinary proof imports, the proof and its explanatory docstring; there is no
   change to an existing definition, statement, visibility or public import. The
   two other modules and nodes are new. The existing node differs only in proof,
   proof_deps and proof_origin. No change record or forced adaptation is needed.

2. **Kernel proof and holes: PASS as a decomposition.** Compiled all three files
   in import order through lcompile.py with no errors or warnings. Independently
   printed axioms of all three delivered declarations in a temporary scratch copy:
   exactly propext, Classical.choice, Quot.sound and sorryAx. Also printed axioms
   of IsLocalRing.depth_le_supportDim: just the three standard axioms. Read the
   construction of depth and the depth bound; the latter applies to the actual
   nontrivial Noetherian fibre stalk, obtained using the restricted-fibre theorem.
   Nonnegativity uses the coercion from ENat, and hdim supplies the reverse bound.
   The opens, membership transport and existential selection are actual Lean
   proofs. No definition is added and no data is selected for a definition from
   an unproved existence theorem. The only textual sorries are the two listed
   named new theorems, each with proof exactly by sorry. No forbidden declaration
   or kernel bypass occurs. The scratch file was removed.

3. **Split statements and sources: PASS.** Independently read Stacks 045U (1), (2),
   02NM, 02NJ, 0A21 (3), (5), and 00N8 together with Definition 10.103.1 in 00N2.
   The locus theorem is exactly openness over a flat locally finitely presented
   restriction, expressed using depth of the Noetherian local ring as a module
   over itself. The partition theorem restricts that same morphism to an arbitrary
   open W all of whose fibre stalks are Cohen-Macaulay; 02NM supplies its disjoint
   clopen relative-dimension pieces. By 02NJ and 0A21 (5), dimension at any point of
   a nonempty fibre of the nth piece is n; open-subspace transport gives the
   original fibre dimension. These are two distinct geometric steps, not copies
   of the item's chosen-point, dimension-zero statement. Both have standalone
   docstring arguments and matching new nodes. Rechecked empty X/U/W, a fat point,
   the generic point of an affine line, and disjoint Cohen-Macaulay components of
   different dimensions: no unwanted nonemptiness, reducedness, smoothness, or
   globally fixed dimension is imposed. All assumptions are used over U only.
   Independent LeanFinder searches using depth-equality and dimension-stratum
   formulations returned flatness/openness, smoothness and module-rank results,
   none of which imply these theorems. Mathlib grep with fibre/fiber-dimension and
   Cohen/Macaulay terms likewise found no match. Searched lean/Sheaf, the upstream
   AlgebraicGeometry files and DAG source tags; smooth results require stronger
   hypotheses, and the existing dimension_locally_algebraic theorem concerns only
   irreducible schemes over a field, not the missing relative decomposition.
   No quick proof closes either geometric hole from available declarations.

4. **Reduction and pruning: PASS.** Read the old proof dependency and the unit
   sk-prop-normal-form record, including its two steps and empty realized lists.
   The old sole dependency, restricted-fibre local Noetherianity, is still used.
   The Cohen-Macaulay/relative-dimension route is retained and no unit is bypassed.
   The proof uses the already proved depth-support bound directly, avoiding a new
   Artinian-ring lemma. Every ordinary proof import is used; public imports provide
   notions in the signatures. No old module or node is pruned, so No longer needed
   is complete. Pairwise disjointness in the partition is the standard source
   decomposition property, although the final existential selection needs only
   its cover and dimension clauses. The report correctly counts one hole closed,
   two added, net -1: decomposition, not an unconditional geometric proof.

5. **DAG agreement: PASS after citation repair.** Matched all Lean statements with
   the verbatim lean.statement records and the informal node hypotheses and
   conclusions. The item's steps now follow its proof: Noetherianity plus the
   depth bound; locus and partition; elementary supremum membership. Their uses
   have union exactly proof_deps. New nodes have source, proof, proof_origin,
   searches, status, created, blueprint ancestry, chapter/unit and complete Lean
   records. The partition's open-subspace dimension transport already has a
   proved library declaration: IsOpen.topologicalKrullDimAt_eq, recorded on
   lem-weil-pbc-dimension-at-point-open-subspace. Added that existing node to the
   transport step and proof_deps, and named its declaration in the new module's
   docstring. Its module was already imported for the statement's dimension
   notion; this repair adds no import, statement or hole.

Second-reading changes: the preceding explicit citation of the existing proved
open-subspace dimension lemma, and this review report. The Lean proof and all
signatures were retained. Final compile/axiom checks and preflight are performed
by the required delivery dry run before pushing.
