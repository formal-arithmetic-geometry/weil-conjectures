## What changed

Reduced `AlgebraicGeometry.principalOpenCech_homology_mono_of_injective_terms`
to one-column cancellation and proved singleton gluing. The item proves the finite
induction, preservation of the differential when subtracting boundaries,
degreewise injectivity from sheaf separatedness, and the homology kernel argument
using cycles, opcycles, and the surjective homology projection. All existing
signatures and visibility are unchanged. Two new proof-only imports point to the
new coordinate lemmas; Mathlib supplies the concrete module homology and gluing APIs.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.principalOpenCech_homology_mono_of_injective_terms`
(node `lem-sc-principal-open-cech-injective-terms`). This is a decomposition,
not a sorry-free proof of the full mathematical result. One existing hole is
closed and one new hole is added: the net hole reduction is zero.

Added one strictly smaller hole:

- `AlgebraicGeometry.principalOpenCech_column_step`
  (`lem-sc-principal-open-cech-column-step`): cancellation of one positive column,
  assuming injectivity only of the single coefficient sheaf in that column,
  with no source complex, augmentation, or homology conclusion.

Proved `AlgebraicGeometry.principalOpenCech_singleton_gluing`
(`lem-sc-principal-open-cech-singleton-gluing`) directly from Mathlib's
unique gluing theorem. The explicit pair sum, degree transports, open transports,
and the equality with the augmentation are all proved, without injectivity of
coefficients or any source differential formula.

No holes remain in the item module or in private helpers. No definitions changed
and no data are selected from an arbitrary unproved existence theorem.

## No longer needed

No original imports removed: both public imports are needed for the statement.
Removed the redundant proof imports tried during development:
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`, and
`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing` from the item, and the
last of these from the gluing module. The public imports already expose these
Mathlib APIs.
The original proof dependencies `lem-weil-pbc-module-injective-open-cover-cech-acyclic`
and `lem-pc-alternating-cech-computes` move below the column-step node, so they are
still needed for that smaller item and are not globally pruned. Their modules
`Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic` and
`Sheaf.AlgebraicGeometry.AlternatingCechComputes` are not imported directly into
this item. No node or module is claimed globally redundant.

## Where the brief, the DAG or earlier work was wrong

The original second proof step hid a finite induction and the passage from
explicit boundaries to abstract categorical homology. Both are now proved in Lean.
The planned tuple results have different section/scalar and indexing interfaces,
so positive-row exactness in the actual subset coordinates is isolated explicitly.
The existing ordered-total theorem requires a coordinate bridge and restriction
to the base open, and does not directly apply to the displayed signature.

Read [Stacks Tag 08C1](https://stacks.math.columbia.edu/tag/08C1) online
because the listed local cohomology.tex is absent
on this machine. Its first paragraph invokes the finite-row total argument,
injective Cech acyclicity, and the alternating comparison. Checked empty cover,
empty basic opens, repeated members, and k above the maximal subset cardinality.
The new column lemma allows u=0 when no column k+1 exists. The gluing lemma uses
the empty-family sheaf axiom when r=0. The unit's realized lists are empty and
no unit-level route was replaced.

Searches: LeanFinder and Loogle produced generic injective replacement,
concrete homology, and unique-gluing declarations, without an exact coordinate
lemma. The Mathlib grep confirmed those APIs. LeanSearch returned an internal
server error, recorded as unavailable rather than as a negative search result.
The blueprint search for Cech found no duplicate of either coordinate statement.

## New nodes

`lem-sc-principal-open-cech-column-step` records a single successor step of the
finite-column induction with one injective coefficient sheaf, and its full row-exactness
proof in words. Its module is `PrincipalOpenCechColumnStep`.

`lem-sc-principal-open-cech-singleton-gluing` records only initial-row exactness,
independently of injectivity. Its module is `PrincipalOpenCechSingletonGluing`.
Both inherit the item's chapter, unit, and nearest blueprint ancestor; the parent
node now lists these two proof dependencies and describes the real Lean argument.
There are no change records or forced adaptations because no existing interface
changed.

## Second reading by H2

1. Interface: compared the item with the repository using diff and extracted
   its existing theorem signature. It is byte for byte identical. The only new
   declarations in the item are private proof helpers. No existing definition,
   public import, statement or visibility changed; no change record is needed.
2. Proof: independently compiled all three modules with lcompile.py, in import
   order, without errors or warnings (12.6, 52.9 and 18.8 seconds). The sole
   explicit sorry is principalOpenCech_column_step, exactly the named theorem
   listed above. No hollow definition or forbidden declaration is present.
   Checked separatedness, boundary preservation, finite induction, chain-map
   cancellation and the cycles/opcycles homology argument line by line.
   Scratch #print axioms shows exactly propext, Classical.choice and Quot.sound
   for singleton_gluing; column_step and the main theorem additionally use
   sorryAx, with no other axiom. The delivery probe also checks private helpers.
3. Split statements: column_step is a single finite-induction step with only
   one injective coefficient, no source augmentation and no homology claim.
   It is strictly smaller than the item. Singleton_gluing is already proved
   from Mathlib's sheaf gluing axiom, including explicit degree/open transports.
   Checked r=0, r=1, k=1, k>=r, empty/repeated opens, and characteristic two
   (the signed pair calculation remains valid). Tag 01EP applies to covers of
   any open, so the union need not equal the whole spectrum. Each new theorem
   has a matching node and a complete sourced docstring. Independent LeanFinder,
   Loogle and source grep searches found general exactness/gluing APIs, not this
   subset-coordinate lemma. Loogle did not recognize the newer opcycles or
   compatibility names; direct source inspection verified their APIs instead.
4. Route and pruning: the shortest available coordinate route is used; existing
   tuple/total-complex results require additional indexing, scalar and base-open
   bridges. Reviewed InjectiveTermsAlternatingCechAugmentation and
   InjectiveAlternatingCechRowAugmentation as possible alternatives. Both public
   imports in each delivered module supply its statement, and the item's two
   new imports are proof-only. Both old proof dependencies are listed under
   No longer needed and retained in the column-step plan, so no global pruning
   is asserted. The unit sk-thm-picard-duality has empty realized lists; its
   statement and route are untouched.
5. DAG: the existing node changes only proof, proof_deps and proof_origin.
   Every proof_deps set equals the union of its proof steps' uses. The two new
   nodes have the required source, searches, provenance, chapter, unit and Lean
   fields; their Lean statements match the actual signatures verbatim. The
   main node's stored normalized signature is unchanged from the repository.

Second reading changed only documentation: clarified why row acyclicity applies
on the union open in the column-step docstring and node, corrected new-module
H2 authorship, and explicitly recorded the zero net hole reduction. No proof or
statement needed repair. Closing the remaining column lemma would require the
full tuple/subset bridge, beyond a few-minute repair; it remains an honest hole.
