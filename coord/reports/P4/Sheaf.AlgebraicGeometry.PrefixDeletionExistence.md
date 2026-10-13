## What changed

Proved `AlgebraicGeometry.Scheme.prefixDeletionExistence` with its repository
signature, docstring, visibility and public imports unchanged. The construction
restricts permutations to the complementary position and label subtypes, proves
prefix deletion injective and surjective, and applies `Equiv.ofBijective`.
Proof-only imports are `Sheaf.AlgebraicGeometry.AlternatingCechPartialSortUnique`
and `Mathlib.Data.Fin.Tuple.Sort`.

Repaired all five duplicate-statement findings in the returned delivery:

- Removed `stable_unique`; both callers now use `Tuple.eq_sort_iff` directly.
- Removed `partial_unique`; both callers now use `ExistsUnique.unique` directly
  on `cechPartialSort_existsUnique`.
- Generalized the private restriction construction and `deletePerm_spec` to an
  arbitrary source-complement equivalence. The increasing enumeration is the
  default used by prefix deletion.
- Replaced `stable_delete` with `stable_restrict`, for arbitrary finite sizes
  and strictly increasing position and label embeddings forming a restriction
  square. Its two callers specialize those embeddings to `succAbove`.
- Generalized `stable_compare` to arbitrary linearly ordered position and label
  types and a function with monotone keys and increasing ties; it no longer
  assumes a finite permutation or `cechStableSort`.

The existing tail helpers are private and cannot be imported by their source
names. The repair takes the return's generalization alternative for the three
restriction/order facts and directly reuses existing public results for the two
uniqueness facts. It changes no other module. Updated only the permitted proof
fields of `new-prefix-deletion-existence` to describe this repaired proof.

Deletion constructs data directly from its input. Surjectivity uses the actual
`Tuple.sort` construction and the already proved unique partial-sort theorem
inside a proof, without choosing arbitrary data from an unproved existence theorem.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.prefixDeletionExistence`
(node `new-prefix-deletion-existence`). Added zero holes; split off zero statements.
No `sorry` remains in the module or its private helpers. This is a proof, not a
decomposition. The imported `cechPartialSort_existsUnique` is already proved.

The repaired module compiles cleanly with `lcompile.py`. The exact
`import_prune_check.py` that rejected the previous delivery now exits 0 with no
findings. The `deliver3.py --no-push` dry run prints OK, including its axiom probe
and preflight; only the fresh second reading remains for the assigned reader.
Nothing was pushed. The proof includes p=0,
b=0 and b=p: the inequalities r<a=b+1 give the necessary bounds, including
r=0, a=1, b=0 for p=0. Equal values use the original label as tie breaker;
empty I has no tuple of the required nonzero length. The general restriction
lemma uses only strict monotonicity of its embeddings and the commuting square,
and the general comparison lemma uses precisely monotone keys and increasing ties.

## No longer needed

No original imports or proof-dependency nodes were removed. No module is pruned
from the target closure by this delivery. Removed the duplicated private
`stable_unique` and `partial_unique` declarations and replaced the special
`stable_delete` declaration with the generalized restriction lemma.

The tail-deletion correspondence module and its nodes remain unnecessary for
this prefix-deletion proof: its private helpers are unavailable to importers.
All three retained imports are used. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned proof duplicated five private theorem statements from
`Sheaf.AlgebraicGeometry.AlternatingCechTailDeletionCorrespondence`.
The earlier second reading accepted that duplication because those helpers were
private; the landing checker refused it. This repair removes two duplicate
helpers and mathematically generalizes the other three, rather than renaming
unchanged statements or copying another module. The previous second-reading
section is removed so the repaired delivery receives a fresh independent reading.

The original DAG plan used partial-sort uniqueness without naming it as a proof
dependency. The updated dependencies retain both the sorting definitions and
`lem-pc-alternating-cech-partial-sort-unique`. The unit
`sk-thm-picard-pn` has empty realized statement/step lists for this auxiliary route.

Stacks Tag 01FM introduces stable and partial sorting but omits verification of
the first homotopy identity. Prefix deletion is a combinatorial part of that
verification. The existing theorem statement and docstring remain unchanged;
the recorded proof supplies the verification. No statement is disputed.

## Second reading by P4

Independent second reader, 2026-10-13, reviewing the repaired delivery rather than
its rejected predecessor.

1. PASS: compared the only delivered module with the repository using `diff -u`.
   Also checked the existing theorem signature and docstring byte for byte with
   a script. Both are identical; its visibility and sole public import are
   unchanged. All added declarations are private; there are no changed existing
   definitions, additional public statements, forced adaptations or change records.
2. PASS: compiled the delivered module with `lcompile.py --all`, cleanly in
   2.7 seconds. Regenerated the stale scratch axiom probe from this exact module
   and compiled it separately. `#print axioms` for every private declaration,
   `prefixDeletionExistence`, and `cechPartialSort_existsUnique` shows only
   `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. Scanned the
   delivered source for forbidden declarations and holes: none. Deletion uses
   explicit subtype equivalences. Surjectivity obtains the uniquely determined,
   already proved partial sort inside a proposition proof, and does not create
   data from an unproved existence assertion.
3. PASS: zero statements split off and zero added holes. Reviewed all private
   helper hypotheses and their proofs. `deletePerm_spec` allows arbitrary source
   complement enumeration; `stable_restrict` handles any increasing restriction
   square; `stable_compare` handles arbitrary ordered types. These are actual
   generalizations of the rejected helpers. Uniqueness calls reuse Mathlib and
   the existing library theorem directly. Independently enumerated all 60
   binary-valued tuples for p=0..3 and all filtered permutations, checking all
   444 outgoing/incoming pairs for injectivity, surjectivity, prefix lengths and
   omitted labels. This includes constant keys, p=0 and b=0,b=p. Empty I cannot
   supply a tuple on Fin(p+2). No boundary case requires an extra hypothesis.
4. PASS: read the target proof from the equivalence construction down through
   injectivity, surjectivity and restriction lemmas. Repeated searches with new
   wording: LeanFinder on increasing embeddings and lexicographic monotone keys,
   Loogle on `Equiv.subtypeEquiv, Equiv.trans`, and source `rg` on sorting,
   restriction and comparison names. Results provide sorting/list and equivalence
   infrastructure, not a shorter theorem for this correspondence. Read the
   nearby tail-deletion and prefix-restriction modules: their related helpers
   are private and their statements are special cases of the repaired helpers.
   All imports serve their declared roles: sorting predicates in the unchanged
   public import, partial-sort uniqueness and Tuple.sort in proof-only imports.
   `## No longer needed` correctly reports no removed original dependency or
   pruned module. The unit sk-thm-picard-pn has empty realized statement/step
   lists for this auxiliary result; neither the unit nor chapter route changes.
5. PASS: compared the delivered node JSON with its repository version. Only
   `proof`, `proof_deps`, and `proof_origin` differ. The proof steps accurately
   describe explicit deletion, uniqueness-based injectivity and surjectivity.
   Their `uses` union is exactly `proof_deps`, including the actually used
   partial-sort uniqueness node. The Lean declaration recorded in the node
   retains the exact theorem signature. No new node needs validation.

Second reading changed only this report and the scratch axiom probe: the latter
was stale and still contained the rejected duplicate helpers. No delivered Lean
or node change was necessary. Closed one original hole, added zero holes, split
off zero statements; no module pruned.
