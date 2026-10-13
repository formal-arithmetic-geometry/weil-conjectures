## What changed

Proved `HomologicalComplex.isIso_limitPost_homology_of_mittagLeffler` with its original
signature and visibility. The proof follows Stacks Tags 070E, 070D and 02N1. Private,
fully proved helpers construct natural cycle and boundary sequences, prove their
termwise exactness, show cycles commute with the limit, and prove injectivity and
surjectivity of the canonical homology comparison. The boundary tower is the actual
kernel of the homology projection in the functor category; no arbitrary data are
chosen from an unproved existence statement.

Added proof-only Mathlib imports for explicit abelian-group cycle representatives,
abelian functor categories, and componentwise mono/epi instances. The existing public
imports and all public signatures remain unchanged. Updated the item's DAG proof,
proof dependencies and proof origin to describe the implementation.

Source read: https://stacks.math.columbia.edu/tag/070E, /tag/070D and /tag/02N1;
the corresponding local literature files are absent from this machine. Read the unit
record `dag/units/sk-thm-p1.json`; this node is below its realized statements and steps,
and the unit route is preserved. Read both open tower-limit change records affecting
this import chain; neither forces an adaptation here.

## Proved and sorry left

Closed the original sole hole:
`HomologicalComplex.isIso_limitPost_homology_of_mittagLeffler`
(node `lem-weil-pbc-mittag-leffler-complex-limit-homology`).

No `sorry` remains in the delivered module. No new holes, modules, or nodes were added.
This is a proof from existing stated dependencies, not a decomposition. In particular,
it still uses the existing Tag 070D theorem
`CategoryTheory.ShortComplex.isMittagLeffler_iff_of_isEssentiallyConstant`, whose own
proof remains another item's responsibility. The Tag 02N1 theorem supplies the ML
quotient assertion and both short exact sequences on limits.

The module compiles through `lcompile.py` without warnings. Searches through the
launcher LeanFinder, Loogle and grep services and local Mathlib/source-library searches
found no direct comparison theorem. The original statement is unchanged, including
its universe and the non-cyclic Fin 4 complex shape. The proofs of the general private
helpers require the actual adjacent-shape equations; the final instantiation derives
these from the relations 0→1 and 1→2. Zero groups and zero differentials are included;
no surjectivity of the original tower transitions is assumed.

## No longer needed

Removed proof import
`Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels`
and proof dependency node `lem-weil-pbc-tower-limit-exact-surjective-kernels`.
The full short-exact conclusion of the existing Tag 02N1 theorem provides the left
exactness needed here directly in abelian groups. Its module-category exactness
construction and the conversion of abelian groups to integer modules are therefore
unnecessary on this proof route. No other original import or dependency is pruned.
Any other target route using that module remains the maintainer's queue's concern.

## Where the brief, the DAG or earlier work was wrong

The statement is correct and needed no correction. The planned separate appeal to
tower-limit left exactness was redundant with the actual Lean statement of the ML
limit-exactness theorem. The existing docstring records the source's original plan;
the revised DAG and Lean proof record this dependency pruning. No statement,
definition, unit route, or external module was changed.

## Second reading by Y3

1. **Visible declarations — PASS.** Read the complete diff against the repository.
   The sole existing theorem signature is byte-for-byte identical, including its
   universe, visibility, local Fin 4 shape, three hypotheses, and canonical comparison
   conclusion. Its docstring and all public imports are unchanged. Added helpers are
   private; the two helper definitions explicitly construct short complexes from
   cycles, the homology projection, and its categorical kernel. No statement or
   definition change record is required.
2. **Proof and trust — PASS.** Independently compiled the delivered file with
   `lcompile.py`, without errors or warnings. A scratch copy with `#print axioms
   HomologicalComplex.isIso_limitPost_homology_of_mittagLeffler` compiled and reported
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; existing open
   imported dependencies account for the last. No delivered declaration contains
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or a bypass of
   kernel checking. Read all helpers, the cone universal-property proof, and the
   mono/epi argument: the naturality identities identify the actual `limit.post`
   map, and the boundary representatives are lifted only in proofs. No arbitrary
   witness from an unproved existence theorem supplies data to a definition.
3. **Split statements and edge cases — PASS.** There are no split-off holes or new
   public statements/modules/nodes. The private exactness helpers correctly require
   `prev j = i` and, for boundary exactness, `next i = j`; their final uses derive
   these from the genuine arrows 0 to 1 and 1 to 2, with no wrap-around. Zero groups,
   zero differentials, and constant complexes satisfy the same constructions.
   Epic quotient maps, rather than surjective tower transitions, are the only
   surjectivity assumptions in the helpers. Closed one existing hole and added zero.
4. **Route and pruning — PASS.** Read Stacks Tags 070E, 070D, 02N1 and both used
   Sheaf theorem modules. Independently searched LeanFinder for kernel/cycle functors
   preserving inverse limits, Loogle for `cyclesFunctor` and `PreservesLimit`, and
   local Mathlib, upstream, and Sheaf sources for cycle-limit and ML-homology results.
   Mathlib's eventually-constant complex comparison needs stronger degreewise
   hypotheses and does not apply. The explicit cycle-limit proof is valid. All three
   added Mathlib imports serve proofs only and are plain imports. The complete old
   dependency difference is the single reported tower-limit-exactness node: the
   existing Tag 02N1 theorem already supplies its needed left exactness. The item
   lies below the statement and steps in `dag/units/sk-thm-p1.json`; its realized
   route remains unchanged. Read the two tower-limit change records: no adaptation
   here is needed.
5. **DAG agreement — PASS.** The only changed JSON fields are `proof`, `proof_deps`,
   and `proof_origin`. Each step matches the Lean implementation: kernels realize
   boundaries, cycles preserve limits, ML descends through epic quotients, Tag 070D
   gives ML cycles, Tag 02N1 gives both limit exact sequences, and the canonical
   comparison is mono and epi. The dependency union is exact and the source is Tag
   070E. No new-node checks are needed.

Second-reading changes: appended this independent review and recorded the fresh
searches. No Lean proof, signature, definition, import, or DAG repair was necessary.
