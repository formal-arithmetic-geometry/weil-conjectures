## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Etale.finiteEtaleTrace_section_descent` by a complete proof from
explicit splitting data, a proved covering theorem, a proved local-sum compatibility
theorem, and Mathlib's sheaf amalgamation theorem. The original statement and docstring
are unchanged. The family value is chosen from a unique characterization by every
splitting, rather than by choosing arbitrary splitting data from an unproved existence
statement. Splitting data are eliminated into proposition goals only.

The new splitting module uses only `Mathlib.AlgebraicGeometry.Sites.Etale` and
`Mathlib.Algebra.Category.Grp.Basic`; the second reader removed the unnecessary
six-functor and AB imports.

New modules:
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceSplitting`: explicit finite clopen splitting,
  presieve of split domains, sheet section morphism, and its finite sum.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceSplitCover`: proves that this presieve covers,
  using the existing finite étale local splitting theorem on the base-changed morphism.
  Pullback symmetry and pasting transport its coproduct and inverse projections.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceSplitReindexing`: the remaining geometric
  statement about local bijections of sheets and equal composite section morphisms.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceSplitSumCompatibility`: proves compatibility
  from local reindexing by additivity, `Fintype.sum_equiv`, functoriality, and separatedness.

The descent proof builds the matching family on all split arrows. It applies
`Presieve.IsSheaf.isSheafFor`, proves the requested formula for any explicit splitting,
then identifies every other characterized section with the same amalgamation.

All modules compile through lcompile.py. Edge cases were checked mathematically:
empty finite index sets are allowed; distinct index cardinalities force the common
base to be empty, where the empty presieve covers; the covering construction uses the
empty point-indexed family for an empty base. No connectedness, nonemptiness, or
surjectivity of f is added. Finiteness of f is used only to obtain the splitting cover.
The compatibility and reindexing statements need only the supplied finite splittings.
The unit route through the trace retraction remains unchanged.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.finiteEtaleTrace_section_descent`
(node `lem-weil-pbc-finite-etale-trace-section-descent`).

Also proved the new theorems:
- `AlgebraicGeometry.Etale.finiteEtaleTrace_split_cover`
  (`lem-weil-pbc-finite-etale-trace-split-cover`).
- `AlgebraicGeometry.Etale.finiteEtaleTrace_split_sum_compatibility`
  (`lem-weil-pbc-finite-etale-trace-split-sum-compatibility`).

Added one hole:
`AlgebraicGeometry.Etale.finiteEtaleTrace_split_reindexing`
(node `lem-weil-pbc-finite-etale-trace-split-reindexing`). Its whole proof is exactly
`by sorry` in its own module; its docstring and node give the complete argument.
It asserts only geometric local sheet correspondence, with no sheaf or global section.
There are no other sorries in the delivered modules. This is a decomposition with
one original hole closed and one smaller hole added, hence net zero holes. It is not
an axiom-free proof of the entire trace construction. The local splitting theorem
already imported from the library remains a dependency.

## No longer needed

Removed the direct proof import `Sheaf.Paper.FiniteEtaleEtaleLocalSplit` from the item;
it remains needed through `Sheaf.AlgebraicGeometry.FiniteEtaleTraceSplitCover`.
The existing public imports remain unchanged to preserve the module interface.

The old direct proof dependencies removed from the descent node are:
- `def-pc-fibre-product`;
- `def-weil-closed-immersion`;
- `def-weil-open-immersion`;
- `def-weil-pbc-etale-site`;
- `lem-weil-pbc-etale-base-change-finite-limits`;
- `lem-weil-pbc-etale-composition-cancellation`;
- `lem-weil-pbc-etale-covering-base-change`;
- `lem-weil-pbc-finite-etale-etale-local-split`;
- `lem-weil-pbc-open-fibre-product`.
All except covering base change remain dependencies of the new splitting, covering,
or reindexing nodes. This is a change of direct dependency edges, not nine pruned nodes.

None of the original geometric nodes is globally pruned by this reduction: the
covering and local reindexing nodes still use the original splitting, pullback,
clopen, étale-composition, and site theory. The original separate covering-base-change
node is no longer needed for this item's descent route: the split covering is obtained
by applying local splitting directly to `W ×[X] Y → W`, and gluing uses the full
presieve of split domains. The local-sum proof uses geometric reindexing on a common
source, not a chosen cover and successive covering base changes. Thus
`lem-weil-pbc-etale-covering-base-change` is removed from this item's proof dependency
closure, although other library modules may still need it. It is a Mathlib leaf with
no project module to remove. No source-library imports or public imports were removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement fault was found. The original DAG steps 2 and 3 describe
real geometric work but do not provide a declaration that states compatibility or
local sheet reindexing. The new geometric lemma makes that work an independent item;
the algebraic summation and generic sheaf gluing are proved here.

The local compiled library lacked `FiniteEtaleTraceLocalSums.olean`, despite containing
its source. An unchanged sandbox copy was compiled to supply that dependency locally;
it is not delivered, and no shared library file was written. Another recently added
sieve criterion was also absent from the cached interface, so the covering proof uses
the established Mathlib `ofArrows_mem_smallEtaleTopology_iff` directly.

LeanSearch returned HTTP Internal Server Error. LeanFinder, Loogle and Mathlib/source
searches supplied generic gluing and finite sum machinery, not the geometric statement.
The locally missing literature sources were checked on the primary Stacks pages:
https://stacks.math.columbia.edu/tag/03SH and
https://stacks.math.columbia.edu/tag/04HN. The detailed reindexing argument is the
original item's descent argument, expanded in the new node and docstring.

## New nodes

`def-weil-pbc-finite-etale-trace-splitting-data` records constructor-supplied splitting
data and the explicit section maps and sum, all in `FiniteEtaleTraceSplitting.lean`.
No data depend on an unproved existential theorem.

`lem-weil-pbc-finite-etale-trace-split-cover` records the proved geometric covering
step. This is the original step 1 applied directly to the base-changed morphism.

`lem-weil-pbc-finite-etale-trace-split-reindexing` records the remaining proper geometric
part of steps 2 and 3: a local bijection matching composite sheet morphisms. It does
not restate descent, compatibility of sheaf sums, or existence of a global section.

`lem-weil-pbc-finite-etale-trace-split-sum-compatibility` records the proved finite-sum
calculation and separatedness argument from local reindexing. All new nodes stay in
the item's chapter and unit. No change record is needed: no existing public signature,
definition, or public import changes.

## Second reading by F1

1. **Unchanged interface: pass.** Read the diff against the repository's descent
   module. The existing theorem signature, including the proof term in its section
   morphism, and its docstring are byte-for-byte unchanged. Only its proof and private
   imports change. The other four modules are new; there are no adapted existing
   definitions, target changes, or change records.
2. **Proof and construction: pass as a decomposition.** Compiled all five modules in
   import order with lcompile.py. Independently appended `#print axioms` in scratch
   copies for the structure, presieve, sectionMap, sum, and all four theorems.
   Definitions use only propext, Classical.choice and Quot.sound. The four theorems
   additionally use sorryAx, from the remaining reindexing hole and the existing
   local-splitting dependency. There is exactly one textual sorry, in the named
   reindexing theorem, and no forbidden declaration. The cover proof applies local
   splitting to the finite etale projection, transports the cofan by symmetry and
   pasting, and uses inverse isomorphisms explicitly. Its choices only construct a
   proposition asserting a cover. Descent chooses a local section from an existence
   theorem that uniquely characterizes it by all splittings; it never chooses
   arbitrary splitting data into a definition. The sum proof genuinely uses
   additivity, functoriality, reindexing and separatedness.
3. **Split-off statements: pass.** Read all new nodes and their Lean signatures,
   and Stacks 03SH (section-trace-method, local sum characterization after 03SE) and
   04HN (lemma-finite-etale-etale-local). The source supplies local splitting and
   trace-by-sums; reindexing expands the geometric independence required there.
   The reindexing hypothesis supplies two finite clopen coproducts and inverse
   projections, not a trace or a global section. After pullback, their pairwise
   intersections are open subschemes of either sheet. Each sheet projects
   isomorphically to Z, so the intersection's projection is an open immersion,
   and corresponding sections agree as scheme morphisms by its inverse, not
   merely on points. Each point defines a permutation; the finite intersection
   of its matching open loci fixes that permutation on a neighbourhood.
   These neighbourhoods cover Z. Checked one sheet, zero sheets, an empty base
   with arbitrary sheet counts, unequal counts over a nonempty base (impossible),
   and disconnected bases with different permutations. No nonemptiness,
   connectedness, finite degree, or surjectivity is silently assumed. The
   geometric lemma is strictly smaller than descent and includes a complete
   docstring proof and node. New searches used LeanFinder on two coproduct
   decompositions, Loogle on Fintype.sum_equiv, and grep on coproduct pullbacks,
   disjointness, sheets and reindexing, plus rg in project and upstream sources.
   They found sigmaMk/sigmaι_eq_iff and generic sum machinery, not the local
   morphism correspondence. Read the finite-etale upstream adjunction and project
   Yoneda trivialization statements: neither directly states this correspondence.
   Closing reindexing requires real scheme geometry, not a short tactic repair.
4. **Route and pruning: pass after repair.** Descent uses the full split-domain
   presieve, a shorter route than choosing a cover and then proving the formula
   by another base change. Compatibility is reduced to the geometric part, with
   the sheaf and finite-sum steps proved. The unit sk-thm-p1 realized route retains
   locally constant reduction and trace retraction; no unit step is bypassed.
   Replaced the new splitting module's unused public six-functor and AB imports
   by smaller Mathlib site and group imports and recompiled the entire set.
   Existing public imports are unchanged. Completed No longer needed with all
   nine old direct proof dependencies removed from descent, distinguishing their
   continued use below from the covering-base-change leaf no longer needed here.
5. **DAG agrees: pass after repair.** Checked descent's three proof steps against
   hvalue/hx, sheaf amalgamation, and uniqueness; cover's steps against base change,
   transported cofan and jointly surjective arrows; compatibility's steps against
   reindexing and the finite-sum calculation. Their proof_deps are the union of
   their cited steps. Reindexing's node and Lean have exactly the common-square,
   finite-splitting and local-bijection clauses, including the empty-cover case.
   All new nodes have source, searches, creation, blueprint, chapter, unit, and
   matching Lean records. Rewrote the new compatibility node's prose statement
   to introduce all its objects and hypotheses explicitly instead of referring
   to another theorem for its setting; its mathematical content and Lean
   signature are unchanged. No new hole or theorem was added in this reading.

Second-reading changes: smaller imports in FiniteEtaleTraceSplitting, complete
old-dependency pruning list, and self-contained compatibility node prose.
