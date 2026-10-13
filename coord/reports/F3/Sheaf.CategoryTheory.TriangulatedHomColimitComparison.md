## What changed

Proved `CategoryTheory.triangulated_hom_colimit_comparison` with its original
statement, universes and public imports unchanged. Added only private constructions
and proved helpers in the item module, plus proof-only Mathlib imports.

The proof constructs the lifted abelian-group Hom colimits, establishes their
exactness by a representative chase, identifies their comparisons with the original
`ColimitType` comparisons, transports the first two comparisons across the shift
equivalence, and applies Mathlib's additive-group five lemma. The sign introduced
by rotating a triangle twice is handled explicitly.

Updated the existing node's proof and proof origin to describe the Lean proof;
its original proof dependencies remain needed. The unit record has no realized
statement or steps, and the original five-term route is retained.

The resumed worker checked the complete proof already present in the sandbox,
removed two redundant proof imports, and recompiled through `lcompile.py` with
no errors or warnings. No existing theorem signature or docstring was changed. The conservative
interface check requires a record for the added local elaboration commands:
`coord/changes/triangulated-hom-colimit-proof-context.md`. This record lists all
downstream modules; none needs adaptation.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.triangulated_hom_colimit_comparison`
(node `lem-pur-triangulated-hom-colimit-comparison`).

No `sorry` remains, and no hole is added. All private helpers are fully proved.
This is a proof, not a decomposition: holes closed 1, holes added 0.

## No longer needed

No existing library node or module is pruned, and no original public import is
removed. The prior attempt's unsubmitted modules
`Sheaf.CategoryTheory.TriangulatedHomColimitInjective` and
`Sheaf.CategoryTheory.TriangulatedHomColimitSurjective`, and their two new node
files, have been removed from this sandbox; the completed proof needs neither.
No import of `Mathlib.Algebra.Category.Grp.AB` is needed: exactness is proved by
representatives using Mathlib's preservation of filtered colimits by forgetful
functors. No import of another `Sheaf` or `WeilConjectures` module is needed. Removed
`Mathlib.CategoryTheory.Whiskering` and
`Mathlib.CategoryTheory.Adjunction.Basic` from the earlier sandbox attempt;
the required declarations are already available through the remaining imports.
These removals prune no original library module from the targets’ closure.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt deferred both injectivity and surjectivity, with empty proof
plans and prose hypotheses that disagreed with its Lean. Those additions are
removed. Its reported missing `deliver3.py` is no longer a blocker: the tool is
available on this machine.

The original DAG's mathematical route works without changing its statement.
Separate index and Hom universes require lifting the Hom groups and explicitly
shrinking the universe parameters for preservation of filtered colimits. The
identification with `ColimitType` is proved by comparing representatives, rather
than assumed definitionally.

The local Stacks literature checkout is absent on this machine. The sources were
read from [Tag 05SC](https://stacks.math.columbia.edu/tag/05SC),
[Tag 00DB](https://stacks.math.columbia.edu/tag/00DB) and
[Tag 05QB](https://stacks.math.columbia.edu/tag/05QB).


## Second reading by F3

1. **Visible interface: pass.** Compared the complete sandbox module and existing
   node with the repository versions. The sole existing declaration's signature,
   universes, docstring, visibility, and three public imports are byte-for-byte
   unchanged. All added constructions and lemmas are private. The local instance
   attribute affects only this module. The elaboration-context change record
   describes the conservative checker's flags; no definition used by a target
   changes and no downstream adaptation is needed.
2. **Proof and axioms: pass.** Compiled the delivered file with `lcompile.py`
   without errors or warnings (2.3 seconds). Compiled a scratch copy with
   `#print axioms CategoryTheory.triangulated_hom_colimit_comparison`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Scanned the
   whole file: no sorry, axiom, unsafe, opaque, implemented_by, or extern. The
   group colimit is Mathlib's actual colimit of the explicit ULift Hom diagram;
   no arbitrary object is extracted from an unproved existence theorem.
3. **Split statements: pass, none.** No new public statement, node, or hole is
   delivered. Read every private helper. In `homColimMap_exact`, common-stage
   equality of a representative and zero produces a stage where naturality
   puts the representative in the pointwise kernel; the pointwise exactness
   hypothesis then supplies its preimage. The reverse inclusion uses the
   pointwise zero composite. `homColim_rep_eq_iff` compares both common-stage
   criteria, and `homComparison_bijective_iff` also uses joint surjectivity on
   both sides. Shift transport uses adjunction naturality in both injectivity
   and surjectivity. Double rotation gives the negative shifted first arrow;
   choosing the negative lift removes precisely that sign. Zero Hom groups,
   contractible triangles, and the one-object indexing case need no excluded
   case or extra hypothesis; empty indexing is already impossible with `j₀`.
4. **Route and pruning: pass.** Read the displayed five-term proof in
   [Stacks 05SC](https://stacks.math.columbia.edu/tag/05SC), its dual order, the
   representative argument in [00DB](https://stacks.math.columbia.edu/tag/00DB),
   and the outer-map conditions in [05QB](https://stacks.math.columbia.edu/tag/05QB).
   The proof uses Mathlib's additive five lemma directly. Its four squares are
   respectively shifted `m.comm₁`, `m.comm₃`, `m.comm₂`, and `m.comm₁`; the six
   exactness premises and outer surjective/bijective/bijective/injective premises
   occur in the correct order. Searched the project and upstream sources and
   Mathlib (recorded grep and Loogle searches with different queries).
   Mathlib `Triangle.isIso₃_of_isIso₁₂` concerns one triangle morphism whose
   first two components are isomorphisms; our hypotheses only identify their
   Hom colimits. Orthogonal bijectivity lemmas require localization/orthogonal
   hypotheses absent here. The categorical AB exactness theorem offers a
   heavier short-complex route, not a missing direct comparison theorem.
   Removing each of the five proof-only imports in separate scratch copies
   fails compilation, so all are needed. Public imports remain necessary for
   the original statement. No old proof dependency or original module is
   pruned. `sk-def-sf-operations.json` has empty realized statement and steps;
   the original five-term route is retained.
5. **DAG agreement: pass.** JSON comparison shows that only `proof` and
   `proof_origin` changed in the existing node; the recorded Lean statement
   matches the unchanged signature. The four new prose steps describe the
   actual exact-pair construction, representative chase and quotient
   comparison, commuting squares and shift transport, and additive five lemma.
   The original dependency set is retained: pretriangulated structure, exact
   filtered abelian-group colimits (proved here by representatives), and the
   five lemma. There are no new-node fields or split-off declarations to audit.

**Changes by the second reader:** added this independent review and recorded
additional searches and validation. No repair to the Lean proof or node was
needed. Holes closed: `CategoryTheory.triangulated_hom_colimit_comparison` (1);
holes added: none (0). This is a proof, not a decomposition.
