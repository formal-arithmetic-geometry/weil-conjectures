## What changed

Proved `CategoryTheory.roosPrefixAcyclic` by dimension shifting for Mittag--Leffler
(ML) towers. The proof uses the existing injective-tower embedding, injectivity of
split towers, Mittag--Leffler limit exactness, and horseshoe delta-functor.
It proves successor-surjective towers ML by induction on composite transitions.
For an ML tower B embedded in an injective split tower I, form the actual cokernel
Q. Exactness of limits gives the degree-one base case; ML of I implies ML of Q,
and the long exact sequence gives the induction step. Apply this to the prefix tower.
Added plain proof-only imports of `Mathlib.Algebra.Category.Grp.EpiMono`,
`Sheaf.CategoryTheory.InjectiveTowerEmbedding`,
`Sheaf.CategoryTheory.InjectiveSplitTower`,
`Sheaf.CategoryTheory.MittagLefflerLimitExact`, and
`Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`.
Updated the existing node's proof and proof dependencies to match.
The sandbox copy of `RoosFinitePrefixes.lean` is byte-for-byte unchanged and is
present solely to compile the dependency missing from the local baseline cache.

## Proved and sorry left

Closed one original hole: `CategoryTheory.roosPrefixAcyclic` (node
`lem-pc-roos-prefix-acyclic`). No sorry remains in the item's module.
Added zero holes and split off zero statements. The existing, undelivered
`CategoryTheory.ShortComplex.mittagLeffler_quotient_and_limit_exact` (node
`lem-weil-pbc-mittag-leffler-limit-exact`) remains sorry; the result rests on that
open theorem and is not yet axiom-free. The other direct helper theorems are
already proved. This is a proof from existing declarations, not a new decomposition.
Net local holes closed: one; authoritative import-closure figures are the ledger's.

## No longer needed

No original imports were removed and no whole library modules are claimed pruned.
Removed old direct proof dependencies: `def-sp-left-exact-additive`,
`lem-pc-tower-abelian`, `lem-pc-tower-enough-injectives`,
`lem-pc-tower-limit-left-exact`, and
`lem-weil-pbc-tower-limit-exact-surjective-kernels`.
The first four are supplied by Mathlib definitions/instances, the given hypotheses,
and Mathlib derived-functor lemmas. Surjective-kernel exactness is encapsulated by
the existing ML limit-exactness theorem. The finite-prefix construction, embedding,
split-tower injectivity, and horseshoe dependencies remain direct.
The discarded duplicate core module/node are not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker added `surjectiveTowerLimitAcyclicCore`, duplicating an existing
general theorem, while its report named the existing theorem. Removed this duplicate.
Trying the existing theorem exposed an import cycle:
RoosPrefixAcyclic → SurjectiveTowerLimitAcyclic → DerivedLimitRoosAbelianGroups →
RoosAcyclicResolution → RoosPrefixAcyclic. A cached single-file compile does not
catch this; deliver3.py correctly refused it. Replaced that route with a real
proof using only lower-level declarations. Checked the sources online because
this checkout has no literature/stacks-project/*.tex files:
[Stacks 07KW](https://stacks.math.columbia.edu/tag/07KW) and
[Stacks 02N1](https://stacks.math.columbia.edu/tag/02N1).

## Second reading by E3

1. Compared both existing sandbox modules with the repository using diff.
   `RoosFinitePrefixes.lean` is identical. In `RoosPrefixAcyclic.lean`, only plain
   proof imports and the theorem body change; the signature and docstring are
   byte-for-byte unchanged. No definition, statement, visibility, or target changed.
2. The repaired item compiles locally with no warning or error. A scratch copy
   with `#print axioms CategoryTheory.roosPrefixAcyclic` reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`, consistent with the existing
   ML exactness hole. The unchanged prefix module and the delivered item have no
   sorry or forbidden declarations. Q is the actual cokernel, not data extracted
   from a holed existence statement. The embedding theorem used to obtain I is
   already proved. No hollow definitions or new data choices were introduced.
3. Removed the split-off general core because it duplicates an existing statement.
   Searched the library with rg and Mathlib through msearch grep using
   `surjectiveTowerLimitAcyclic`, `MittagLeffler`, and `IsZero.*rightDerived`.
   This found the reusable injective-object vanishing lemma and the library's
   ML quotient/limit theorem. There are no new statements or nodes. Edge cases:
   s = 0, n = 0 has an empty prefix, covered by extension by zero; zero degree is
   excluded by the unchanged hypothesis; induction starts at degree one.
4. The general surjective-tower theorem is unavailable here because of its import
   cycle; instead the real proof reuses the existing lower statements. The ML
   theorem combines quotient stability and limit exactness, so no new lemma is
   needed. Public imports are needed by the signature, additions only by the
   proof. No longer needed lists every removed old direct dependency. Inspected
   `dag/units/sk-thm-picard-duality.json`: realized is
   {statement: [], steps: [[]]}; no realized unit step is bypassed or changed.
5. The node proof now records the composite-transition induction, actual cokernel
   sequence, degree-one exactness argument, and higher-degree induction. Its
   proof_deps is precisely the union of the five existing nodes used by those
   steps. Its proof_origin records dimension shifting from 07KW using 02N1.
   No new node or change record is required.

Second reading removed the duplicate core module/node, replaced the circular
shortcut with the compiled dimension-shifting proof, repaired the DAG route,
and corrected the report's hole and dependency accounting. All existing
signatures and definitions are unchanged.
