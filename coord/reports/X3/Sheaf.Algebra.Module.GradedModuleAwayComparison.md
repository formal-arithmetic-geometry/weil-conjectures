## What changed

Replaced `LocalizedModule.gradedModuleAwayComparison`'s sorry with a complete Lean
construction from denominator clearing and kernel detection. Added proof-only imports
of `Mathlib.Algebra.Module.LocalizedModule.Away`,
`Sheaf.Algebra.Module.GradedModuleAwayClearing`, and
`Sheaf.Algebra.Module.GradedModuleAwayKernel`. The private, fully proved
`LocalizedModule.comparisonOfClearing` builds the module and ring localization
instances, constructs the equivalences with Mathlib, and proves both extension laws,
the fraction identity, and semilinearity by cancelling a unit denominator.
The original theorem's signature and docstring are unchanged.

## Proved and sorry left

Closed the original hole in `LocalizedModule.gradedModuleAwayComparison`
(node `lem-weil-pbc-graded-module-away-comparison`) by decomposition, not by an
unconditional proof. The item's module has no sorry. Two strictly smaller holes added:

- `LocalizedModule.gradedModuleAwayClearing`, node
  `lem-weil-pbc-graded-module-away-clearing`: source and target fractions can be
  related after multiplication by a power of the comparison denominator.
- `LocalizedModule.gradedModuleAwayKernel`, node
  `lem-weil-pbc-graded-module-away-kernel`: elements mapped to zero are annihilated
  by a power of the comparison denominator.

The complete private lemma `LocalizedModule.comparisonOfClearing` has no sorry.
The two new statements assert only numerator-level existence and zero criteria;
neither asserts a comparison map, equivalence, or compatibility of an equivalence.
The top theorem combines them through the actual universal properties in Lean.
This is one upper hole closed and two lower holes added (net minus one).
Edge cases checked mathematically: nilpotent or zero denominators give zero
localizations; zero ring and zero module require no nontriviality; degree one makes
the extra numerator power zero. The kernel computation never cancels in S.

## No longer needed

No imports or modules pruned. The four old proof dependencies
`def-nagata-homogeneous-localization-degree-zero`,
`def-weil-pbc-module-localization-away`, `def-weil-ring-localization-away`, and
`def-sc-degree-zero-module-fractions` are no longer direct proof dependencies of
the comparison node: its direct proof dependencies are now clearing and kernel.
All four remain statement dependencies and are used by the intermediate nodes,
so their modules remain necessary. The proof route keeps all three
original steps: universal-property construction, surjectivity, and kernel detection.
No unit statement or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node's dependencies are definitions only; no declared theorem supplies
the denominator-clearing or kernel computations. The source leaves them implicit
in its fraction formulas. They have now been exposed as separate statements, and
the rest is proved in Lean. No statement was found false or changed.
The literature/stacks-project/constructions.tex file is absent on this machine;
the cited source was read at https://stacks.math.columbia.edu/tag/01M4.
LeanSearch returned Internal Server Error; LeanFinder, Loogle and source searches
provided the relevant universal-property API but no exact graded-module result.

## New nodes

`lem-weil-pbc-graded-module-away-clearing` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-graded-module-away-clearing.json`,
with module `Sheaf.Algebra.Module.GradedModuleAwayClearing`. It realizes step 2
of the comparison node and records the degree-adjusted numerator construction.

`lem-weil-pbc-graded-module-away-kernel` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-graded-module-away-kernel.json`,
with module `Sheaf.Algebra.Module.GradedModuleAwayKernel`. It realizes step 3
and records how an ordinary localization zero criterion produces a power of U
that kills the original numerator. No interface changes or change records.


## Second reading by X3

1. Compared the comparison module with the repository by diff and checked its
   existing theorem signature byte for byte: unchanged, as is its docstring.
   The only existing-module additions are a private proved helper, proof-only
   imports, a scoped linter option, and the replacement proof. No definition or
   target statement changed; no change record is required. Verdict: pass.
2. Compiled all three modules in import order using lcompile.py: no errors or
   warnings. Only gradedModuleAwayClearing and gradedModuleAwayKernel contain
   sorry, each as the entire proof of its documented named theorem. No forbidden
   trust features or hollow definitions occur. Checked the helper and all three
   public declarations with #print axioms in scratch copies: the helper uses
   only propext, Classical.choice, Quot.sound; the public declarations additionally
   use sorryAx through the two recorded holes. The equivalences come from actual
   Mathlib localization constructions; their extension laws determine them
   uniquely, so the final choice is not an arbitrary undetermined object.
   Verdict: pass, conditional on the listed split statements.
3. Read the split statements and fraction arguments against Stacks Tag 01M4
   (https://stacks.math.columbia.edu/tag/01M4). Clearing uses the explicit numerator
   g^(n*(d-1))*y over f^(n*delta); kernel uses g^N*a^m*x = 0 and multiplication
   by f^m, not cancellation in S. Checked d = 1, n = 0, zero modules/rings and
   nilpotent denominators; the latter give zero localizations. The ring-map
   fraction formula follows from preservation of S and inverses. These are
   strict parts of the argument, not renamed comparison equivalences. Fresh
   LeanFinder, Loogle, Mathlib grep and upstream/library rg searches found only
   the generic criterion and fraction-representation/product-localization APIs.
   No split can be closed in a few minutes using those APIs: the graded fraction
   computations remain. Verdict: pass.
4. Read from the top: the proof applies Mathlib's module and ring localization
   criteria, then their actual equivalences; the fraction law and semilinearity
   are proved, with cancellation only of a unit in the target. Each import is
   needed by either a statement or proof. The old definition dependencies remain
   necessary for statements and lower nodes; their move out of direct proof_deps
   is now explicitly listed above. Checked sk-thm-reduction.json realized: its
   statement and all unit steps are retained, with this comparison still below
   the symmetric-product route. Verdict: pass; decomposition, net minus one hole.
5. Checked all three DAG records against declarations and the actual proof route:
   proof_deps is the union of proof-step uses, sources and blueprint links are
   present, and new nodes have creation, status, search and Lean records. Corrected
   the two new lean.statement fields to verbatim multiline signatures, and made
   their informal proof steps agree with the expanded docstrings. Verdict: pass.

Second reading changed no Lean proof or existing signature. It clarified the new
lemma docstrings (degree identification, nilpotent case, ring restriction formula,
and injective inclusions), synchronized their DAG proofs and verbatim signatures,
added independent search records, and corrected the dependency accounting above.
