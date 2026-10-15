## What changed

Proved `CategoryTheory.exists_site_finite_basis_hypercover` in
`Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence`, with its original statement and
public imports unchanged. The proof constructs the zero-truncation, recursively extends
finite split truncations, and explicitly assembles the compatible tower into a simplicial
object. Each operator is evaluated at a finite stage; independence of stage proves the
functor laws and exact restriction to every stage.

Added the fully proved module `Sheaf.CategoryTheory.SiteFiniteBasisHypercoverStep`.
Its public definitions `faceInclusion`, `faceDiagram`, and `IsFiniteBasisTruncation`, and
its theorem `exists_finite_basis_truncation_extension`, are in namespace
`CategoryTheory.FormalSplitAttachment`. The theorem proves the induction step from the
existing `exists_split_truncated_extension`. The supporting proofs establish finite
boundary limits, finality of the proper-face inclusion using simplex image factorization,
and stability of a finite covering family under a finite enlargement. It handles empty
covers and empty matching families. No existing definition or theorem signature changed.

The original node now records the implemented tower argument, and the new step has a
complete node. Both files compile without warnings through `lcompile.py --all` (about
2.2 and 3.7 seconds). The delivery dry run performs the final checks.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.exists_site_finite_basis_hypercover`
(`lem-weil-pbc-site-finite-basis-hypercover-existence`).

Also proved the new theorem
`CategoryTheory.FormalSplitAttachment.exists_finite_basis_truncation_extension`
(`lem-weil-pbc-site-finite-basis-hypercover-step`) and every private helper in both files.
There are no remaining `sorry`s in either delivered Lean file and no new holes.
This is one original hole closed and zero holes added, not a decomposition into new holes.
The existing dependency `CategoryTheory.FormalSplitAttachment.exists_split_truncated_extension`
(`lem-weil-pbc-site-hypercover-finite-extension`) remains unproved in the baseline library;
this delivery uses its stated interface as required by stage 3 and does not change it.
Consequently the target's transitive axiom closure still includes that existing `sorryAx`.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.SiteCoveringAxioms`: neither its
`CategoryTheory.Precoverage.IsSiteForCoverings` definition nor its sheaf-cohomology imports
are needed for this construction. The proof works directly with `Precoverage` and the
stated covering hypotheses. The conceptual site-definition node remains a statement
reference; this does not withdraw or change it.

Removed the main module's direct imports of
`Sheaf.Paper.SiteHypercoverFiniteExtension` and
`Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`.
They are retained transitively where the proved induction-step module uses them, so this
is import cleanup, not pruning of those dependencies. The new module imports only the
finite-limit, formal-family, simplex-image, and finite-index APIs its proofs need.
The direct proof dependencies on `lem-weil-pbc-site-hypercover-finite-extension` and
`lem-weil-pbc-finite-limits-from-terminal-pullbacks` move into the proved step node;
both remain needed transitively. No other planned node or module is made unnecessary.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The plan needed explicit glue between
the attachment theorem's boundary cone on all lower-degree operators and the target's
proper-face matching diagram. This is proved by finality of the proper-face inclusion:
the image of each simplex operator gives an initial factorization through a proper face.
Finite matching indices are proved using preservation of finite limits by the index-set
functor, rather than constructing a separate full subcategory of finite families.
These implement the same split-skeleton route of the original node and unit.

The new module uses `import all Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic`
only in proofs: its existing pullback-cone theorem exposes a private proof constant to
kernel checking. An ordinary import produced an unknown-private-constant error; the
`import all` form compiles and does not alter the public interface of the item.
The Leansearch service was unavailable during the recorded search; Leanfinder, Loogle,
grep, and direct local library searches found no all-degree finite-basis construction.

## New nodes

`lem-weil-pbc-site-finite-basis-hypercover-step`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-site-finite-basis-hypercover-step.json`,
records the fully proved one-degree extension theorem and its invariant definitions in
`lean/Sheaf/CategoryTheory/SiteFiniteBasisHypercoverStep.lean`. It is strictly the induction
step, not a restatement of the all-degree existence theorem. Its only existing unproved
proof dependency is the categorical split attachment theorem mentioned above. No change
record is needed: no existing signature, definition, public import, or target meaning
changes, and no other module is adapted.

## Second reading by F1

1. **Signatures and accidental changes — pass.** Compared the delivered target module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; the only existing-module edits are proof and proof-only imports. The added module contains the declared new invariant definitions and induction theorem.
2. **Proof and axioms — pass.** Compiled both delivered modules with `lcompile.py --all`; no errors, warnings, forbidden declarations, or `sorry`s occur in the delivered files. The target's remaining `sorryAx` comes only from the pre-existing imported split-attachment theorem, which is explicitly recorded in the report and node dependencies.
3. **Split statements — pass.** The added theorem is a one-degree extension of a finite split truncation and is strictly smaller than the all-degree target. Its definitions and theorem have source/docstrings, matching DAG data, and no duplicate declaration was found in the repository or search results. Edge cases for empty covers and empty matching families are handled in the proof.
4. **Route and pruning — pass.** The proof follows the split-skeleton route through the new extension theorem, preserves the unit route, and removes only imports no longer used directly. The `## No longer needed` section lists the removed imports and explains the transitive dependencies retained by the step module.
5. **DAG agreement — pass.** Updated `proof`, `proof_deps`, and `proof_origin` match the implementation in both node files; the new node has the required Lean record, source, blueprint, creation metadata, and complete proof steps.

I changed only this report section after the second reading; no Lean statements or proof code required repair.
