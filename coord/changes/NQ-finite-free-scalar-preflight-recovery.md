# NQ finite-free scalar preflight recovery (2026-10-21)

Maintenance for lem-weil-finite-free-completed-scalar-comparison@100b8fa83.

The unchanged retained stage-1 split was repeatedly refused by upstream DAG records:

* def-weil-integral-scalar-extension cited lem-weil-integral-constructible-linear
  for linearity of the ambient scalar-extension functor. That theorem concerns the
  constructible subcategory and requires its triangulation, which reaches coefficient
  presentation transport and this comparison, closing a six-node cycle. The existing
  lem-weil-integral-scalar-extension-well-defined, clause 3 and proof step 8, already
  proves ambient functor linearity using lem-weil-linear-abelian-derived-category.
  Replace the stale citation and statement dependency by that ambient theorem.
  The defined functor and all mathematical clauses are unchanged.
* Commit 8fbeee85ea changed the exceptional-adjunction proof_deps to its two new
  construction/coherence obligations and changed the Lean body to record assembly,
  but retained the previous 13-step natural-language proof. Align the proof field
  with the existing assembly. The obligations retain the substantive arguments;
  proof_deps now equals the union of uses. The statement and Lean are unchanged.

Original records are preserved alongside them as
*.json.maint-NQ-finite-free-20261021.bak. No Lean, launcher, review or landing tool
was changed. In particular the comparison item's genuine scalar-extension dependency
is retained. No item mathematics was undertaken by this maintenance repair.

Next NQ worker: retain the existing five statement-only children, the 2067-character
assembly, citations and search evidence in the sandbox. Run the normal deliver.py
dry run against updated sheaf-dag, then deliver under the existing worker brief.
The maintenance REPORT.md records validation and the server commit.
