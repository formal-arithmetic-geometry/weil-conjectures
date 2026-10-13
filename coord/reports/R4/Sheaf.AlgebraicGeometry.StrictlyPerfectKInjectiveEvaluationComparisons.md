## What changed

Closed the body of AlgebraicGeometry.exists_strictlyPerfect_kInjective_evaluation_comparisons
without changing its signature, hypotheses, visibility, or prescribed chain map f.
The proof combines separately stated left- and right-inverse identities for the restricted
canonical evaluation. It proves those inverse maps agree and forms an actual Iso.
The existing open-restriction theorem and derivedInternalHom_obj_iso supply the target
comparison b using the supplied K-injective F. The existing degreewise ordinary evaluation
theorem supplies an inverse of f. Set a = e ≪≫ b ≪≫ (Q.mapIso (asIso f)).symm.
Associativity and the inverse equation prove the required square.

Added two modules, StrictlyPerfectEvaluationLocalRetraction and
StrictlyPerfectEvaluationLocalSection, one one-sided inverse identity in each. These are
independent parts of the invertibility argument, rather than another theorem asserting the
comparison square. Neither mentions F, eN, f or hf, and neither asserts both inverse identities.
Their sources and complete ordinary-model proof plans are in the docstrings and nodes.
They do not choose data in definitions; there are no new definitions.

The docstring and revised DAG record the categorical construction actually written in Lean.
The unit route is unchanged. The unit record has no realized binding for this item.

## Proved and sorry left

Closed one original hole:
- AlgebraicGeometry.exists_strictlyPerfect_kInjective_evaluation_comparisons
  (lem-pc-strictly-perfect-kinjective-evaluation-comparisons).

Added two holes, each exactly a named public theorem with proof `:= by sorry`:
- AlgebraicGeometry.exists_strictlyPerfect_evaluation_local_retraction
  (lem-pc-strictly-perfect-evaluation-local-retraction).
- AlgebraicGeometry.exists_strictlyPerfect_evaluation_local_section
  (lem-pc-strictly-perfect-evaluation-local-section).

No sorry remains in the assigned module. This is a decomposition: one upper hole is closed
and two lower holes are added, so the net hole reduction is -1. The derived representative
comparison and inverse identities still need proof; this delivery does not claim that the
underlying derived evaluation argument is axiom-free. The categorical assembly is complete.

## No longer needed

Removed the assigned module's direct proof imports:
- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
  (lem-pc-bounded-above-flat-kflat-site).
- Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso
  (lem-pc-bounded-exact-term-hom-quasi-iso).
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
  (lem-sc-finite-free-internal-hom-exact).

These are not claimed as globally pruned: their proof imports are relocated to both
new inverse-identity modules, where their ordinary-model plans use them. Those modules
also import the open-restriction, ordinary-evaluation and K-injective-resolution
lemmas used by their plans. All these imports are private to the proofs. No whole module is
claimed unnecessary in the targets' closure. The two public imports are retained because
the original signature uses their declarations. DerivedInternalHomRestrictOpen remains
as a proof import and both new proof imports are used.

The assigned node no longer directly uses def-pc-perfect-complex,
def-pc-scheme-derived-tensor-structure, def-pc-tensor-complex-sheaves,
def-pur-hom-complex, def-pur-kinjective-complex or the three removed lemma nodes.
Their notions or subsidiary calculations remain needed in the signatures and lower plans.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original proof plan demands compatible model choices,
but the statement only quantifies over comparison isomorphisms with one equation. Once
restricted canonical evaluation and ordinary evaluation are invertible, its source
comparison can be defined from the target comparison, rather than independently.
This avoids an additional compatibility theorem about that independently chosen source.

The local literature checkout contains lists but lacks stacks-project/cohomology.tex.
Read Stacks 08DQ, 08DM and 08DL online at their stable tag pages. LeanSearch returned an
Internal Server Error and is recorded as unavailable; LeanFinder returned unitors and Tor
results, and Mathlib grep returned no local derived evaluation inverse theorem. Searches
of both library roots and the imported blueprint found no usable non-circular theorem.
Existing StrictlyPerfectRHomEvaluationLocal and PerfectRHomEvaluationIsomorphisms import
this item indirectly and cannot be used here.

The blueprint ancestor helper returned None because created.item records a module name;
the existing node's explicit blueprint.from identifies lem-sc-finite-duality, which the
new nodes inherit. No binding field or ancestor record of an existing node was changed.

Edge cases of both new statements: P=0, rank-zero terms, N=0 and empty U give identities
on zero objects. N is arbitrary and may be represented by an unbounded complex; bounded
support is required only of P. A left inverse alone is weaker than invertibility, as is
a right inverse alone; the written categorical proof needs both and proves their equality.

## New nodes

lem-pc-strictly-perfect-evaluation-local-retraction, in
lean/Sheaf/AlgebraicGeometry/StrictlyPerfectEvaluationLocalRetraction.lean, isolates the
source inverse identity for the canonical restricted evaluation. The proof plan follows
Stacks 08DQ's bounded tensor model and evaluation followed by its degreewise inverse.

lem-pc-strictly-perfect-evaluation-local-section, in
lean/Sheaf/AlgebraicGeometry/StrictlyPerfectEvaluationLocalSection.lean, isolates the
target inverse identity, checked after Hom product projections. Its argument follows the
same Stacks models but proves the other inverse equation. No change record is needed
because all existing signatures and definitions are unchanged.

## Second reading by R4

1. **Interface: pass.** Compared the assigned module against the repository with
   `diff -u`, and extracted every delivered theorem signature up to `:= by`.
   The original theorem signature is byte-for-byte unchanged, including the given
   f, hf, eK, eN and F.IsKInjective. Its node changes only proof, proof_deps and
   proof_origin. Both other modules and nodes are new. No definitions, existing
   statements, public imports or visibility were changed; no change record is needed.

2. **Kernel checks: pass as a decomposition.** Compiled all three modules through
   lcompile.py, in import order, without errors or warnings (7.7, 5.8 and 37.1 s).
   Explicit `#print axioms` in scratch copies of each module returned only propext,
   Classical.choice, Quot.sound and sorryAx. The latter is expected: the two named
   inverse-identity theorems remain open. The assigned module contains no sorry;
   each lower module contains exactly its reported theorem's `:= by sorry`.
   Checked all delivered files for axiom, unsafe, opaque, implemented_by and extern;
   none occurs. There are no new definitions or arbitrary data witnesses chosen
   into definitions. The comparison isomorphisms are witnesses inside a theorem
   proof; their construction does not define exported data.

3. **New statements: pass.** Read Stacks
   [08DQ](https://stacks.math.columbia.edu/tag/08DQ),
   [08DM](https://stacks.math.columbia.edu/tag/08DM), and
   [08DL](https://stacks.math.columbia.edu/tag/08DL).
   The ordinary tensor-Hom calculation gives precisely the two inverse equations.
   For a finite free term, evaluation and the dual-basis inverse cancel in both
   orders. For a retract i:E→B, p:B→E, i;p=1, the inverse for E is obtained from
   the inverse for B by precomposition with p and restriction of the dual along i;
   naturality reduces both composites to i;p=1. Finite support makes the relevant
   sums and products finite, even for unbounded N. Localization and conjugation
   preserve each identity. Checked P=0, N=0, rank zero and the empty open; all
   reduce to identities on zero objects. Also checked a shifted one-term finite
   free P: only its matching dual degree contributes, with arbitrary terms of N.
   Both lower theorems have source-tagged complete proof docstrings and matching
   nodes. Neither reasserts the original comparison square: each asserts only
   one inverse identity and has no F, eN, f or hf. The actual proof needs both.
   Independent msearch searches used the different terms “dualizable”,
   “canonical map from tensor with its dual to internal Hom”, HasRightDual,
   tensorRightHomEquiv and isIso.*curry, with leanfinder, loogle and grep.
   Mathlib provides rigid-category equivalences requiring an exact pairing;
   no theorem supplies the local pairing or identifies it with this fixed
   derived-Hom family. Searches of both source roots found no non-circular
   local derived evaluation inverse. StrictlyPerfectRHomEvaluationLocal and
   PerfectRHomEvaluationIsomorphisms depend on this item through its parents.
   Neither lower hole has a short proof from the presently usable declarations.

4. **Route and pruning: pass after repair.** Read the proof from its conclusion
   downward: a=e;b;(Qf)⁻¹ gives the square, ordinary evaluation gives IsIso f,
   the existing restriction and K-injective Hom computations give b, and the
   two lower identities give e. Checked the cancellation argument r=s and both
   Iso fields. Both new proof imports are used. The three old calculation
   imports have moved into the lower modules' proof plans, not disappeared from
   the overall argument. The No longer needed section lists every old node
   removed from the assigned node's proof_deps; no global pruning is claimed.
   Read dag/units/sk-thm-picard-duality.json: realized.statement and its sole
   realized step are empty, so no realized unit binding is bypassed or changed.
   The delivery closes one hole and adds two: net -1, a decomposition rather
   than an axiom-free proof of derived evaluation.

5. **DAG: pass after repair.** Matched each Lean signature verbatim with its
   node's lean.statement, checked all dependency IDs exist, and verified
   proof_deps is exactly the union of the steps' uses. Read the cited dependency
   statements, including bounded exact-term Hom, finite-free Hom exactness,
   bounded-above flat K-flatness, ordinary evaluation and open restriction.
   Retract exactness and finite support are the intervening ordinary arguments.
   New nodes have the required source, searches, origin, creation, blueprint,
   chapter, unit and Lean records. The assigned node now also retains the
   canonical-family dependency used explicitly when defining g in the proof.

**Changes made by the second reader:** added proof-only imports to both new
modules for the six lemma modules their plans cite; corrected the assigned
module's proof docstring to describe the categorical reduction actually written;
removed one extra blank line; retained the canonical tensor-Hom family in the
assigned node's proof_deps and the corresponding step; updated pruning and
construction documentation in this report. No theorem body or signature changed.
