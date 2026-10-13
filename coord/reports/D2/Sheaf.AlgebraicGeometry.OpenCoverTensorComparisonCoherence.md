## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.OpenCoverTensorComparisonCoherence by a
complete calc proof from a single recovery-normalization triangle (used twice) and an
ordinary pullback refinement diamond. Added proof-only imports of
Sheaf.AlgebraicGeometry.OpenCoverTensorRecoveryNormalization and
Sheaf.AlgebraicGeometry.OrdinaryPullbackRefinementCoherence. A proved private helper, assemble_refinement_comparisons, contains the generic
functor-level naturality/cancellation calculation. All existing signatures and
public imports are unchanged. The target node follows the resulting argument.

Named comparison arguments, each fixed by an equation to its canonical construction,
keep kernel conversion from unfolding large adjunction and pullback data repeatedly.
The comparison definitions are locally irreducible in the assembly proof; this has
no effect on importers. The original statement contains unused let binders D and Ll;
the unused-variable linter is disabled only for this unchanged declaration.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.Modules.openCover_tensor_comparison_coherence,
node lem-pc-open-cover-tensor-comparison-coherence. No sorry remains in the item.

Added two public whole-proof holes:
- AlgebraicGeometry.Scheme.Modules.openCover_tensor_recovery_normalization,
  node lem-pc-open-cover-tensor-recovery-normalization.
- AlgebraicGeometry.Scheme.Modules.ordinary_pullback_refinement_coherence,
  node lem-pc-ordinary-pullback-refinement-coherence.

This is a decomposition: one upper hole closed, two strictly smaller holes added.
The first concerns one factorization and has no refinement diamond; the second has
only ordinary pullback and no tensor construction or chosen tensor adjunction.
The combination of those steps, including naturality, comparison cancellation and
projection equations, is proved. There is no admitted glue or hollow definition.

## No longer needed

None. No original import is removed. All original comparison constructions remain
needed, directly in the signature and transitively in the normalization step.
The ordinary step requires no tensor modules, so its new module imports only Mathlib.
No original DAG dependency is pruned: normalization still needs the tensor composition,
chart comparison, recovery construction and pinned adjunction. Those old dependencies
now occur beneath the new normalization node rather than directly in the target proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The original two-step prose plan contained no
separately stated normalization triangle or ordinary diamond; those are now explicit
items. The raw explicit-comparison interfaces caused expensive kernel conversion;
named isomorphism parameters with defining equations resolve this in the new lemmas.
The published local build initially lacked ModuleRecoveryComparisonIso and
OpenCoverRefinementComparisons; unchanged sandbox copies were compiled to supply those
imports. They contain no edits and are not part of this delivery's changed files.

## New nodes

lem-pc-open-cover-tensor-recovery-normalization: single-factorization normalization
of tensor recovery followed by inverse chart comparison, with canonical c, t, ck and
rho fixed by equations. Its source and complete mate/cancellation argument are in its
docstring and node. The zero module, empty charts and identity maps are included.

lem-pc-ordinary-pullback-refinement-coherence: ordinary pullback coherence for two
three-step paths through a refinement square. It assumes only the five displayed
scheme-map equalities and no open-cover or tensor hypothesis. Its associativity and
congruence argument is in its docstring and node. Identity refinements, empty schemes
and zero modules cause no exception. The conservative attribute-command check requires the record
coord/changes/openCover_tensor_comparison_coherence-local-transparency.md.
It documents local elaboration scope only; no consumer adaptation is needed.

## Second reading by D2

1. Compared all five sandbox modules with repository sources. The two support
   copies are byte-identical. The item's existing theorem signature, visibility,
   docstring and public import are unchanged; only its proof, a private proved
   helper and local elaboration commands were added. No target or construction
   changed. The existing change record accurately limits the attributes to this file.
2. Compiled the complete sandbox in import order without errors or warnings.
   The item contains no sorry; exactly the two reported public named theorems
   contain sorry, with no data definitions introduced. Explicit #print axioms
   for all three public theorems returned only propext, Classical.choice,
   Quot.sound and the expected sorryAx. No forbidden declaration mechanism occurs.
   The helper's cancellation uses mapped isomorphisms, so requires no extra
   geometric hypothesis. Choice is used only for the existing pinned adjunction,
   which determines its comparison uniquely, not for arbitrary geometric data.
3. Read both new statements, their docstrings and matching nodes. Their supplied
   comparisons are fixed by equations, so cannot hide an arbitrary coherence
   assumption. Tensor normalization concerns one factorization and contains no
   refinement; ordinary coherence contains neither tensor pullback nor adjunction.
   Both are strictly parts of the original argument. Identity maps reduce to
   associativity and inverse cancellation; zero modules and empty charts impose
   no exceptional condition. Checked mate directions against the definitions of
   tensorPullbackCompositionIso, openCoverTensorPullbackComparison and
   moduleRecoveryComparisonIso. Repeated leanfinder, loogle and grep searches
   with different queries; inspected Mathlib pullback associativity, the upstream
   and library search results, OpenCoverTensorPullbackComposition and
   ChartTensorPullbackComparisonCoherence. None states either new lemma exactly.
   A pre-existing scratch attempt to prove the ordinary lemma timed out at 60 s;
   it is not delivered and introduces no additional holes.
4. Read the proof from its target through both reductions. The assembly calc
   proves the actual remaining naturality/cancellation step. No shorter immediate
   library application was found. The normalization module did unnecessarily
   import the whole refinement-comparison bundle; replaced that public import
   by the three modules whose constructions occur in its statement. No existing
   module is pruned. All four old proof dependencies remain used: three beneath
   normalization, and refinement comparisons directly. The unit's realized
   record is unchanged, and no unit statement or proof step is bypassed.
5. Checked proof steps, dependency unions, origins, source references, new-node
   creation and blueprint fields, and Lean declaration names against the code.
   Updated the new nodes' lean.statement fields to the verbatim multiline source
   signatures. The target's proof_deps correctly lists the two new reductions
   and the refinement comparison definition.

Second-reading changes: narrowed the normalization imports, wrapped two long
statement lines, restored exact spacing at the item's proof boundary, removed
extra blank lines, and made new-node signature records verbatim. No mathematical
statement or construction changed. This remains a decomposition: one original
hole closed and two smaller holes added (net minus one hole closed), not a
sorry-free proof of the target's import closure.
