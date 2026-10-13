## What changed

Proved AlgebraicGeometry.exists_cohomologyFraction_mayerVietoris_exact without changing its signature or docstring. Constructed the restriction and boundary maps by direct-sum extension and quotient descent, proved the four generator formulas, represented fractions and pairs at a common denominator, and proved degree-zero injectivity and all three exact positions by lifting kernels to a later twist. The successive killing argument for product targets preserves the first zero restriction by naturality.

Added Sheaf.AlgebraicGeometry.CohomologyFractionEventuallyZero with the completely proved theorem AlgebraicGeometry.Scheme.Modules.cohomologyFraction_eventually_zero. Its transition-coherence facts are imported directly with `import all Sheaf.AlgebraicGeometry.FractionZeroTensorPower`; its public result there is too specialized (top open, degree-zero numerator, subsingleton presentation) for this item. The new proof maps the explicit quotient to Mathlib's additive direct limit and applies of.zero_exact. It does not assume invertibility. Neither the library module nor its dependencies were adapted. The repair removes all ten duplicate private theorems flagged by import_prune_check.py and the duplicate private tensorSectionTransition definition; the proof now uses the original declarations.

The existential quotient maps are determined uniquely by their values on every direct-sum generator. Choice in the proof selects only these uniquely determined maps, never arbitrary mathematical data. All definitions and local helper proofs are complete.

Both modules compile with lcompile.py --all, with no warnings. Each compiles well within the 60-second limit. Lean statements cover zero sections, empty opens, zero numerator classes and arbitrary degrees uniformly. The source read was Stacks Tag 09MR (canonical fractions and upper Mayer--Vietoris row), and Tag 01EB (module naturality). Searches found generic Mathlib exactness and direct-limit zero_exact infrastructure; no existing public theorem for this explicit quotient. LeanSearch was unavailable and is recorded without a mathematical verdict.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.exists_cohomologyFraction_mayerVietoris_exact (lem-sc-cohomology-fraction-mayer-vietoris-exact). Added and proved AlgebraicGeometry.Scheme.Modules.cohomologyFraction_eventually_zero (lem-sc-cohomology-fraction-eventually-zero). No sorry remains in either delivered module; no hole was added or split off. This is a proof, not a decomposition: one original hole closed, zero new holes.

## No longer needed

Removed the redundant direct proof import Sheaf.Topology.OpenModuleCohomology; its declarations remain needed and are already publicly available through CohomologyFractionPresentation. Its node def-sc-open-module-cohomology remains a dependency, so this does not prune that module from the target closure. No mathematical node or module from the original plan is pruned. Retained the original two public imports unchanged, and added only a private proof import for the new proved eventual-zero module. The new module privately imports Mathlib.Algebra.Colimit.Module, all of whose relevant infrastructure is used.

FractionZeroTensorPower is now a private proof import using `import all` to access its existing private transition definition and identities. Its specialized public theorem is not used; neither is ModuleCohomologyTopComparison, although that module is reached through this import. Removed the ten locally duplicated tensor-coherence/transition theorems and the duplicate transition definition. No global pruning claim is made for these modules. The unit sk-thm-curveestimate has no realized steps affected by this proof; its realized statement thm-sc-proper-cohomology is preserved.

## Where the brief, the DAG or earlier work was wrong

The returned delivery incorrectly duplicated ten already proved private helper statements. Repaired by importing and using the existing declarations, rather than reproving them. No incorrect mathematical statement or interface found. The original plan is valid, but its stronger presentation-is-the-direct-limit assertion is unnecessary: a homomorphism from the fraction quotient to the direct limit suffices to deduce the eventually-zero criterion. Common denominators follow directly from the defining relations. The full tensor coherence proof was already present in proved private helpers of FractionZeroTensorPower; `import all` allows direct reuse without any visibility change.

## New nodes

lem-sc-cohomology-fraction-eventually-zero records the proved single-numerator vanishing criterion, with arbitrary open and numerator degree, and points to Sheaf.AlgebraicGeometry.CohomologyFractionEventuallyZero. Its proof explicitly records the imported tensor transition identities, quotient descent to the additive direct limit, and Mathlib of.zero_exact. The node has the source, the actual search records, its complete Lean signature and edge cases. Updated the item's node proof, proof_deps and proof_origin to follow the Lean proof. No change record is needed because no existing signature, definition or visibility changed. The repair adds the node of FractionZeroTensorPower to the helper node proof_deps to record this actual proof import.

Repair validation: both revised modules compile with lcompile.py --all (2.8 s and 8.7 s). The second reading below describes the returned version and is retained as history; its assertions about locally copied helpers and absence of the FractionZeroTensorPower import are superseded by this repair. A new second reading is still required.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered main module with the repository using diff. After restoring
   one extra space before its proof, the existing theorem signature is byte for byte
   identical. Its docstring and the original public imports are unchanged. There are
   no changed existing definitions, declarations, hypotheses, conclusions or
   visibility, and no forced adaptations or change records. Verdict: pass.
2. Read both modules completely, including the tensor coherence, transition casts,
   quotient descent, common denominators, and all four exactness/injectivity arguments.
   Compiled both with lcompile.py --all without errors or warnings. Scratch copies
   with #print axioms show exactly propext, Classical.choice and Quot.sound for both
   public theorems, with no sorryAx. Text search found no sorry or forbidden constructs
   in the delivered Lean. All private definitions are explicit constructions; choices
   in the main proof select quotient maps uniquely determined on generators.
   Verdict: pass.
3. No statement is split off with sorry. The new, proved eventual-zero criterion is
   strictly part of the argument and is true without invertibility. Checked zero
   numerators, zero sections, n=0, arbitrary cohomology degrees and empty opens:
   the quotient/direct-limit proof has no nonzero or nonempty assumptions. Independent
   Loogle search for AddCommGroup.DirectLimit.of found of_f and of.zero_exact, already
   used here. Lean Finder search for element vanishing in a filtered colimit found
   general categorical colimit lemmas requiring additional comparison infrastructure.
   Local searches by fraction vanishing and transition names found no equivalent
   public criterion; FractionZeroTensorPower only handles a subsingleton top-open
   presentation and degree-zero numerators. Verdict: pass; no shorter public route found.
4. The proof follows the target downward and uses the shortest applicable direct-limit
   zero criterion. The main module's two public imports serve its statement; its sole
   private import supplies eventual vanishing. The helper publicly imports its fraction
   definitions and privately imports Mathlib's direct-limit machinery. Both old proof
   dependencies remain used, so No longer needed correctly claims no node or module
   pruning. The removed direct OpenModuleCohomology import is redundant through the
   public fraction-presentation import. Read sk-thm-curveestimate.realized: its sole
   realized statement thm-sc-proper-cohomology and empty steps remain untouched.
   Verdict: pass.
5. Compared both node records with the Lean signatures and argument. Their proof_deps
   equal the union of proof-step uses, proof_origin describes the actual route, and
   the new node has its source, search records, created/blueprint fields and Lean
   record. The existing node's original dependencies are retained, with the proved
   eventual-zero node added. Verdict: pass.

Second reading changed only whitespace at the two proof boundaries and the new
helper's proof docstring to describe the actual quotient-to-direct-limit map and
Mathlib zero_exact argument. No mathematical statement or proof body changed.


## Second reading by B3

1. Compared the main module against the read-only repository with diff, and checked
   the existing theorem header byte for byte through the proof boundary. The header,
   existing docstring, public imports, hypotheses, conclusion and visibility are
   unchanged. The existing node changes only proof, proof_deps and proof_origin.
   There are no adaptations or change records. Verdict: pass.
2. Read both delivered modules and the imported private transition construction and
   identities in FractionZeroTensorPower. Compiled both with lcompile.py --all:
   3.2 s and 8.9 s, no errors or warnings. Separate scratch-copy #print axioms checks
   for both public theorems show only propext, Classical.choice and Quot.sound,
   without sorryAx. Text search finds no sorry or forbidden construct in either
   module. fractionOf is explicitly the direct-sum inclusion followed by quotient;
   the chosen maps are lifts uniquely determined on generators. Verdict: pass.
3. No sorry statement is split off. The new proved eventual-zero theorem is a proper
   part of the argument and requires neither invertibility nor injective transitions.
   Its quotient-to-direct-limit map proves precisely the one direction needed.
   Checked zero numerators, n=0, s=0, empty opens, arbitrary p, and zero groups:
   no step assumes a nonzero section, positive exponent, or nonempty open. An
   independent Loogle search for AddCommGroup.DirectLimit.of confirmed of_f and
   of.zero_exact with the needed types. Local searches using eventually_zero,
   zero_exact and fraction/zero terms found no existing public criterion for this
   presentation. FractionZeroTensorPower supplies the reused private identities;
   its public result concerns top-open degree-zero numerators under subsingleton
   fractions and cannot replace this general criterion. Verdict: pass.
4. Read the proof downward through quotient descent, common-denominator induction,
   all three kernel lifts, vanishing composites, and degree-zero injectivity.
   Successive killing preserves the first zero restriction by naturality. The
   main public imports are used in its statement; its private helper import is used
   in proofs. The helper's public import supplies its signature, and both private
   imports supply actual proof declarations. No unnecessary additional comparison
   is constructed. Both old proof dependencies remain used; the removed direct
   OpenModuleCohomology import is redundant through CohomologyFractionPresentation.
   No node or module is pruned. Checked sk-thm-curveestimate.realized: its statement
   thm-sc-proper-cohomology and empty steps are untouched. Verdict: pass.
5. Checked both nodes against the Lean signatures and complete arguments. Each
   proof_deps is exactly the union of the proof steps' uses. The new node records
   the actual FractionZeroTensorPower reuse, quotient descent and zero_exact route,
   source, searches, creation, blueprint, unit, chapter and verbatim Lean signature.
   The existing node accurately records the natural quotient maps and kernel lifts.
   Verdict: pass.

Second reading changed only this report by adding the fresh independent review.
No Lean proof, statement, import or node needed repair in the revised delivery.
