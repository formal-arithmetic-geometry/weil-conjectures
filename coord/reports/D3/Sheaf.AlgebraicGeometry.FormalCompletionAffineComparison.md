## What changed

Proved the body of `AlgebraicGeometry.formalCompletion_affine_comparison` without changing
its signature, visibility, public imports, or existing docstring. Added proof imports for
coherent closure, the locally Noetherian coherence criterion, affine finite-type sections,
upstream Čech acyclicity, underlying-module sheafification, and the relevant Mathlib APIs.

The ring is the actual section ring Gamma(X,U), the ideal is I(U), and the module complex
is explicitly S evaluated on U. Private proved helpers establish exactness of the coherent
inclusion and short exactness of affine sections. Finiteness uses the existing private theorem
`AlgebraicGeometry.Scheme.Modules.finite_sections_of_finiteType` directly, via
`import all Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`. The restriction
helper and its supporting module are unnecessary.
A private concrete sections functor names the evaluation composite and proves preservation
of zero maps. No data is selected from an unproved mere existence theorem.

Steps 2–4 are isolated as the public theorem
`AlgebraicGeometry.formalCompletion_affine_natural_comparison` in the new module
`Sheaf.AlgebraicGeometry.FormalCompletionAffineNaturalComparison`. This compares every
coherent object and morphism with its actual affine sections. It assumes no short exact
sequence and makes no exactness or finiteness assertion. The main proof applies its
naturality to the two arrows of the independently constructed and proved exact complex.

## Proved and sorry left

Closed: `AlgebraicGeometry.formalCompletion_affine_comparison`
(node `lem-weil-pbc-formal-completion-affine-comparison`). There are no remaining sorries
in the original module. All private helpers are proved.

Added: `AlgebraicGeometry.formalCompletion_affine_natural_comparison`
(node `lem-weil-pbc-formal-completion-affine-natural-comparison`), whose entire proof is
`:= by sorry`. Its docstring and node give the complete proof in words, including the
zero ideal, unit ideal, empty affine open, and zero-module cases.

This closes one upper hole and adds one strictly partial comparison hole: a decomposition,
not a net reduction of holes. The affine section exactness and finiteness part is proved
from existing library declarations. Both delivered modules compile without errors or
warnings through lcompile.py. The main theorem still depends on the new comparison hole
and on any holes already present in its existing proof dependencies.

## No longer needed

The duplicate private helper `AlgebraicGeometry.finiteType_over_ringSheaf` is no longer
needed. The direct finite-sections theorem also removes the need for the proof import
`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback` and its node
`lem-weil-pbc-support-pullback-finite-type`. Removed the redundant proof import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`. No original import was removed:
all four public imports support the unchanged statement.
No previously reached module is claimed to become unreachable. The original module had
no proof-dependency imports despite its DAG plan.

The main theorem no longer directly needs
`lem-weil-pbc-ringed-space-module-exactness-local-lifting` or
`lem-weil-pbc-quasi-coherent-module-cokernel-image`: upstream Čech acyclicity and the
left-exact sections statements replace the planned local-lifting/cokernel-image route.
Their modules are not imported.

The affine spectrum, tilde-sections adjunction, coherent formal affine equivalence,
open restriction, ideal-product section formulas, coherent completion definition and
adic completion definition are retained in the new comparison node's plan; they are
not globally pruned. The main node now cites the new comparison rather than listing
these comparison-internal steps as its own direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer X-4cd89 / head 4cd890a97: the former private restriction helper
duplicated an existing theorem word for word. The first repair removed that helper. The second reading found a shorter
route: apply the existing finite-sections theorem directly. Its visibility remains
private; Lean `import all` provides access within this proof only. No other module is adapted.
The main DAG node records the affine finite-type node; it no longer needs the
support-pullback node.
The previous second reading predates this repair and has been removed for a fresh
independent reading. The delivery tool rebuilds the commit on current sheaf-dag.

The standing brief says the module already imports its stated proof dependencies;
this module instead had only statement imports. The worker-specific brief describes
that actual state correctly.

The planned affine section exactness argument can use already proved upstream
`cechAcyclicOnAffines_of_isQuasicoherent` and
`surjective_app_of_cechAcyclicOnAffines`, together with
`TopCat.Sheaf.injective_app_f` and `TopCat.Sheaf.exists_app_f_eq`.
The original statement and the unit route are preserved. No statement was disputed,
no signature was corrected, and no other existing module was adapted.

## New nodes

`lem-weil-pbc-formal-completion-affine-natural-comparison` states only the natural
realization of coherent completion on affine sections (original plan steps 2–4).
The original plan's step 1 is proved separately in the original module. The source is
Stacks Tags 087W and 0881, read online because literature/stacks-project/coherent.tex
is absent on this machine. Blueprint searches for affine completion, 087W and adic
completion found no duplicate (the adic derived-reduction hit is a different result).
LeanFinder and a focused Mathlib source grep found no natural comparison theorem;
LeanSearch returned Internal Server Error and is recorded as unavailable.
No change record is required: all existing signatures and public imports are unchanged.

## Second reading by D3

1. PASS: diffed both delivered modules against the repository. The only existing
   public declaration is `AlgebraicGeometry.formalCompletion_affine_comparison`;
   its signature and docstring are byte-for-byte unchanged. All original public
   imports remain. No existing definition or target statement changes.
2. PASS: both modules compile through lcompile.py without errors or warnings.
   Scanned all delivered Lean for forbidden declarations/options and holes. The
   sole literal sorry is the reported public natural-comparison theorem. Scratch
   `#print axioms` checks for the concrete sections functor, both private exactness
   helpers, the main theorem and the split theorem show only propext,
   Classical.choice, Quot.sound and (except for the concrete functor) sorryAx.
   Existing proof dependencies remain open; the private exactness proofs therefore
   are checked reductions, not independent sorry-free results. No definition
   chooses an arbitrary object from an unproved existence statement: the sections
   functor and module complex are concrete, and the existential comparison is
   eliminated only inside a theorem proof.
3. PASS: the split statement is natural comparison for objects and maps, without
   short exactness or finite-generation conclusions. It is a strict part of the
   argument, rather than a renamed restatement. Read its full docstring and node
   against [Stacks 087W](https://stacks.math.columbia.edu/tag/087W) and
   [Stacks 0881](https://stacks.math.columbia.edu/tag/0881). The zero ideal gives
   a constant tower, the unit ideal a zero tower, the empty affine open a zero
   section ring, and zero modules zero limits; reflection via full faithful
   inclusions and scalar restriction still applies. The equation on underlying
   systems fixes the action of rho; no additional zero-preservation hypothesis
   is needed. Independent LeanFinder and Mathlib grep searches used inverse-limit
   and global-section wording, and rg searched both Sheaf and WeilConjectures.
   The affine-open adic-sections theorem only handles individual tower levels;
   the affine equivalence theorem handles arbitrary formal systems and lacks this
   completion comparison. Neither duplicates the new statement. Closing that
   comparison requires substantial quotient and transport constructions, beyond
   a short repair. This delivery closes one literal upper hole and adds one lower
   hole: decomposition, net zero, with upstream dependencies still open.
4. PASS after pruning: replaced restriction-finiteness plus the affine criterion
   by the existing direct finite-sections helper. Removed its now-unused supporting
   module and the redundant Mathlib sheaf-limits import. The unit sk-thm-p1's
   realized statement and step nodes are untouched, and the changes occur below
   unit level. No globally unreachable module is claimed. The old direct proof
   dependencies absent from the new main node are exactly:
   - `lem-weil-pbc-module-restriction-open-immersion-colimits`
   - `lem-weil-pbc-ringed-space-module-exactness-local-lifting`
   - `lem-weil-pbc-quasi-coherent-module-cokernel-image`
   - `def-weil-affine-spectrum`
   - `lem-weil-pbc-affine-tilde-gamma-adjunction`
   - `lem-weil-pbc-coherent-formal-modules-affine`
   - `def-weil-pbc-coherent-formal-module`
   - `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
   - `def-weil-pbc-adic-completion`
   Comparison-internal nodes remain in the new comparison's proof plan; the
   local-lifting and cokernel-image route is replaced by upstream affine Cech
   acyclicity and left exactness.
5. PASS after metadata repair: checked proof steps and their dependency union
   against the Lean proof, existing nodes and unit. Removed the support-pullback
   dependency after shortening the proof. The new node has its source, complete
   proof plan, searches, creation/blueprint records and Lean record. Corrected
   its Lean statement field to the exact multiline signature. No change record
   is needed because no existing signature or definition changed.

Second reading changed: the finite-sections proof and proof import, removed two
proof imports, updated the main node's proof/dependencies and this report, and
made the new node's signature record verbatim. No additional hole was closed.
