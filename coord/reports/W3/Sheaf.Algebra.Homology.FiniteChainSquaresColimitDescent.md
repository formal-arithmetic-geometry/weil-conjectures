## What changed

Proved `CochainComplex.eventually_commuting_finite_chain_squares`. Added two strictly
smaller supporting modules: preorder equality descent for finitely presented module maps,
and coherence of transported graded scalar-extension maps. The item now imports those
modules and `Mathlib.Data.Int.Interval`.

## Proved and sorry left

Closed the one original hole:
`CochainComplex.eventually_commuting_finite_chain_squares`
(node `lem-pc-finite-chain-squares-colimit-descent`). Added zero holes and split off zero
unproved statements. Both new public theorems are proved:
`ModuleCat.eventually_equal_maps_of_directed_preorder_colimit` and
`CochainComplex.graded_scalarExtension_colimit_coherence`. All private helpers are proved.

The existing imported theorem `ModuleCat.finitePresentation_descent_directedColimit`
(node `lem-pc-fp-module-map-descent-affine`) remains `sorry` upstream, unchanged. Thus this
is a complete proof of the item from the stated descent dependency, not a claim that its
entire import closure is sorry-free.

## No longer needed

The proof no longer imports `Sheaf.Algebra.FinitePresentationColimit` directly; its partial-
order equality theorem is used indirectly by the new preorder helper. The old direct
proof edge to `lem-pc-fp-module-map-descent-affine` is replaced by the edge to
`lem-pc-preorder-module-map-equality-descent`, which still uses that descent node.
No module is made unreachable by this delivery: finite-presentation descent remains
needed through antisymmetrization. The direct proof edge to
`lem-pc-filtered-colimit-commrings-elementwise` is removed; it is not used here directly
and remains a dependency of the existing finite-presentation theorem. No pruning of that
node's transitive work is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG left scalar-extension coherence and finite-stage aggregation in one elementary
step. The proof makes these precise using proved helpers. Its non-elementary preorder
equality step required explicit reindexing rather than direct application of the imported
descent theorem. The imported finite-presentation theorem only handles partial orders, so
the preorder case requires antisymmetrization and a final functor argument.

## New nodes

`lem-pc-preorder-module-map-equality-descent` is stated in
`Sheaf.Algebra.Homology.PreorderModuleMapEqualityDescent` and records the antisymmetrization
reduction to `ModuleCat.finitePresentation_descent_directedColimit`.

`lem-pc-graded-scalar-extension-coherence` is stated in
`Sheaf.Algebra.Homology.GradedScalarExtensionCoherence` and records the associativity and
naturality calculation for the canonical comparisons.

Both new statements were checked at their edge cases: the index supplied to equality
descent ensures nonemptiness; antisymmetrization handles distinct mutually comparable
indices; zero modules and already-equal maps are included. Coherence assumes neither
finite presentation nor commuting chain squares, works at i=j and in all degrees,
and uses equality induction to handle the exact eqToIso comparisons. The empty interval
case is the empty Finset branch of the proved common-stage induction, which chooses i.
The unit record has empty realized statement and step lists; no unit statement or
realized proof step is bypassed.

No change record is needed: all existing signatures, definitions and public imports
are unchanged. Both supporting imports in the item are proof-only. Mathlib searches
were recorded in the new nodes: LeanSearch failed with Internal Server Error; LeanFinder,
Loogle and local source searches identified the associativity lemmas and no direct
preorder equality theorem. Sources read: Stacks Tags 05N7 (3) and 09RE affine case (1)
on their official pages because the local Stacks source files are absent.

## Second reading by W3

1. Compared the delivered item against the repository with `diff` and checked the
   original theorem signature byte for byte: unchanged, including the exact `e`
   comparisons and all hypotheses. The existing docstring and public imports are
   unchanged. The two supporting modules are new; no existing definition or public
   interface is altered and no change record is required. Verdict: pass.
2. Compiled all three delivered modules in import order using `lcompile.py`: no
   errors or warnings. Scanned all delivered Lean for holes and forbidden declarations:
   none. A scratch copy with `#print axioms` checked all three public theorems. The
   coherence theorem uses only `propext`, `Classical.choice`, and `Quot.sound`; the
   preorder equality and item theorems additionally use `sorryAx` from the unchanged
   upstream finite-presentation descent theorem. The proof constructs `w` explicitly
   by conjugation, with no hollow definition or arbitrary witness hidden in data.
   Verdict: pass relative to the stated open upstream dependency.
3. No unproved statement is split off. Read both new proved helper statements and
   their complete docstring arguments. Equality descent is a genuine one-pair
   specialization over arbitrary directed preorders, not a restatement of finite
   chain-square descent. Coherence has no directedness, presentation, or commuting
   square assumptions. Checked the empty interval, zero modules, equal maps, i=j,
   and distinct mutually comparable indices: the finite induction, representative
   inequalities, and equality induction cover them. Repeated LeanFinder, Loogle,
   and local Mathlib/source searches with tensor/transition-algebra and equality
   queries. Results concern fixed-ring module colimits, ring-map descent, or the
   associativity lemmas already used, not a direct substitute. Verdict: pass.
4. Read the proof from the target downward: pairwise descent, finite directed
   aggregation, naturality for the chain squares, then associativity coherence for
   every degree. The existing partial-order descent theorem is reused rather than
   restated as a new hole. All added imports are proof-only; existing public imports
   supply the statement. The old two direct dependency edges are both accounted for
   under No longer needed, and remain upstream where needed. No module pruning is
   claimed. Read `dag/units/sk-thm-picard-semicon.json`: its realized statement list
   and sole realized step list are empty; the route is not bypassed. Verdict: pass.
5. Checked each node's Lean signature verbatim, proof steps against the actual code,
   and proof_deps against the union of step uses. The existing node changes only
   proof, proof_deps, and proof_origin. Both new nodes have source, creation, blueprint,
   chapter/unit, Lean records, and three recorded search kinds. Their proofs correctly
   distinguish the upstream descent use from elementary naturality/coherence work.
   Verdict: pass.

Second reading changed only this report: clarified the removed direct edge to
`lem-pc-fp-module-map-descent-affine` and recorded these checks. The Lean proofs and
node files needed no repair. Closed one original hole; added zero holes.
