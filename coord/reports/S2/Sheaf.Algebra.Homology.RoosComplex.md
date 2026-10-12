## What changed

`CategoryTheory.roosComplex_quasiIso` now has a complete Lean proof from two strictly
smaller new statements. It constructs the canonical map, checks the signed differential,
proves a K-injective homotopy retraction using Mathlib, and constructs an explicit inverse
of the comparison after localization. The original public signature and public imports are unchanged; proof imports changed.

Added `TowerSplitComplexReplacement`, `RoosSplitComparison`, and
`RoosComparisonHomotopyRetract`. The split replacement is proved from the existing
`tower_split_envelope` and `exists_kernel_to_shifted_mappingCone_of_degreewise_epi`:
apply the additive envelope to the complex, take the cokernel, identify the original
complex with its kernel, and form the shifted cone. Proven private helpers transport
split transitions through tower isomorphisms and form sections of binary biproducts.
The other two new statements remain named proof obligations with complete docstrings.

All four delivered modules compile together through lcompile.py. No data definition
has a sorry. Existential intermediate data is used only locally in proofs, never to
define arbitrary objects in the library.

## Proved and sorry left

Closed the original hole `CategoryTheory.roosComplex_quasiIso` (node
`lem-weil-derived-limit-roos-complex`). Also proved the new declaration
`CategoryTheory.tower_split_complex_replacement` (node
`lem-weil-tower-split-complex-replacement`). The target is a decomposition, not an
independent sorry-free proof: two holes are added, for a net increase of one hole.

Every hole added is exactly a named public theorem with proof `:= by sorry`:
`CategoryTheory.roos_split_comparison` (node `lem-weil-roos-split-comparison`) and
`CategoryTheory.roos_comparison_homotopy_retract` (node
`lem-weil-roos-comparison-homotopy-retract`). There are no holes left in the item's module
or the split replacement module. Existing imported split-envelope and kernel/cone holes
remain in their own unchanged modules.

## No longer needed

Removed direct proof imports `Sheaf.CategoryTheory.TowerSplitEnvelope` and
`Sheaf.Algebra.Homology.KernelShiftedMappingCone` from RoosComplex; both are still needed
transitively by the proved replacement, and the latter also by the split comparison.
Thus no dependency module is globally pruned. The target's immediate proof dependencies
now name the three chain-level intermediate modules and the Mathlib K-injective and
derived-category facts. The unit route is unchanged.

Old immediate proof dependencies no longer used directly by the item:
`lem-weil-tower-category-levelwise-abelian`, `def-weil-tower-transition-endomorphism`,
`def-weil-inverse-system`, `lem-weil-tower-split-envelope`, and
`lem-weil-degreewise-epi-kernel-cocone-qis`. The mathematical constructions they
provide remain in the intermediate statements and their dependencies; this is
no claim that their modules leave the targets import closure.

Second reading removed unnecessary public imports of
`Mathlib.Algebra.Homology.DerivedCategory.Basic` and
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective` from all three new modules,
using the smaller public `QuasiIso` or `Homotopy` import required by their signatures.
It also removed `Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism` from
`TowerSplitComplexReplacement`, whose statement and proof do not use it.

## Where the brief, the DAG or earlier work was wrong

The planned mathematics works. The stated lemmas did not include the chain-level glue
of the split presentation or the homotopy-natural retract diagram. These are now two
separate, strictly smaller statements: the split comparison assumes split terms and
no K-injectivity; retract transfer assumes a given homotopy retraction and makes no
quasi-isomorphism claim. Neither restates the target.

The local Stacks text is absent from this read-only clone. Read the primary source at
https://stacks.math.columbia.edu/tag/070M, especially its split short exact sequence and
triangle. The arbitrary-tower extension is the existing agent-written argument recorded
in the original node. All searches were made through msearch and recorded in the nodes;
LeanSearch returned Internal Server Error, while LeanFinder, Loogle and source grep
found generic complex, mapping-cone and K-injective API but no exact Roos theorem.

Edge cases checked mathematically: zero tower and zero comparison; constant towers
with identity transitions (recursive section of 1-s); arbitrary unbounded complexes
in the replacement (no induction in cochain degree); and the identity retraction
in the transfer statement. The sign in the cone homotopy is (-P(h)y,P(h)x), so the
mixed transition terms cancel. The explicit localized inverse uses the correct
composition order cU, inverse etaJ, lR and both comparison squares.

## New nodes

`lem-weil-tower-split-complex-replacement`: proved generic replacement of any tower
complex by split terms, using the existing envelope and kernel/cone declarations.

`lem-weil-roos-split-comparison`: the split-term product/kernel/signed-cone construction
and comparison, exactly the split short exact sequence argument of Tag 070M.

`lem-weil-roos-comparison-homotopy-retract`: naturality and homotopy invariance of both
presentations, returning commuting squares and retraction homotopies only.

## Earlier second reading (a previous round; superseded)

The target declaration is unchanged and its proof compiles. The three new nodes are
strictly smaller than the target: replacement produces split transitions; split comparison
proves only the split case; retract transfer proves only naturality and homotopy equations.
Their statements match their Lean declarations, have the source and blueprint tags, and
are imported by the target. The proved replacement has no sorry; the two remaining holes
are named public theorems with corresponding DAG nodes. The unit route through the split
envelope and kernel/cone comparison is retained.

New node ids: `lem-weil-roos-comparison-homotopy-retract`, `lem-weil-roos-split-comparison`, and `lem-weil-tower-split-complex-replacement`.


## Second reading by S2

1. Compared every delivered module with the repository: only RoosComplex exists
   there, and its theorem signature is byte-for-byte identical, including exact
   products, enough injectives, K-injectivity and every differential equation.
   The other three modules are new. No existing definitions or signatures change.
   All additional imports of the original module are private proof imports.
   Verdict: pass.
2. Compiled the four files together, then scratch copies with `#print axioms`
   for all four public theorems and all three private helpers. The helpers use
   only propext, Classical.choice and Quot.sound. The public theorems use these
   plus sorryAx, precisely because of the two new obligations and the existing
   envelope/kernel-cone obligations. Exactly two local sorries remain, both
   complete named theorem proofs. No hollow definition, axiom, unsafe, opaque,
   implemented_by, extern or skipped kernel checking occurs. The existential
   replacement is eliminated inside a proof, never used to define library data.
   Verdict: pass as a decomposition, not an axiom-free proof of the target.
3. Read both new obligations against their full hypotheses. For the split case,
   the recursion a_0=0, a_(n+1)=(a_n-pr_n) followed by the chosen section gives
   a_n-a_(n+1)f_n=pr_n; hence 1-s is split epi without exact products. The signed
   cone square vanishes because d commutes with s. For retract transfer, naturality
   factors the product homotopy through the kernel in each degree, and the cone
   homotopy (-h y,h x) cancels mixed terms. Zero complexes, constant identity
   towers, degrees below zero and the identity retraction introduce no exception.
   These statements respectively require split transitions or a supplied homotopy
   retraction; neither contains the arbitrary K-injective target conclusion.
   Read their sourced docstrings and matching nodes, and checked Stacks Tag 070M
   (https://stacks.math.columbia.edu/tag/070M): its split exact sequence supports
   the split case, while the arbitrary-tower extension is explicitly agent-written.
   Independent LeanFinder search for kernel/cone split inverse-sequence comparison,
   Loogle search for Homotopy.map, msearch grep for homotopy functoriality and direct
   source searches found generic APIs, no exact replacement for either obligation.
   Closing either requires substantial chain-level constructions, beyond a few
   minutes. Verdict: true, needed and strictly smaller; retained.
4. Read the proof top down: explicit canonical map and chain-map check, proved
   split replacement, Mathlib K-injective Hom bijection for the retraction, split
   comparison, homotopy transfer, then the explicit inverse in D(A). Verified both
   inverse identities and composition order. The Mathlib equivalence theorem
   requires both objects K-injective and cannot replace the one-sided retraction.
   Removed unnecessary public imports in the new modules; recompiled successfully.
   Completed the list of old immediate dependencies removed above. The unit
   sk-thm-properbasechange realized statement/steps stay intact, with the envelope
   and kernel/cone route preserved transitively. Verdict: pass.
5. Matched all new node Lean signatures verbatim, their proof-dependency sets to
   the union of step uses, and each proof_origin to its written argument. Checked
   source, chapter, unit, blueprint ancestry, creation data and actual logged
   searches. The replacement node accurately records its envelope, levelwise
   abelian and kernel/cone dependencies. Verdict: pass.

Changed only unnecessary imports in the three new modules and reporting:
corrected the claim that all original imports were unchanged, completed pruning,
and recorded this independent reading. No proof or statement repair was needed;
no additional holes were introduced or closed by this reading. One original hole
is closed by a decomposition with two added holes (net -1); the new replacement
statement is proved relative to existing imported obligations.
