## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.SmoothAtPrimeArtinianLiftingReverse`
with a complete Lean reduction. The proof constructs a localized finite polynomial
presentation and proves the localization map surjective by lifting numerators and
denominators. A proved private tensor/quotient helper converts a conormal retraction
modulo the maximal ideal to residue-field injectivity. Mathlib's finite-free local
splitting criterion gives the full conormal splitting; its extension criterion gives
formal smoothness, and its smooth-locus theorem and principal-open isomorphism give
the requested smooth neighbourhood. The original public signature and public imports
are unchanged. All new imports are proof-only. No definitions or interfaces were changed.

The new module `Sheaf.AlgebraicGeometry.ArtinianLiftingConormalModMaximal` isolates
the original Artinian-quotient construction and comparison (steps 7--11), specialized
to reduction modulo the maximal ideal. Both node proofs follow this actual route.

## Proved and sorry left

Closed: `AlgebraicGeometry.artinian_lifting_smooth_on_open_reverse`
(`lem-weil-pbc-smooth-at-prime-artinian-lifting-reverse`), the item's only original hole.
The private `AlgebraicGeometry.residue_injective_of_split_quot` is fully proved.

Added and left: `Algebra.artinian_lifting_conormal_split_mod_maximal`
(`lem-weil-pbc-artinian-lifting-conormal-mod-maximal`), exactly one named public theorem
with proof `:= by sorry`. There are no holes left in the item's module.
This is a decomposition (one upper hole closed, one strictly intermediate hole added),
not a claim that the Artinian lifting criterion is proved without remaining holes.
The new lemma assumes neither finite type of A nor formal smoothness of the extension
ring and concludes only a quotient-level linear retraction, without a geometric conclusion.

Compilation: the two delivery modules compile together in import order with lcompile.py.
The delivery dry run printed OK after compilation, axiom probing and static preflight;
only the second reading is pending, as the worker brief requires. Nothing was pushed.

## No longer needed

Removed all four original proof imports from the item's module:

- `Sheaf.Paper.ArtinianIdealLengthOneFiltration`: retained as a proof dependency of the new lemma.
- `Sheaf.RingTheory.KaehlerDifferentialsModPowerIdeal`: retained as a proof dependency of the new lemma.
- `Sheaf.RingTheory.JacobiZariskiQuotientSmooth`: unused on the entire new route.
- `Sheaf.RingTheory.SplitInjectionAfterCompletion`: unused on the entire new route.

The first two have moved to the new lemma and are not pruned. The latter two modules
and their exclusive descendants are candidates for removal from this item's import closure;
other target paths may still need them. No global unreachability is asserted.

Original proof dependency nodes no longer used by either delivered node:

- `lem-weil-pbc-jacobi-zariski-quotient-smooth`
- `lem-weil-pbc-kahler-differentials-localization`
- `lem-weil-pbc-morphism-factors-through-open-subscheme`
- `lem-weil-pbc-polynomial-ring-kahler-basis`
- `lem-weil-pbc-split-injection-after-completion`

The polynomial basis and explicit localized-differential comparison are unnecessary:
essential finite type supplies differential finiteness, and formal smoothness plus
locality supplies the free target. Jacobi-Zariski is replaced by Mathlib's extension
criterion. Completion is replaced by the finite-free local residue-field criterion.
Artin-Rees and differential reduction modulo ideal powers are still needed within
the new Artinian conormal lemma; they are not pruned.

## Where the brief, the DAG or earlier work was wrong

No statement or target correction. The original plan is valid but longer than needed:
it asks for splitting modulo arbitrarily high powers and then completion, while here
the target is finite free over a local ring and a retraction modulo the maximal ideal
already suffices. The original theorem docstring is preserved as the source plan;
the module docstring explains the actual shorter route, recorded in the updated node.

The ancestor node's review note suggests the residue-field criterion also removes
Artin-Rees. This delivery does not claim that: Artin-Rees is retained to compare the
Artinian quotient's conormal source with the original source modulo the maximal ideal.
A relation in a high maximal-ideal power illustrates why naive low-order truncation
can lose a conormal class.

The referenced `literature/stacks-project/algebra.tex` is absent in this clone.
The source proof was read at https://stacks.math.columbia.edu/tag/02HT, alongside the
original detailed node. All writes remained in the assigned sandbox.
The unit `sk-thm-p1` and its realized statement/steps are unchanged; this item lies
strictly below that unit's own declarations.

## New nodes

`lem-weil-pbc-artinian-lifting-conormal-mod-maximal` in
`dag/nodes/sec-proper-base-change/`: conormal splitting modulo the maximal ideal for
any Noetherian local R-algebra extension onto A_q. The source construction uses
Artinian quotients, a length-one filtration, localization and quotient uniqueness,
square-zero conormal retraction, Artin-Rees and differential reduction. Its docstring
and node give the complete proof in words. Edge cases checked: zero kernel, zero
polynomial variables, arbitrary residue characteristic, the required exponent N>=2,
and universe enlargement by ULift. R or A being the zero ring is excluded by the
existing prime/local hypotheses. No arbitrary object is defined from its unproved
existence assertion. Searches: LeanSearch unavailable (Internal Server Error);
LeanFinder and grep returned related constructions but no matching implication;
the imported blueprint and both library roots were searched before adding the node.
No change record is required because no existing statement, definition or visibility changed.

## Second reading by F1

1. **Interfaces: pass.** Compared the complete delivered item with the repository
   using diff, and compared its theorem header through `:= by` byte for byte.
   The existing public signature, docstring and public imports are unchanged.
   The only additional declaration is a private proved helper; no definition or
   target is changed, and no change record is required.
2. **Proof and trust: pass as a decomposition.** Compiled both modules in import
   order with lcompile.py, without errors or warnings. Independently compiled
   scratch copies with `#print axioms` for all three declarations. The private
   helper has only propext, Classical.choice and Quot.sound. Both public theorems
   additionally have sorryAx, as expected from the single reported new hole.
   Static inspection found exactly that named theorem's `:= by sorry`, no hollow
   definitions and no forbidden trust mechanisms. The extension's section is
   chosen from the locally proved surjectivity, not an unproved existence theorem;
   retractions obtained from the open lemma are used only in proofs.
3. **Split statement: pass.** Read the quotient construction against Stacks Tag
   02HT, including the filtration, section and Artin-Rees comparison. The argument
   applies to any Noetherian local extension ring; finite type and formal
   smoothness of that ring are not needed for this intermediate conclusion.
   Checked zero kernel, field extension ring, zero-variable presentation, N=c+1
   with c>=1, arbitrary residue characteristic and universe lifting. In particular
   N>=2 kills the extra differential relations modulo the maximal ideal, while
   Artin-Rees prevents losing conormal classes. This quotient-level retraction is
   strictly a part of the argument, not the geometric theorem under another name.
   Independent LeanFinder search for residue-field cotangent injectivity and
   Loogle search for Algebra.Extension.cotangentComplex found related Jacobian
   criteria, not the Artinian-test implication; rg searches of both library roots
   found no duplicate. The remaining hole is substantial and was not closed.
4. **Route and pruning: pass.** Read Mathlib's local finite-free splitting theorem
   and the local Jacobian criterion. The existing direct splitting proof is valid;
   the latter criterion only packages the same argument and does not remove the
   remaining Artinian construction. Proof-only imports supply the actual proof
   and the remaining lemma's documented plan. Compared the old proof_deps against
   both delivered nodes: the five removed nodes listed above are exactly the
   dependencies no longer used. The two retained original imports remain needed
   below the split lemma. Read sk-thm-p1.json's realized statement and steps:
   this change is below them and bypasses none of their declarations.
5. **DAG: pass.** The existing node changes only proof, proof_deps and proof_origin.
   Its steps agree with the localized polynomial construction, proved quotient/
   tensor helper, finite-free splitting and principal-open conclusion. The new
   node has the complete statement, source proof, dependency union, search records,
   provenance, blueprint reference and verbatim Lean signature required by the
   standing brief. Its docstring supplies the same complete argument.

Second reading changed only this report, adding the independent checks and their
verdicts. No mathematical, Lean, import or DAG repair was necessary. The result
remains one original hole closed and one strictly intermediate hole added: net
zero holes closed, with the two reported import branches removed from this route.
