## What changed

Replaced the earlier invalid sandbox decomposition with a checked reduction of
`AlgebraicGeometry.Scheme.Modules.exists_proper_flat_finitePresentation_model`.
Its signature, visibility and original docstring are unchanged. Two new proof-only
imports supply bounded perfect-model existence and a general affine truncation lemma.
The proof constructs the final complex as `C.truncGE 0`, proves its upper bound using
Mathlib's term isomorphisms, and composes the two homology isomorphisms for each
cartesian square. No definition chooses data from an unproved existence theorem.

The unit's Noetherian approximation/proper coherence route stays inside the bounded
perfect-model step. The normalization is a separate algebraic step with no proper
morphism or coefficient sheaf. All three delivered modules compile through lcompile.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.Scheme.Modules.exists_proper_flat_finitePresentation_model`.
This is a decomposition, not a sorry-free proof: two holes are added, for net -1.
There are no sorries left in the item's module. The two new sorries are:

- `AlgebraicGeometry.Scheme.Modules.exists_proper_flat_boundedPresentation_model`
  (node `lem-pc-proper-flat-bounded-presentation-model`): bounded perfect-model
  existence with universal comparisons, without nonnegative termwise support.
- `AlgebraicGeometry.Scheme.Modules.affine_flat_connective_truncation`
  (node `lem-pc-affine-flat-connective-truncation`): flat finite-presentation
  terms and universal homology comparison for the concrete lower truncation.

Each is exactly `:= by sorry` in a separate new module with a source and full
natural-language proof. The second lemma is purely algebraic geometry on an affine
scheme and has no f or F. The first stops before the flat-opcycle step, so neither
is the original theorem with its hypotheses repackaged. Edge cases checked in
words: empty affine scheme, zero sheaf/complex, upper bound zero, and nonaffine new
bases. Arbitrary module tests are recovered from square-zero algebra base changes.

## No longer needed

No repository imports were removed: the item's three public imports are needed by
its unchanged signature. From the previous unpublished sandbox attempt, removed
`Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationStructural` and
`Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationComparison`, their two theorem
holes and their two uncommitted node files. They are not part of this delivery.

The original plan's `lem-pc-pseudo-coherent-bounded-finite-free-model`, module
`Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel`, is unnecessary for this
proof route: directly truncate the bounded finite-projective model supplied by
`lem-pc-perfect-affine-bounded-projective`. There is no separate finite-free
resolution or upper-tail cancellation. The other original dependencies remain
needed in the two new nodes' plans (proper perfect direct image, affine perfect
models, affine sheafification, derived base change and the flat-opcycle criterion).
Pruning is local to this item's route; other targets may still need the module.

For completeness, all six old direct `proof_deps` are absent from the new top-level
proof. Five are retained transitively in the new lower plans:
`lem-pc-proper-support-perfect-direct-image`,
`lem-pc-perfect-affine-bounded-projective`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-pc-rf-base-change-complex`, and
`lem-pc-module-flat-opcycles-tor-criterion`.
Only `lem-pc-pseudo-coherent-bounded-finite-free-model` is removed from the whole
local planned route. No module is certified as pruned from the targets' import
closure by this delivery; no original import was removed.

## Where the brief, the DAG or earlier work was wrong

The prior sandbox comparison statement was false. It asserted the universal
cohomology comparison for every structurally bounded flat complex, with no link
between that complex and f,F. For f the identity of a nonempty affine field
spectrum and F its structure sheaf, B=0 satisfies every structural hypothesis,
but its degree-zero homology is zero and f_*F is nonzero. The prior structural
existence statement also had no cohomological content: B=0 always sufficed.
Those uncommitted lemmas were deleted, rather than used as axioms or marked as
repository statement disputes. Their node records improperly copied review
metadata and did not contain verbatim Lean signatures; all new records are fresh.

The old plan's finite-free resolution is not required: its bounded projective
model can be truncated directly using universal negative vanishing. This does
not bypass the unit's proper coherence/Noetherian approximation argument.
LeanSearch was attempted twice and returned Internal Server Error; recorded as
unavailable. LeanFinder, Loogle and source grep were run; no exact theorem was
found. Stacks Tags 0B91, 08EB and 0653 were checked online. No repository interface
or target statement was changed, and there are no forced adaptations.

## New nodes

`lem-pc-proper-flat-bounded-presentation-model` lives in
`Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel`. It isolates the
perfect direct-image and affine model step before imposing a lower support bound.
Its node records the actual signature, source, proof steps and performed searches.

`lem-pc-affine-flat-connective-truncation` lives in
`Sheaf.AlgebraicGeometry.AffineFlatConnectiveTruncation`. It states the flatness,
finite presentation and universal nonnegative homology of canonical truncation;
its proof tests flatness with square-zero algebra base changes and uses the
flat-opcycle criterion. Its node records the actual signature and performed
searches. Blueprint searches for flat opcycles and bounded perfect models found
no matching blueprint nodes. No change record is required: existing signatures
and visibility are unchanged.


## Second reading by Y2

1. **Interfaces: pass.** Read the complete diff against the repository. The sole
   existing theorem's signature is byte-for-byte identical, including its
   universes, hypotheses, base-change quantifiers and conclusion. Its docstring
   and visibility also stay identical. Only its proof and two ordinary imports
   change; no existing definition, target or other module is adapted. The new
   statements have no change records because they are new declarations.
2. **Kernel checks: pass as a decomposition.** Recompiled all three delivered
   modules with `lcompile.py --all`; no errors or warnings. Scratch copies with
   `#print axioms` for each of the three declarations compiled and printed exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Source scans found
   only the two reported theorem sorries and none of the forbidden constructs.
   There are no definitions in the delivery, hence no arbitrary witness is used
   as definitional data. One upper hole is closed, two lower holes added: net -1,
   not a sorry-free proof or positive ledger progress.
3. **Split statements: pass.** Independently read
   [Tag 0B91(2)](https://stacks.math.columbia.edu/tag/0B91),
   [Tag 08EB](https://stacks.math.columbia.edu/tag/08EB), and
   [Tags 0653](https://stacks.math.columbia.edu/tag/0653) and
   [0654](https://stacks.math.columbia.edu/tag/0654).
   Finite presentation in Mathlib supplies quasi-coherence, so the coefficient
   sheaf meets the perfect-direct-image theorem's requirements. Properness
   supplies quasi-separatedness. The bounded-model lemma isolates the geometric
   perfectness/base-change step without lower termwise support; the affine lemma
   isolates lower truncation without a proper map or coefficient sheaf. Neither
   restates the item. For the affine lemma, square-zero A-algebras test every
   A-module N: P tensor (A ⊕ N) splits as P ⊕ (P tensor N), so vanishing in
   degree -1 gives flatness of the degree-zero opcycle by the existing criterion.
   Its finite presentation follows from a cokernel of finitely presented modules.
   Pullback preserves cokernels, and Mathlib's canonical truncation projection
   preserves all nonnegative homology. This also handles nonaffine new bases
   locally. Checked zero complexes, empty affine schemes, b=0, a>0, and identity
   maps; no counterexample or missing nontriviality hypothesis arises. A complex
   with a nonflat zeroth opcycle fails the universal vanishing test. Both new
   modules include source-cited complete prose proofs and matching nodes.
   Independent LeanFinder searches used connective derived pushforward and
   right-exact functor terminology; Loogle inspected truncation declarations and
   attempted higherDirectImage (absent from that index); source grep covered
   Mathlib, upstream and Sheaf. No complete existing theorem matches either new
   statement. Closing either lower hole needs substantial affine/derived bridges,
   not a few-minute application of an existing lemma.
4. **Route and pruning: pass, report clarified.** Read the existing geometric,
   affine-model, derived-base-change and flat-opcycle declarations. They are
   ingredients, not direct replacements for either new statement. The explicit
   top-level proof takes B=C.truncGE 0, transports upper support using
   `truncGEXIso`, and composes the homology isomorphisms. Both new imports are
   needed only by this proof and correctly use ordinary `import`. Public imports
   in the new files supply the names used by their signatures. All six former
   direct dependencies are now explicitly accounted for above. The unit
   `dag/units/sk-thm-picard-coherence.json` retains its Noetherian approximation,
   proper coherence and universal bounded-model route inside the geometric lower
   statement. Its repository `realized` record is already empty; this delivery
   does not alter it or bypass a realized unit step. No target-closure module
   pruning is claimed.
5. **DAG: pass.** Checked the existing node diff: only `proof`, `proof_deps`,
   `proof_origin` change. Each dependency list equals the union of its proof-step
   uses. Every new node has its source, statement dependencies, complete proof
   plan, origin, searches, status, creation and blueprint records, chapter/unit,
   and Lean record. Each new `lean.statement` is the verbatim signature of the
   corresponding theorem; both new files and ids are absent from the repository.
   The top node records precisely the reduction compiled by Lean.

Second-reading changes: expanded the pruning account to enumerate every removed
old direct dependency and distinguish retained lower-plan dependencies from
actual target-closure pruning; recorded the independent Loogle checks in both
new nodes; corrected the bounded-model node's origin text, which had mistakenly
mentioned square-zero testing belonging only to the affine lemma. Lean code and
all signatures required no repair. The two lower holes remain openly reported.
