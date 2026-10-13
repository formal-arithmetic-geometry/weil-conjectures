## What changed

Proved `AlgebraicGeometry.affineSectionsUnit_transport` without changing its signature,
universes, visibility, or existing docstring. Added a proof-only import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` for preservation
of K-injectivity by an additive equivalence. All original public imports remain.

Three proved private helpers supply the resolution criterion, the affine restriction
equivalence, and the natural isomorphism of sections functors with the correct scalar
restriction. The main proof transports invertibility of the localized resolution map
through that natural isomorphism and the homotopy-category composition isomorphism.
The elaboration options are scoped to individual declarations. Updated the existing
node's proof and proof origin to describe these constructions; its proof dependencies
are unchanged.

Searches: LeanFinder for invariance of a right-derived unit under an equivalence;
Loogle for `AlgebraicGeometry.Scheme.Modules.restrictAppIso`; launcher grep and local
`rg` for derived-unit naturality, equivalence preservation of K-injectives, and affine
sections comparisons. The existing source theorem
`Functor.preservesKInjectiveComplexes_of_isEquivalence` provides the nontrivial generic
preservation result. No new unproved theory is needed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.affineSectionsUnit_transport`
(node `new-affine-sections-unit-transport`). Added zero holes; no `sorry` remains in
any delivered Lean file. This is a proof from the existing resolution machinery,
not a decomposition into new statements. The three private helpers are fully proved.
Single-file compilation through `lcompile.py` passes with no warnings.

## No longer needed

None. No original import, dependency node, or module is pruned. The original resolution
existence dependency remains needed. No affine acyclicity or tilde-unit modules are
introduced. The existing public imports continue to provide the statement's API;
the one added proof-only import is used for equivalence preservation of K-injectivity.

## Where the brief, the DAG or earlier work was wrong

The node's route is valid. Its elementary first step still requires explicitly
constructing the functor equivalences and checking the scalar action. This delivery
uses uniqueness of left adjoints to identify restriction with pushforward along the
inverse chart, rather than manipulating `restrictAppIso` at the image of top directly.
This avoids transport along an equality of opens. Naturality of the already chosen
derived units replaces the final abstract uniqueness comparison in the prose plan.
The result remains conditional and applies to arbitrary unbounded complexes, including
the zero complex and the empty affine scheme, with independent derived-category
universes and no quasi-coherence assumption.

The cited Stacks Tag 06Z0 (https://stacks.math.columbia.edu/tag/06Z0) supplies the
derived-sections context; the exact-equivalence transport is the agent-written formal
argument already identified as such in the original node. No unit-level route changes.

## Second reading by H3

1. Compared the delivered module with the repository version. The existing theorem signature,
universes, visibility, and docstring are byte-for-byte unchanged. The added import is proof-only,
and the three helpers are private. No external definition or statement changed. Verdict: pass.

2. Compiled the delivered module through `lcompile.py`: no errors or warnings. Inspected every
helper and the main proof: no `sorry`, forbidden declaration, or hollow definition. The affine
equivalences are explicit constructions; the resolution witness is used inside a proof only.
Checked the unit criterion by its naturality square and cancellation of invertible morphisms.
Scratch `#print axioms` checks for the main theorem and all three helpers show exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Verdict: pass.

3. There are no split-off statements or new public declarations. Read the upstream equivalence
preservation proof and the Mathlib restriction/pushforward adjunctions. Independently searched
with launcher grep for `isIso.*rightDerivedFunctorUnit|rightDerivedFunctorUnit.*resolution`
(no hits), and with local `rg` for transport and unit-resolution lemmas. No direct replacement
was found. The helpers apply equally to zero complexes and the empty affine scheme: the argument
requires only equivalences, additive functors, and resolutions, with no nonzero-object assumption.
Verdict: pass.

4. The proof retains the node's affine-equivalence and resolution-transport route. Its natural
isomorphism uses the inverse scalar map, verified by `Scheme.toSpecΓ_appTop`; uniqueness of left
adjoints avoids transporting top opens manually. All original imports remain needed for the
statement's definitions and instances; the new plain import supplies K-injective preservation.
The old proof dependency remains used, so `No longer needed` is complete. Read the unit's
`realized` record; this delivery leaves it and its route unchanged. Verdict: pass.

5. Compared both node JSON files: only `proof` and `proof_origin` changed. The two proof steps
accurately describe the implemented constructions, naturality criterion, and transport through
homotopy-category composition. `proof_deps` still names the used resolution-existence node.
There are no new nodes requiring additional fields. Verdict: pass.

Changed during second reading: appended this review only. No Lean or DAG repair was necessary.
