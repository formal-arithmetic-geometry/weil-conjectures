## What changed

Preserved the statement of `CategoryTheory.exactProductFunctorStrictLimit` verbatim.
Its proof assembles the signed Roos comparison, the canonical chain comparison,
localization descent, ordinary-limit preservation, and triangle and augmentation
compatibility. Ordinary-limit preservation follows from Mathlib's construction of
limits from products and equalizers, using countability of the tower category.

Four separate Roos lemmas organize the argument. The chain lemma constructs the
comparison with Mathlib's cone and shift isomorphisms, then verifies its coordinates
and naturality by product projections. The compatibility lemma constructs the
projection, boundary and augmentation as actual chain maps and transports their
equations through the exact functor's localization and shift comparisons. The descent
lemma uses full faithfulness of restriction along localization to construct lambda.
The resolution lemma extends injective-term normalization to every complex by
naturality, and uses K-injective derivability to prove invertibility of the derived
units. Their naturality then gives the formula for every supplied resolution.

No existing public signature, definition, or public import changed. The item's new
imports are proof-only. All work remains in this item's sandbox.

## Proved and sorry left

Original holes: 1, in `CategoryTheory.exactProductFunctorStrictLimit`.
Its replacement proof and all four new lemmas contain zero `sorry`:

- `CategoryTheory.exactProductFunctorStrictLimit`;
- `CategoryTheory.exactProductFunctorRoosChainMaps`;
- `CategoryTheory.exactProductFunctorRoosCompatibility`;
- `CategoryTheory.exactProductFunctorRoosResolution`;
- `CategoryTheory.exactProductFunctorRoosDescent`.

Holes added: 0. No unfinished statement is split off. All private helpers are proved,
and every definition has a concrete construction. The inclusion choices in the
resolution proof are uniquely determined by their coordinate equations and are
eliminated inside a proposition. No arbitrary data is chosen from an unproved
existence assertion. Imported declarations retain their own existing obligations.

Validation: the resumed required delivery dry run compiles all five modules
without compiler diagnostics and passes stage-3 preflight (CODEX review class).
A source comparison confirms the original theorem signature is verbatim unchanged;
all five DAG Lean records agree with their module signatures, and every Lean line
meets the 100-character limit. Preflight initially required a record for the
private proof-context commands; the added change record resolves that diagnostic.
The latest dry run's main-module axiom probe received no response from the busy
compile server; earlier checks received no response for compatibility and descent.
The delivery command retries the probes, and the merge checks them again. No
nonstandard axiom was reported by the probes that returned.

## No longer needed

Removed direct proof imports of
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`,
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`, and
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients` from
the item. The final proof uses strict Roos comparison and Mathlib's exact-functor
and limit APIs instead of their separate derived-product and tower-site arguments.

The item's direct proof dependencies no longer include
`lem-weil-derived-limit-products-core`, `lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`,
`prop-pur-kinjective-resolutions-exist`,
`lem-sf-exact-functor-derived-triangulated`, or
`lem-weil-tower-category-levelwise-abelian`. Some are used transitively or provided
by Mathlib; none is claimed globally pruned. Removed obsolete direct tool-use
approvals for `lem-weil-derived-limit-products-core`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`, and
`prop-pur-kinjective-resolutions-exist`. No module is withdrawn.

The chain lemma needs only its statement imports and Mathlib's cone API. The descent
assembly needs localization infrastructure and the resolution formula. Removed
exploratory imports of `RingedSiteKInjectiveResolutionsOfUniverses`,
`GrothendieckAxioms.FunctorCategory`, `Adjunction.Evaluation`, and
`KInjectiveResolutionInjective` from descent; the last three are needed in the
resolution module instead. The resolution argument avoids the original plan's
separate homotopy-refinement comparison by extending normalization with naturality.

## Where the brief, the DAG or earlier work was wrong

The retained report described two open lemmas, while subsequent interrupted work
had supplied their full proof bodies. Their remaining issues were elaboration and
rewrite errors. The resumed work checks the current sources and repairs those
errors before delivery; the report no longer counts a decomposition as a proof.

The signed-coordinate identities require explicit cone and shift transport. The
implementation uses Mathlib's actual cone comparison and commutative-shift API.
No mathematical statement is disputed. The unit `sk-prop-sf-cbc` has empty realized
statement and step lists, so no recorded unit statement or step is bypassed.

## New nodes

`lem-cbc-exact-product-functor-roos-chain-maps` realizes the chain-level parts of
original steps 1 and 3. Its proof constructs the cone isomorphism and verifies both
coordinates and naturality, with no new assumptions or remaining holes.

`lem-cbc-exact-product-functor-roos-descent` realizes localization in original step 4
and combines it with the resolution formula. Full faithfulness descends the
specified natural isomorphism and gives its square.

`lem-cbc-exact-product-functor-roos-resolution` proves only the arbitrary-resolution
formula for a fixed lambda and square. It does not construct lambda or assert any
triangle or augmentation property. Its proof first extends eta theta = Q(iota) to
all complexes, then uses invertibility of units on K-injectives and naturality.

`lem-cbc-exact-product-functor-roos-compatibility` realizes original steps 5 and 9
for a fixed chain comparison and localization square. It constructs the prescribed
triangle and augmentation maps and proves their localized equations. It makes no
resolution assertion and does not choose lambda.

Zero complexes, zero transitions, and the identity functor satisfy these
constructions. The coordinate equations determine the cone maps, and full
faithfulness of localization determines lambda. These are separate parts of the
original argument; every new theorem is proved in this delivery's sources.
Change record: `coord/changes/exactProductFunctorStrictLimit-private-proof-context.md`.
It documents private-helper context and elaboration commands flagged by preflight;
existing signatures, definitions and public imports are unchanged. The downstream
audit lists all 264 transitive importers and requires no consumer adaptation.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
