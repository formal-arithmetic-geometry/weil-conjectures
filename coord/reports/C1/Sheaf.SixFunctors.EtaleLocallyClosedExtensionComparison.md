## What changed

Proved `AlgebraicGeometry.etale_locallyClosed_extension_comparison` completely in
`Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison`, preserving its exact signature
and every existing definition and public import. The two retained proof imports are:
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` and
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp`.

Five proved private helpers supply the argument: `normalized_iso_unique`,
`normalized_iso_exists`, `closure_factorization_square`, `closure_factorization_iso`, and
`closure_closed_composition_iso`. The closure square follows from kernel base change.
The two closures for a closed composition have equal ideal sheaves over X; their closed
lift is therefore an isomorphism. Composition of direct images, identification of direct
image with open extension along this isomorphism, and composition of open extensions give
the second comparison. A categorical adjustment by an automorphism of the identity functor
normalizes each initial comparison. Full faithfulness proves uniqueness. The finite/open
comparison is applied directly to ModuleCat A, so there is no separate scalar descent.

Updated the existing node's proof, proof_deps, proof_origin, and obsolete tool approvals to
match this route. No new modules, statements, definitions, nodes, or change records.
The unit's realized fields are empty; no realized unit statement or step is bypassed.

Validation: the complete Lean module compiles through lcompile.py. Its public theorem
signature was compared verbatim with the original. All lines have at most 100 characters.
The proof uses neither a new axiom nor any forbidden declaration form. Edge cases checked:
empty source and ambient schemes, identity immersions, pure open and pure closed immersions,
nonreduced closed subschemes, and Y=X. The kernel argument keeps the scheme structures;
no set-theoretic equality is used in place of scheme-theoretic equality.

Searches: leanfinder for locally closed extension independent of closed/open factorization
found only immersion geometry; loogle for IsPullback/toImage found the canonical coborder
square but no arbitrary-factorization comparison; grep for full-faithfulness/whiskering
found the generic categorical APIs. Repository rg found finiteOpenComparison and the
existing composition and full-faithfulness APIs used here. No duplicate comparison theorem
was found.

## Proved and sorry left

Closed 1 of the original 1 holes:
`AlgebraicGeometry.etale_locallyClosed_extension_comparison`
(node `lem-sfb-etale-locally-closed-extension-comparison`).

Holes added: 0. Split off: 0. Sorries left in the delivered module: 0.
All five new private helpers are fully proved.

## No longer needed

All original public imports remain: they support the existing statements and restriction
definitions. Compared with current sources, removed these private proof imports:
`Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`,
`Sheaf.CategoryTheory.RingedSiteModules`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and
`WeilConjectures.SixFunctors.OpenClosed.Complex`. The essential-image and ringed-site
modules are unused; the other APIs are already available through the public imports.
Added the proof import `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp`
for composition of open extensions. A trial explicit proof import of
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful` was removed as
redundant; its API is already available through the retained imports.

The proof no longer uses `lemma-nagata-scheme-image-of-closed-immersion` as a separate
comparison step. Kernel base change directly identifies the closed subschemes in the
closure square. Its standalone image-identification work is unnecessary here.

The proof does not import or use `lem-kun-04ca` /
`Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`. Its essential-image/support
characterization is unnecessary; the already-proved closed counit and full-faithfulness
API in `WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion` suffice. These two obsolete
tool approvals were removed from the node, preserving the order of those retained.

`def-weil-pbc-constant-sheaf` and `def-weil-sheaf-of-modules-category` are no longer proof
dependencies: the comparison library is generic in the coefficient category, so its
ModuleCat specialization already consists of A-linear morphisms. Both remain statement
dependencies, unchanged, as required by the node's coefficient conventions.

No original module has become globally unnecessary or is withdrawn. The closure-square
and closed-composition geometry, open unit, closed counit, adjunction and inverse/direct
image constructions are all retained.

## Where the brief, the DAG or earlier work was wrong

The DAG's scalar enhancement step need not be repeated: the library's finite/open theorem
already accepts ModuleCat A. The Noetherian argument can be made purely topological:
the source embeds into Noetherian X, hence every map from that source is quasi-compact.
In particular one need not separately prove that the closed ambient Y is Noetherian.

The original proof plan and docstring asserted that the unadjusted finite/open comparison
has the exact displayed restriction normalization. This delivery instead proves the
required normalization by a general naturality argument and obtains the unique normalized
comparison from it. No unproved mate-coherence calculation is used.

The node's unit record is historically assigned to sk-lem-sf-flat-model although the
node's chapter is sec-six-functors-basics; this pre-existing mismatch was left unchanged.

The rewritten proof adds existing generic tools `prop-openclosed-lowerstar-fully-faithful`
and `lem-cbc-extension-zero-composition` as proof dependencies. The former is the exact
already-imported counit/full-faithfulness API, and the latter is the already-proved open
composition isomorphism used when transporting across the closure isomorphism. These
supply elementary general tools unavailable as statements of this item's unit. Approval
of new tool_uses remains with the maintainer; no tool_uses entries were added here.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
