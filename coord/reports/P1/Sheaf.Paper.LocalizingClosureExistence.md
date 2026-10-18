## What changed

Proved `AlgebraicGeometry.ProEtale.localizingClosure_exists` with its complete original
signature, for arbitrary condensed rings, without a commutativity hypothesis. The proof
uses the existing source theorem `Mod.isGrothendieckAbelian`, K-injective resolutions,
and the proved derived coproduct statements. A private construction transports Mathlib's
product-of-distinguished-triangles theorem through the opposite-triangle equivalence;
its three vertex cocones are proved to be coproducts. The intersection's closure conditions
and universal property are proved directly. Small coproducts in the full subcategory
follow by universe lifting the indexing type. Its idempotent completeness then gives
retract stability by uniqueness of splittings. The comparison of generating classes is
proved pointwise from minimality.

Only the assigned module and its node are changed. No new public declarations or
intermediate obligations are added. The unused public Tor-amplitude import is removed;
the associated import-interface record is `coord/changes/P1-localizing-closure-imports.md`.

Validation: the complete assigned module compiles without warnings in 8.6 seconds.
The axiom probe and delivery preflight passed. All six direct importers compile unchanged
against the modified module, individually within 30 seconds. A text comparison confirms
the original theorem signature is identical, and all delivered Lean lines are at most
100 characters. The unit record has no realized statement or proof steps to bypass.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.localizingClosure_exists`
(node `det-def-localizing-closure-existence`), one original hole.

Added: none. Remaining holes in delivered Lean files: zero. This is a proof from existing
library declarations, not a decomposition. The inherited upstream obligations reached by
those declarations remain the responsibility of their existing items.

## No longer needed

Removed imports:

- `Sheaf.Paper.ConstantModelTorAmplitude` (the assertion is for arbitrary S and does not
  use constructibility or Tor amplitude).
- `Sheaf.CategoryTheory.SheafTensor`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`.
- The redundant private `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic` import.

Unused former proof dependencies:

- `sk-def-sfb-sheaf-tensor`, `lem-pc-sites-sheaf-tensor-bilinear-universal`,
  `def-weil-sheaf-of-modules-category`, and `lem-weil-pbc-ring-sheaves-grothendieck`:
  the source theorem proves the Grothendieck property directly for internal left modules,
  including noncommutative monoids. No reconstruction of sectionwise rings or actions is
  necessary.
- `def-weil-pbc-proetale-site` and `def-weil-size-convention` remain statement conventions;
  no separate site-skeleton construction is needed by this proof.
- `lem-sbc-biproduct-triangle-distinguished`: retract closure follows from the existing
  proved countable-coproduct idempotent-completeness theorem and uniqueness of splittings.
- `det-def-sfb-constructible-tor-amplitude` remains only an optional example in the node's
  mathematical statement, not a Lean import or proof dependency.

The cone-sum calculation and the nonzero-idempotent counting argument for large index sets
are unnecessary: Mathlib supplies triangle products, and the actual landed closure
predicate already closes under every existing coproduct in the object universe. Universe
lifting suffices for the small coproducts needed to split idempotents.

Withdrawn obsolete tool approvals on the assigned node:
`lem-pc-sites-sheaf-tensor-bilinear-universal` and
`lem-weil-pbc-ring-sheaves-grothendieck`. The derived-coproduct approval is retained.

No modules or nodes are deleted. These are dependencies pruned from this proof; other
parents may still need them.

## Where the brief, the DAG or earlier work was wrong

The original plan overlooks the existing noncommutative `Mod.isGrothendieckAbelian`
theorem. Its proposed sheaf-module identification is valid but unnecessary. The
sum-of-cones calculation can likewise be replaced by duality from Mathlib's
`productTriangle_distinguished`. The localizing closure and all target signatures are
unchanged. Empty families, arbitrary or empty S, zero rings, and empty schemes introduce
no additional hypotheses; the arguments are uniform in these cases.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
