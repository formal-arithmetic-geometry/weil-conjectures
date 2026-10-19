## What changed

Proved `AlgebraicGeometry.Scheme.Hom.conormalStalkFibre_shortExact_of_smooth` in
`Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion`, preserving its entire statement and
all four existing definitions. No other Lean module changes.

The proof works directly with the surjection of actual stalk rings R -> S. Smoothness makes
S formally smooth over k. Mathlib's square-zero lifting theorem and
`retractionKerCotangentToTensorEquivSection` split the conormal map. Right exactness of tensor
products supplies exactness and surjectivity after tensoring with the residue field, and the
tensored retraction proves injectivity without a flatness assumption. Private proved helpers
identify relative-differential stalks with Kahler differentials using the universal derivation
and the stalk-skyscraper adjunction. Transporting the algebraic sequence through these
identifications proves both required generator formulas.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` for the existing stalk-skyscraper
API. Its import direction was checked and creates no cycle. The smooth-algebra and tensor
right-exactness APIs are already publicly available through the original smooth-morphism
import, so their redundant trial imports were removed.

Normalized the identity-morphism point in private helper types. This avoids repeated unfolding
of stalk colimits in comparisons involving `(identity Z) z`. Explicit arguments in the final germ rewrites avoid expensive inference through the tensor
and stalk definitions. The optimized full proof compiled in 12 seconds, within the existing
60-second file limit; no limit was raised and no file was split.

Updated only `proof`, `proof_deps`, and `proof_origin` of
`dag/nodes/sec-smooth-purity/lem-pur-conormal-sequence-smooth-immersion.json` to record the
implemented direct-stalk argument. The existing theorem docstring retains the original affine
proof plan. The unit and chapter routes are unchanged.

The static interface check flags the added private-proof section commands. Change record
`coord/changes/conormal-sequence-private-proof-section.md` documents their local scope and
the unchanged public interface. The downstream scan found no textual users of the five
existing declarations outside this module; neither direct importer needs adaptation.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Hom.conormalStalkFibre_shortExact_of_smooth`
(node `lem-pur-conormal-sequence-smooth-immersion`).

Holes added: 0. Holes remaining in the delivery: 0. Split off: 0.
Every private helper is proved, and every private definition is constructed from proved APIs.
This is a proof, not a decomposition.

## No longer needed

Removed these original proof-only imports:

- `WeilConjectures.AlgebraicGeometry.Thickening`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `Mathlib.RingTheory.Kaehler.Basic`
- `Mathlib.RingTheory.Localization.Ideal`
- `Mathlib.RingTheory.Localization.Basic`
- `Mathlib.RingTheory.Ideal.Maps`

The direct-stalk proof removes these eight entries from the node's proof dependencies:

- `lem-weil-pbc-closed-immersion-affine-cover-criterion`: only surjectivity on stalks is used.
- `def-weil-affine-spectrum`: no affine presentation is chosen in the proof.
- `def-sbc-first-order-thickening`: the square-zero lifting is performed algebraically.
- `def-weil-open-immersion`: no factorization through an affine open is needed.
- `lem-weil-pbc-affine-open-stalk-localization`: the argument starts with actual stalk rings.
- `lem-weil-pbc-spec-map-stalk-localization`: no localized affine quotient is compared.
- `lem-weil-pbc-localization-at-prime-of-quotient`: no localization of the conormal module occurs.
- `lem-weil-pbc-spec-tilde-stalk-localization`: the universal property identifies differential
  stalks directly, without tilde localization.

The public imports required by the unchanged statements and definitions are preserved.
No modules or nodes are withdrawn. Reachability elsewhere remains the maintainer's calculation.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The DAG's affine argument is mathematically
valid, but its localization steps are unnecessary once the existing smooth-stalk criterion and
stalk-skyscraper adjunction are used. Only the proof route below the unit level changed.
The proof assumes no smoothness of X, no closedness of z, and no flatness of its residue field
over S. The algebraic argument also covers zero kernel and zero tensor modules.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
