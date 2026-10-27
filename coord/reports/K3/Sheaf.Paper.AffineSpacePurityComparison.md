## What changed

Filled all eleven theorem proofs in
`lean/Sheaf/Paper/AffineSpacePurityComparison.lean`. All signatures, attributes, public
imports, docstrings, and definition bodies are unchanged. No other module is edited.

The coefficient annihilator is transported through `AffineLinePurity.ringEquiv` from the
already proved `PurityFiniteSetting.diagonalExponent_annihilates`, then multiplied by ell.
Projection compactifiability is proved by induction: given a compactification
`X_d -> Z -> Y`, compactify the affine line over Z, postcompose its proper part to Y,
and precompose its open part with `AffineSpace.map` of `X_d -> Z`. The map-over equation
identifies its composite with the actual tower projection. This constructs the required
compactification for arbitrary Y without a quasi-compactness assumption on Y.

Tower geometry uses the existing affine and locally finite-type projection instances;
Noetherianness follows over Spec k. The source and exceptional coordinate lemmas unfold
only the recorded functors. For each unique-transport theorem, the raw composite itself
has the required endpoints after the zero/successor case split, and HEq fixes its hom;
`Iso.ext` or `eq_of_heq` gives uniqueness.

For applicability, the invertible comparison unit identifies Ke with the actual
`Rnu_* K`, preserving its finite-Tor property. Apply the source library's existing
`Etale.constructibleFiniteTor_rightDerivedUpperShriek` directly to that object, and its
bounded-below exceptional-image lemma to K. Derive the required invertible-exponent
instance from `annihilates` and `exponentUnit`; quasi-compactness for bounded-below
preservation follows from `tower_noetherian` at zero. The all-stage version separates
zero from the positive-stage clause. The ordered four-arrow recursion is unchanged.

Validation: single-file remote compilation through lcompile.py; delivery performs the
required compilation and axiom probe. No new lemma or construction is introduced.

## Proved and sorry left

Closed 11 existing holes; added 0 holes; 0 holes remain in the delivered module.
All names below are in `AlgebraicGeometry.ProEtale.AffineSpacePurity` and attached to
`def-pur-affine-space-comparison`:

- `annihilates`
- `projection_geometry`
- `tower_geometry`
- `tower_noetherian`
- `lineSource_obj_eq`
- `exponentUnit`
- `sourceReassociation_existsUnique`
- `exceptionalEtale_eq`
- `exceptional_applicability`
- `stage_applicability`
- `exceptionalComposite_existsUnique`

This is proof completion, not decomposition. Existing dependencies such as
`AffineLinePurity.source_eq` and `AffineLinePurity.primeUnit` retain their own proof
obligations; none is duplicated here.

## No longer needed

No existing imports, nodes, or modules are withdrawn. Temporary private imports of
`Sheaf.Paper.FixedFinitePositiveCoefficientTwist` and the upstream upper-shriek stability
modules were removed: the existing public import closure already provides their APIs.
No new imports remain.

The specific proof of `exceptional_applicability` does not need the detour through
`sf_preservation_class`, affine chart presentations, and finite-Tor reflection. The
existing ordinary-etale finite-Tor preservation theorem applies directly to the
canonical Rnu_* antecedent once it is identified with Ke. The published source module
and all existing public imports remain available to other consumers. No unit step or
construction dependency is pruned: this is the same finite-Tor applicability clause of
the definition, with no change to the unit's affine-line iteration route.

## Where the brief, the DAG or earlier work was wrong

The compactifiability docstring suggests composition of compactifiable morphisms, but
there is no unrestricted composition instance, and the arbitrary base Y is not assumed
quasi-compact or quasi-separated. The proof supplies the missing explicit construction
by lifting the last affine line to the preceding compactification. It works also for
zero dimension and empty schemes.

The applicability docstring describes a longer proof via fixed-coefficient preservation
and reflection. The current source library already states the ordinary-etale
preservation result for the exact canonical antecedent; the comparison unit makes that
shorter route available. No mathematical statement changes, new nodes, or DAG route
changes to the ordered comparison definition are required.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
