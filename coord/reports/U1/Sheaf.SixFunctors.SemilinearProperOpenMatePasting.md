## What changed

The assigned module proves `rhoPullInv_isIso` and `rhoR_isIso` from the ordinary
and derived scalar-comparison packages. The private comparison with the chosen
scalar functor retains its section normalization and transition equation.
Uniqueness identifies the ordinary inverse mate with the conjugated package
comparison. Exact localization and mate whiskering identify the derived mate
with the invertible comparison proved by the derived package's private
`scalarD_isIso` component.

The ordinary restriction construction is proved over a general site and ring
family, then specialized. Exactness and the normalized direct-image comparison
are transported through the resulting isomorphism. Exactness uses only the
ordinary scalar restriction record; the direct-image comparison additionally uses
the ordinary scalar adjunction record. The ordinary inverse mate and open-extension
isomorphism also use these smaller records. All public signatures,
non-theorem data bodies and public imports are unchanged.

Evaluation reuses `VaryingRing.moduleEvalP` and its forward section formula;
the isomorphism law gives the inverse formula. A separate canonical-comparison
helper serves the local proof. The existing private normalization helper retains
its original statement for import-all consumers. Section extensionality is shared
over abstract carriers. A single proved ordinary mate-normalization lemma supplies
the canonical comparison for ordinary, derived and open evaluation proofs.
Localization of a constant-diagram square is calculated over abstract exact
functors and reused in the derived and open arguments. The
general restriction construction retains an abstract sequence natural transformation
with its component equations, avoiding expansion of its concrete construction.
The open comparison uses the proved
`exact_localization_inverse_mate`, with a generic comparison of localized adjunctions.
The original `exact_hom_fac`, `normalized_square` and inverse-mate helper interfaces
are preserved for their consumers.

Proof-local attributes prevent unfolding the model ring and module pushforward
after their construction steps. Proved component formulas expose the
constant-diagram comparison without expanding its data in evaluation proofs.
Pushforward coherence batches its section-formula rewrites.
The standard derived-category construction, its localization functor and factor
isomorphism are locally irreducible. Ordinary evaluation is locally irreducible
after its section normalizations. Localization symmetry handles the derived inverse.
The node records the canonical evaluation construction as a direct use of
`def-sp-varying-ring-operations`. The proof imports `SemilinearScalarDerivedComparison`, `SemilinearScalarAdjunctions`
and `ExactLocalizationInverseMate`. No source-library module is changed.

Validation: public interfaces and non-theorem data bodies match the current source;
there are no added holes. Full-module runs report no Lean errors. The delivery gate
checks runtime, the sorry/axiom probe and server preflight. The six import-all
consumers were scanned; the four that use affected helpers retain their original
interfaces and need no adaptation.

The change record is `coord/changes/U1-semilinear-scalar-proof-scopes.md`, including
the table of 529 transitive consumers. Retained obsolete change records and
experiments are in scratchpad and are not part of the packet.

## Proved and sorry left

Closed two of the original six holes:

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoPullInv_isIso`.
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoR_isIso`.

No holes added and no statements split off. The four retained holes are:

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting`.
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_identities`.
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_scalarRestriction`.
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_evaluation`.

All six declarations realize `lem-sf-semilinear-proper-open-mate-pasting`.

## No longer needed

No DAG nodes or modules were pruned. The remaining four clauses retain their
planned dependencies. No source-library declaration is removed or weakened.

Removed unused private helpers: `normalized_iso_transport`,
`pushforward_restrict_eq`, `sequence_push_scalar_normalized`, `rho_level_push`,
`constant_direct_image_map`, `sequence_push_evaluation_normalized`, and
`scalar_rho_iso`. The latter is superseded by `restriction_rho_iso` for the smaller
restriction record.
The canonical evaluation comparison makes the duplicate pushforward construction
and its coefficient-map computation unnecessary.

Removed the direct private import of `DerivedMateComparison`: the existing
`ExactLocalizationInverseMate` theorem supplies that argument. Removed the redundant
direct import of `SemilinearScalarOrdinaryComparison`, which is publicly imported
by the derived comparison module. Its declarations remain needed.
The full `derivedScalarComparison` conjunction is not used: its proved private
`scalarD_isIso` component gives exactly the direct-image invertibility required here.
The module and its node remain needed; no source declaration is withdrawn.
The full ordinary comparison record is unnecessary for exactness and the chosen
ordinary direct-image comparison, inverse mate and open-extension isomorphism:
these use the smaller restriction and adjunction records. The derived scalar
comparison still uses the full record.

## Where the brief, the DAG or earlier work was wrong

The retained packet needed carrier-normalization and elaboration repairs before
it could compile. The private scalar comparison needed a section-normalized
conclusion, rather than mere nonemptiness of the isomorphism type. Its only users
are in this module. The chosen ordinary scalar functor keeps its original inferred
signature and choice body.

The evaluation support modules import the assigned module, so importing them back
would create a cycle. Existing varying-ring operations and proved generic mate
arguments supply the evaluation support here. No faithfulness of derived
evaluation or scalar restriction on morphisms is assumed.

A scan of import-all consumers found uses of the private section-square,
normalization and localization APIs. Those names and statements are preserved;
private visibility alone does not make a declaration unused.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
