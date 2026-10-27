## What changed

Replaced the hole in `WeilConjectures.zlImmersionPullbackWeightPreservation`
without changing its signature, its weight predicates, its canonical pullback, or
any existing definition. The Lean argument transfers punctual purity, maps the
finite mixed filtration through an exact functor, uses the preserved-cokernel
isomorphism on each quotient, and applies the resulting assertion degreewise at
weight `w + a`.

Validation: all four delivery modules compiled together without warnings.

Exactness of precisely `zlWeilPull` is supplied by the existing
`zlWeilHeartLocalizationExact`. The closed-point step is proved directly by Mathlib
`Scheme.Hom.closePoints_subset_preimage_closedPoints` and the source library
`Scheme.Hom.isIso_residueFieldMap`; it uses no new geometric hole. The new
`zlCanonicalImmersionPunctualSpectrum` proves the residue-cardinality and
nonzero-eigenvector assembly from a separate normalized stalk-comparison result.

Two geometric comparison results are separated into their own modules. They are
weight independent parts of the original restriction argument: finite-model
Frobenius conjugacy for the actual canonical pullback, and compatibility of that
pullback with the actual normalized Weil cohomology. Each has its source,
complete proof in words, edge-case checks, and its own DAG node. They neither
assume nor conclude the assigned weight-preservation theorem. The main proof
combines them with the existing exactness theorem through explicit filtration
and degreewise arguments.

## Proved and sorry left

Closed: `WeilConjectures.zlImmersionPullbackWeightPreservation` (the single
original hole). Its module now has zero holes. This delivery is a decomposition,
not a net decrease of holes.

Also proved: `WeilConjectures.zlCanonicalImmersionPunctualSpectrum`, including
preservation of residue cardinality, nonvanishing of the mapped eigenvector,
and construction of the finite-presentation witness for the input eigenvalue.
The private isomorphism-invariance helpers in the main module are proved.

Added holes, exactly two:

- `WeilConjectures.zlCanonicalImmersionStalkConjugacy`, node
  `lem-zl-canonical-immersion-stalk-conjugacy`.
- `WeilConjectures.zlCanonicalImmersionCohomology`, node
  `lem-zl-canonical-immersion-cohomology`.

No hole occurs in a definition, private declaration, or an inner proof. These
results only provide propositions and isomorphisms consumed inside theorem
proofs; they define no arbitrary data. Identity immersions, empty sources,
zero stalks, quotients killed by restriction, repeated filtration terms,
length-zero filtrations, and negative cohomological degrees satisfy the stated
arguments. The stalk lemma is imposed only at closed source points with the
closed image required by its local operators.

## No longer needed

Removed the main module's direct proof imports
`Sheaf.Paper.ZlImmersionWeilLocalBehavior`,
`Sheaf.Paper.LocalFrobeniusTrace`,
`Sheaf.Paper.IntegralPullbackComposition`, and
`Sheaf.SixFunctors.FrobeniusPointTransportNatural`.
The last three were only needed for the lower normalized comparison arguments;
the main argument operates directly on the finite-presentation definition.
The first package also ties the coefficient universe to the scheme universe,
whereas the assigned statement has independent universes.

The main node now depends on the spectrum and cohomology comparison nodes and
`lem-zl-weil-heart-localization-exact`, together with the existing weight
definitions. Its former direct proof dependencies on
`lem-zl-immersion-weil-local-behavior`, `def-weil-local-frobenius-trace`,
`lem-pod-integral-pullback-composition`, and
`lem-weil-frobenius-point-transport-natural` have moved to the appropriate lower
comparison nodes. The spectrum module also removes
`Sheaf.Paper.ImmersionWeilPullbackLocalBehavior`: its only use was
`immersionWeil_closed_point`, now replaced by proved existing results.
No global deletion or withdrawal is claimed: these modules
remain needed transitively or by other consumers. No unit route is bypassed.
No source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

The local-behavior package is not immediately an interface for the assigned
canonical operations. Its coefficient datum has `Qbar : Type u`, while the
assigned theorem has `Qbar : Type v`. Its supplied equivariance is normalized
using the finite local composition comparison; the assigned operation uses
`zlFrobeniusSquare`, built from `zlPullComp`. These must be identified rather
than treating an arbitrary supplied square as definitionally equal. The existing
stage-2 review already flags this issue.

Likewise the package's cohomology is built from its supplied
`ConstructiblePullbackComparison.commShift`. The weight predicate uses
`sfWeilCohomologyFrobenius` and its representative-normalized
`fieldCommonWeilFrobeniusShift`. Merely forgetting the Weil structures, or using
an unconstrained cohomology isomorphism, would not prove the assigned theorem.
The separated cohomology statement explicitly concerns the prescribed functors.

The retained new-node records used `mathlib_search` instead of the required
`mathlib_searches`. This attempt corrects that field and records a fresh LeanSearch
query, completing all three required kinds of search. The original rework quarantine
file is now absent; the restored live module still has the original signature and
single hole, which this packet preserves and proves.

The current blueprint places the open--closed argument in
`sk-prop-wgen-relative-line/det-l-dl-general-excision.proof.md`; the old unit route
and the parent statement are retained. The new statements expand only its
restriction/cohomology justification.

## New nodes

`lem-zl-canonical-immersion-stalk-conjugacy` records the finite-stage
Frobenius-intertwining stalk isomorphism for `zlFrobeniusSquare`, including
comparison with any finite Weil presentation of the output. It has no purity,
mixedness, embedding, or weight assumption or conclusion.

`lem-zl-canonical-immersion-cohomology` records the Weil-heart isomorphism
between canonical inverse image and `sfWeilCohomology` in every integer degree.
It has no weight predicate. Its proof must retain the prescribed signed shifts.

`lem-zl-canonical-immersion-punctual-spectrum` is proved by the closed-point
residue-map lemma and the stalk-conjugacy node. It records the residue-cardinality
and elementary eigenvector steps separately from the geometric comparison.

No existing definition or theorem signature is changed, so no change record or
consumer adaptation is needed.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
