## Worker report

The module states `AlgebraicGeometry.admissibleModificationCohomologyPresentation`.
Its conclusion is a nonempty package of the specified data, uniformly in the input
sheaf. The sole postponed theorem is this existence theorem; every helper
definition has actual data and every structure describes data and its laws.
No change to the informal statement or proof is requested. The statement dependency list gains the new coefficient-data definition node, which cites the new limit-site definition node.

Hypotheses and clauses:

- A commutative ring and henselian pair are `{A : Type u} [CommRing A]`,
  `(I : Ideal A) [HenselianRing A I]`; finite generation is `hI : I.FG`.
- `U` is an open of `Spec A`, with `hU` specifying membership as the complement
  of `PrimeSpectrum.zeroLocus I`. Binding this open with its defining equality
  avoids introducing another open-complement convention.
- `AdicCompletion I A`, its algebra map, `admissibleCompletionBase`,
  `admissibleCompletionIdeal`, `admissibleCompletionOpen` and
  `admissibleCompletionOpenMap` give the completion, extended ideal, inverse-image
  open and its canonical map. `admissibleClosedFibres` is the actual pullback
  diagram over `Spec (A / I)` using `Over.pullback`.
- `AdmissibleCentre` consists exactly of finitely generated ideals with the same
  zero locus as I. `AdmissibleModification` is their induced category in
  `Over (Spec A)`. It retains isomorphic blowups rather than taking a skeleton;
  this is an equivalent presentation. `AdmissibleToposPresentation.cofiltered`
  and `.thin` assert cofilteredness and uniqueness of domination morphisms.
- `AdmissibleOpenEmbeddings` supplies the common open embeddings into the actual
  affine blowups, cartesian over U, with compatibility under domination.
- `AdmissibleLimitSite` uses a single site functor for each projection, for both
  set and abelian coefficients. Its exact inverse image is the sheafified Kan
  extension. `AdmissibleToposPresentation.isLimit` states existence of cone lifts
  and unique lifting of compatible transformations, the two-dimensional limit
  property. `conservative` says that the compatible geometric points detect
  isomorphisms; `IsGeometricPoint` identifies each projection with a geometric
  small-etale point, using the canonical universe lift.
- `admissibleCoefficientFunctor` is precisely
  `p_J^{-1} i_J^{-1} (R^q j_{J*})`. Its transition is
  `admissibleCoefficientTransition`, constructed from the canonical derived
  exchange and pullback-pasting comparisons, not an arbitrary morphism.
  `AdmissibleSpectralPresentation.diagram`, `.finiteStage`, and `.transition`
  specify this diagram; `.coefficient` and `.coefficientIsColimit` give its
  colimit in functors of F. Evaluation therefore gives exactly L_F^q.
- `spectralSequence` is a functor to the existing first-quadrant natural-indexed
  E2 cohomological spectral-sequence category. `pageTwo` gives its E2 terms as
  right derived global sections on the presenting site of the coefficient
  colimit. `pageTwo_naturality` specifies naturality in F.
- For every F and `hF : F.IsTorsion`, `abutment` is the existing
  `SpectralSequence.Abutment` of `Etale.cohomology` applied to `singleFunctor 0 F`.
  This structure includes F^0 = top, F^{n+1} = bottom, decreasingness and the
  n+1 graded-piece isomorphisms. `gradedIso` records the chosen identifications.
- `AdmissibleCompletionComparison.extensionCentre` fixes the extension functor
  on ideals; `cofinal` asserts finality in the opposite, filtered direction.
  `blowupSquare`, `fibreIso`, `fibreSquare`, `fibreNaturality`, `openSquare` and
  `siteComparison` specify the corresponding completed blowups and their
  closed-fibre identifications and projections. Both original and completed
  topos presentations use the same site, expressing their identification.
- `comparison.coefficientMap` is the finite-stage completion exchange.
  `coefficientExchange_normalization` characterizes its map on colimits on each
  cocone leg. `spectralSequenceMap` is natural in F, and `pageTwo_commutes`
  identifies its E2 map with the map induced on H^p by coefficient exchange.
- `filteredPullback` uses `admissibleCohomologyPullback` as its abutment map.
  This helper is the derived adjunction-unit map followed by homology, with the
  canonical composition and single-functor comparisons. The
  `AdmissibleFilteredAbutmentMap` fields specify the maps on filtration steps,
  their compatibility with inclusions, and that their induced quotient maps
  agree with the stable spectral-sequence page map. `filtration_naturality`
  also records this for a morphism of torsion input sheaves.
- Neither the coefficient exchange nor the abutment pullback is required to be
  an isomorphism.

Dependency interfaces used: `HenselianRing` from
`WeilConjectures.Mathlib.RingTheory.Henselian`; `AdicCompletion` and its algebra
structure from Mathlib's AdicCompletion modules; `AlgebraicGeometry.Spec` and
`Spec.map` from `Mathlib.AlgebraicGeometry.Scheme`; scheme base change via
`Over.pullback` as recorded by `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`;
`Sheaf` and `Sheaf.IsTorsion` from
`WeilConjectures.AlgebraicGeometry.EtaleSheaves`; `Etale.upperStar`,
`Etale.lowerStar` and their canonical adjunction and composition comparisons from
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`;
`AffineBlowup` and `.toSpec` from `WeilConjectures.Blowup.Affine.Defs`;
`CategoryTheory.SpectralSequence` from Mathlib and its `Abutment` convention from
`WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic`;
`Etale.cohomology` from the existing derived global-sections interface.
The canonical derived exchange uses
`WeilConjectures.SixFunctors.BaseChange.Derived`; the geometric morphism and
geometric point constructions use the existing site and small-etale point
interfaces. No dependency declaration is privately copied.

Edge cases checked: I = 0 gives an empty complementary open; nilpotent I also
has empty U. The blowup index remains nonempty (I itself is an allowed centre),
and the statements permit empty closed fibres and zero sheaves. The zero ring
and degree zero require no nontriviality assumptions. In degree n = 0 the
filtration has exactly one possible graded piece. No noetherian, excellence,
locality, nonempty-open, fixed exponent, or prime-invertibility hypothesis is
added. Completion is not assumed injective or flat. The sheaf on U' is always
its inverse image; no arbitrary second sheaf is substituted.

Source checked directly with pdftotext: ILO XX 4.4, printed pp.373–374 (PDF
pp.379–380): full-support ideals, the domination preorder, finite-stage (**), its
limit, morphism of limit spectral sequences, and the final Note. The proof
outline in the theorem docstring follows the node's seven proof steps; the
stage-2 proof is `sorry` as required.

Searches: msearch LeanFinder with “Admissible blowups of a henselian pair give an
inverse limit etale topos and a natural spectral sequence for torsion sheaf
cohomology” returned eight unrelated completion/etale-algebra hits; no matching
statement. Loogle with “CategoryTheory.SpectralSequence,
AlgebraicGeometry.AffineBlowup” returned no hits (unknown AffineBlowup).
Mathlib grep with “admissible.*blow|Zariski.?Riemann|ToposLimit” in
AlgebraicGeometry returned no hits. LeanSearch with “Limit etale topos of
admissible blowups spectral sequence for cohomology of open complement” returned
eight unrelated small-etale/limit hits. Project rg searches in WeilConjectures
and Sheaf found the affine blowup, spectral-sequence, inverse-image and derived
exchange infrastructure used here, but no declaration of this item. The literal
item id search in WeilConjectures found no existing theorem. The recorded
statement dependencies and their full interfaces were read before reuse.

## Second reading by Q117

A second reading against the node found and corrected these draft mismatches:
F' must be the pullback sheaf on the completed open; U must be the complement of
V(I); henselianity and finite generation must be hypotheses; the coefficient
terms must be actual colimits with canonical exchange transitions; the E2 and
filtration maps must be characterized rather than arbitrary maps. The final
package states all these clauses and keeps the common presenting site explicit.
The dispatcher forbids starting another agent, so this is a separate rereading
by the same worker; the maintainer's independent review remains required.

## New nodes

`def-per-admissible-modification-coefficient-data` defines the full-support centre
category, closed-fibre diagram, continuous projection-site data and their
coherence and limit universal-property predicates, compatible geometric-point
predicate, canonical higher-direct-image exchange, finite-stage coefficient
functors and transitions, canonical cohomology pullback, and completion maps.
Its own module is `Sheaf.AlgebraicGeometry.AdmissibleModificationCoefficientData`.
It makes no existence assertion; the item's theorem supplies the presentation.
This is a missing definition interface needed by the item's statement, grounded
in ILO XX 4.4, printed pp.373–374. The definitions are separated into their own
module so each file compiles within the prescribed per-file limit.

The additional LeanFinder query “Site projections and canonical exchange
coefficient diagrams for the limit etale topos of closed fibres of admissible
blowups” returned eight scheme-limit helpers, not these data. LeanSearch with
“Canonical coefficient diagram of higher direct images on admissible blowups
pulled back to their limit etale topos” likewise returned scheme-limit and
small-etale site components. Mathlib grep for
`AdmissibleLimitSite|admissibleCoefficientTransition|admissible.*coefficient`
returned zero. Exact rg of the proposed names in WeilConjectures and Sheaf
returned no existing declarations. The DAG and `tools/blueprint_refs.py search
admissible` show no existing definition of these projection/coefficient data;
the unsplit existence lemmas for the geometric system and its topos limit are
not replaced by this definition. The new node reuses their standard component
constructions and is cited in the item's statement dependencies. The rereading
above also covered this definition module: every definition has real data and
no helper existence theorem has been silently assumed.

`def-per-admissible-modification-limit-site-data` owns the full-support centre
category, actual closed-fibre diagram and projection-site data, their coherent
cone, the two-dimensional limit predicate and compatible geometric-point
predicate. Its module is
`Sheaf.AlgebraicGeometry.AdmissibleModificationLimitSiteData`. The coefficient
node imports and cites this definition and owns the canonical exchange and
completion constructions. Both nodes use the searches listed above: no existing
DAG definition or Mathlib/project declaration supplies these data types, while
the component constructions are reused. They are grounded in the same source,
ILO XX 4.4, and their data definitions were reread together with the theorem.
The split between these two definition modules keeps the canonical site and
coefficient constructions independently compilable within the 60-second limit.

Validation: the final three modules compile independently in dependency order
through scompile.py, with no errors or warnings. The 2026-10-24 deliver2.py
--no-push run passed preflight and compilation (dry-run commit 38ba231093c).
The only sorry is the requested stage-2 theorem. No local or global library
build was run, and all source changes are confined to this sandbox.
