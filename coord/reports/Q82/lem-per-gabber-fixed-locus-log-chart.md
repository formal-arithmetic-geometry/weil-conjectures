## Worker report

The module `Sheaf.AlgebraicGeometry.GabberFixedLocusLogChart` states
`AlgebraicGeometry.GabberFixedLocus.exists_fixed_locus_log_chart`. Its sole postponed
proof is `sorry`; every auxiliary definition has actual data. The auxiliary structures
package the explicit coordinates and canonical maps of this statement, not extra
hypotheses. No dependency interfaces or natural-language statement were changed.
The item gains the four existing definition dependencies for strict normal crossings,
ordinary normal crossings, the global Rees blowup, and scheme-theoretic strict transform.

The source was read in the local ILO PDF, Expose X, printed pp.136--146, including
Proposition 1.2, the reductions and diagram (1.b) of 1.3, Lemmas 1.5--1.6,
and the Claim and Ui/Vi calculations of 1.7. In particular the boundary after
blowing up is the exceptional divisor UNION the strict transform. The displayed
fixed ring is the coordinate ring of the fixed subscheme, never the invariant ring.

Clause correspondence:

- Noetherian fs log schemes: `X S : FineSaturatedLogScheme.{u}` with the two
  `IsNoetherian` instances. The original recorded fs structure and morphisms are used.
- Log regular pairs and their divisorial log structures: `_hX`, `_hS`, `_hXZ`, `_hSD`.
  `IsDivisorial` says the structural map is injective on every etale object with image
  exactly `divisorialSections` for the complement of the indicated boundary.
- X regular: `_hregular : IsRegularScheme X.scheme`.
- Strict normal crossings: `_hZ : IsStrictNormalCrossingsBoundary Z` supplies regular
  global components and regular expected-codimension intersections; `_hZn` supplies
  the stated local product of distinct regular parameters. These are the two
  explicitly specified parts of the node's normal-crossings convention.
- Log smooth morphism: `f : EtaleLogHom X S` and `_hf : f.IsLogSmooth`.
- Finite group, over the trivial base action: `G`, `[Group G]`, `[Finite G]`,
  `a : G →* Aut X.scheme`, `_hover`; `_hpreserve` expresses action on the pair.
  Because the log structure is divisorial this also determines the log action.
- G-strictness: `_hstrict : IsGroupStrict a Z` tests each irreducible component of
  the boundary subspace; every translate is equal or disjoint.
- Tameness: `_htame` tests the cardinality of the stabilizer of EVERY geometric
  point, as an invertible element of its ordinary local ring. It does not replace
  the hypothesis by invertibility of the entire group everywhere.
- Chosen geometric point and replacement by inertia: `Ω`, `Field`, `IsAlgClosed`,
  `x`, `_hinertia`. Thus G already IS its inertia group at this point. The
  chosen subgroup is `H : Subgroup G`, including trivial and full subgroups.
- Coefficients: positive `N`, `Λ`, the algebra over `CyclotomicRing N ℤ ℚ`, and
  `IsLocalization M Λ` with `(N : CyclotomicRing ...) ∈ M` give exactly a
  localization of Z[1/N,mu_N]. `∀ g, g^N=1` is the annihilating-exponent condition.
- Sharp fs base chart: `Q`, its monoid instance, `IsFineSaturatedMonoid Q`,
  the condition that every unit is 1; `LocalChart.base_isChart` and
  `sharp_at_point` make it a sharp chart at the actual image point.
- The local boundary monoid is the actual `ToricMonoid t r = Multiplicative
  ((Fin t → ℤ) × (Fin r → ℕ))`. `ModelRing` is polynomial over its monoid algebra,
  hence exactly Λ[u_j^{±1},z_j,y_j]. `γ` and `groupMap` use canonical completion;
  injectivity, finiteness of the torsion quotient, and invertible torsion order are
  explicit conjuncts.
- Etale localization of both source and base and the chosen point are `c.V`, `c.W`,
  `c.point`, `point_over`, `toBase`, and `over`. The sourceAction fixes the lifted
  point and is equivariant over a; it acts trivially over c.W.
- The comparison is the canonical `pullback.lift` of `toBase` and `toModel`, with
  the commuting square prescribed by gamma. `Etale c.comparison` is required.
  `baseChart`, `sourceChart`, `source_isChart`, `source_alpha`, and `compatibility`
  express strict compatible charts, through their actual images in functions.
  The source monoid is ULift of the finite-rank monoid only to meet the recorded
  IsChart universe; no sizes of sites or schemes are equated or restricted.
- Model equivariance and action over Sigma are `equivariant` and `model_over`.
  `coefficient_fixed`, `units_fixed`, `character`, `eigenvectors`, and `linear`
  respectively say inertia fixes Λ and the u-coordinates, acts diagonally on z,
  and preserves the span of the finite polynomial y-basis.
- Adaptation to H: `m ≤ r`, `n ≤ s`, and the `IsFixedSubscheme` clause for
  `(center ...).subschemeι` give exactly the ideal (z_j for j<m, y_j for j<n).
  The same universal-property condition for `c.sourceAction` identifies the
  pulled-back centre with the actual fixed subscheme on the etale source.
- Boundary pullback: `Z.comap c.V.hom = (boundary ...).comap c.toModel`.
- Trivial action: no blowup assertion is invoked unless `0 < m+n`. If H acts
  trivially, the equalizer ideal is zero, hence m=n=0 in the nonzero local model;
  the source point rules out the zero coefficient ring. This is the omitted
  operation required by the statement.
- The model base-change assertion is the first `BlowupComparison`, for the actual
  projection from `S_local ×_Sigma Y`. The second is for `c.toModel`, and so gives
  the same assertion after the strict etale comparison. `BlowupComparison` uses
  an `IsPullback` square with the canonical structure maps, and equality of
  embedded strict-transform ideals after pullback. These are precisely the
  two displayed scheme isomorphisms, with more explicit embeddings.
- Blowup means the recorded `IdealSheafData.blowup`, built by gluing affine Rees
  Proj constructions. `strictIdeal` is the kernel of the recorded
  `strictTransformMap`, hence scheme-theoretic closure away from the centre.
- Ui charts are `BlowupCharts.zChart`, with open immersion, map `zSubstitution`,
  exceptional equation z_i and the product of all other strict boundary equations.
  Its ring retains t invertible, r boundary, and s polynomial coordinates.
- Vi charts are `yChart`; its ring has t invertible coordinates, r+1 boundary
  coordinates, and polynomial indices `{j : Fin s // j ≠ i}`. `ySubstitution`
  sends killed z_j to exceptional*y'_j and each killed y_j (other than i) to
  exceptional*y'_j; y_i itself goes to the exceptional coordinate. Other variables
  are fixed. `y_exceptional` and `y_strict` specify both parts of the new boundary.
- `beta` and `delta` implement exactly e_j -> e_j+e_i and e_j -> e_j+e_{r+1},
  respectively, on the stated initial blocks and fix the other basis vectors.
  `BlowupCharts.BaseMaps` explicitly identifies the maps to Sigma with beta*gamma
  and delta*gamma. The union boundary is their product, so its log monoid is
  N^r on Ui and N^(r+1) on Vi, together with the unchanged Z^t unit factor.
- `BlowupCharts.covers` says these two families jointly cover the blowup.

Dependencies read and used: `FineSaturatedLogScheme`, `EtaleLogStructure.IsChart`,
`FineSaturatedLogScheme.IsLogRegular`, and `EtaleLogHom` from
`Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`; `EtaleLogHom.IsLogSmooth` and its
FSLogChart/comparison definitions from `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`;
`IsStrictNormalCrossingsBoundary`, `IdealSheafData.IsNormalCrossingsDivisor` from
their matching modules; `IdealSheafData.blowup`, `blowupMap` from
`WeilConjectures.Blowup.Gluing`; `strictTransformMap` from
`WeilConjectures.Compactification.StrictTransform`; monoid algebras, MvPolynomial,
GrothendieckGroup, CommGroup.torsion, Spec and GammaSpec from the recorded
Mathlib constructions. The already stated proof-input modules
FreeCharacteristicRegularBoundary, FsFaceSharpening, ProjectiveOverLocalFree,
BlowupChartRegularSequencePresentation, and Affine.Defs are imported without public.
The currently unstated proof nodes are not imported; no proofs of them are needed
in this stage-2 interface.

Edge cases checked: trivial G and trivial H; m=n=0 (skip the procedure); m=0
(only Vi charts); n=0 (only Ui charts); r=0 (empty boundary, Vi exceptional boundary);
t=0; s=0; one-generator centre (invertible-centre blowup, with empty strict transform
for a sole boundary generator); empty products equal 1; arbitrary residue
characteristics, subject to precisely the invertibility hypotheses. The empty X has
no geometric point, so the pointwise assertion has no instance there. A test example
is the order-2 sign action on the affine plane with one or both coordinate boundaries:
the origin ideal and both substitution maps agree with the usual two blowup charts.
All universes and variables are explicitly bound.

Searches (raw service records in searches.jsonl): LeanFinder query "tame group action
log smooth regular normal crossings fixed subscheme coordinate blowup charts" returned
8 ordinary smooth/relative-dimension/normalization results, no match. Loogle query
"AlgebraicGeometry.Etale, AlgebraicGeometry.Scheme.IdealSheafData.blowup" gave 0 hits
(the latter identifier was unknown to its index). msearch grep
"fixedLocus|fixedSubscheme|GStrict|IsTame|log.smooth" in AlgebraicGeometry gave 0 hits.
LeanSearch query "equivariant etale local coordinates tame finite group action fixed
subscheme blowup normal crossings" returned 8 generic etale/fixed-field/group-action
results, no match. Direct rg over Mathlib, upstream WeilConjectures and project Sheaf
found no GabberFixedLocus declaration or equivariant fixed-locus chart. Existing
strict-transform, ordinary coordinate-blowup and divisorial log definitions were
opened and reused; the finite-field correspondence FixedScheme interface is a
different notion and was not imported. DAG searches by fixed subscheme, tame/inertia,
strict normal crossings, blowup, and strict transform located the reused nodes.
No STATEMENT-DISPUTED flag or statement correction was required.

## Second reading by Q82

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
