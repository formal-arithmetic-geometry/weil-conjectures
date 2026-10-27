## Worker report

The module `Sheaf.SecSmoothPurity.NestedAffineOrientation` states
`WeilConjectures.PurityFiniteSetting.NestedAffine.nested_affine_orientation`.
Its conclusion is the explicit proposition `Statement`, and all new theorem
proofs are `sorry`. The helper definitions have real data. No statement correction,
dependency repair, new notion node, or disputed mathematical statement is proposed.

The equations use the canonical ordinary-etale presentation of the ordinary
constant-coefficient pro-etale categories, as do the recorded finite etale
normalization and Cartesian-tower tensor-comparison interfaces. Exact finite site
comparison and its specified tensor, pullback, unit and exceptional comparisons
transport these equations to the actual pro-etale categories. This is not a
replacement by arbitrary maps or arbitrary endpoint isomorphisms.

Hypotheses and objects, clause by clause:

- `P : PurityFiniteSetting.{u}` supplies the algebraic closure of a finite field,
  the prime ell different from the characteristic, the positive level, and the
  actual finite coefficient quotient. `_hE : P.extension = ⊥` specializes the
  finite-stage coefficient convention to E=Q_ell, hence the Z/ell^r stage (with
  its existing universe lift). This is the same specialization used by
  `diagonalOrientationCharts`. No larger coefficient extension is silently used.
- `d e : ℕ` includes both zero dimensions. The instances on f and g assert
  separatedness, locally finite type, quasi-compactness, and smooth pure relative
  dimensions d and e. `aZ` is a separated finite-type structure morphism to k.
  The corresponding X- and Y-structure maps are f g aZ and g aZ, so these
  schemes are also separated finite type over k. This packages exactly the
  separated finite-type k-scheme domain of the node.
- `S : Z.Opens`, `V : Y.Opens`, `U : X.Opens` and their `IsAffine` instances
  are the three affine opens. `hV : V ≤ g ⁻¹ᵁ S` and
  `hU : U ≤ f ⁻¹ᵁ V` are the two nesting conditions. The local maps are the
  canonical `g.resLE S V hV` and `f.resLE V U hU`, not supplied unrelated maps.
- `v` and `u` have exactly the two Mathlib affine-space targets, with `Etale`
  instances. They are automatically separated and of finite presentation:
  their sources and targets are affine, and these finite-type field schemes
  are Noetherian. The two equations `hv`, `hu` assert that their projections
  are the restricted maps. The canonical `affineTraceAffineSpaceIso` merely
  reads these same coordinates in the ordered affine-line tower.
- `vt`, `ut`, and `k := ut ≫ affineTraceMap vt d` are respectively v, u and
  bu in these tower coordinates. `chartComposite` asserts the required
  equality with `h0 := fU ≫ gV`. Its proof docstring uses precisely the
  Cartesian affine projection square and the two chart equations. No
  Cartesian hypothesis is made on the composite outer chart square.
- The finite-type and Noetherian instances and all compactifications are
  derived internally; none is an extra hypothesis.

Arrows and conclusions, clause by clause:

- `orientation P m w aY` is the inverse of the specified diagonal orientation's
  ordinary presentation, `P.chartOrdinaryOrientation`. That existing definition
  selects the uniquely normalized ordinary representative of the actual
  pro-etale diagonal orientation. It does not choose an arbitrary orientation.
- `twistPull` is the recorded shifted Tate coefficient pullback.
  `source` concatenates the ordered powers using `compositionEtalePowerAdd`,
  applies the specified symmetry, and then inverse Tate pullback. Thus its
  source is L_(d+e) and its target is f*L_e tensor L_d, including the even shifts.
- `gammaUnit` is `diagonalAffineMate` using the canonical projective-line
  trace transport and normalized projective-line trace data. `gamma` is
  `DiagonalAffineTrace.ordinaryTranspose`, the actual coefficient-first
  ordered integration transpose for every H. Neither is defined using the
  diagonal orientation or the desired equality.
- `total` transports gamma_(d+e),R along the coordinate flattening `blockEq`.
  `blockProjection` identifies its projection with q p. These helper theorems
  assert coordinate/projection identities and have complete inductive proof
  docstrings. The chosen equality proof changes parentheses and retains the
  coordinate order. Its rank-zero map is the canonical identity comparison.
- `iterated` is source reassociation, the tensor of q*gamma_p,R with identity
  on L_d, gamma_q,G_p R, and the inverse of the actual adjunction-normalized
  `finiteExceptionalComposition`. This is exactly the second displayed affine
  route, expressed before the common exceptional compositor.
- `tensorRoute` is source reassociation, f*a_g tensor a_f, and the actual
  counit-defined `smoothPurityEtaleTheta` at omega_g. It is not an arbitrary
  purity-map family.
- `r` is the normalized open restriction from omega_h to omega_h0. It first
  changes the coefficient unit using `chartDualizingUnit`, uses the recorded
  `DualizingLocality.restriction` for the compatible open square, and changes
  back. This restriction requires a commutative square, not a Cartesian one.
- `lhs` is j*a_h, with canonical Tate source restriction and r. `rhs` is
  j*(c_R^{-1} t_f,omega_g(f*a_g tensor a_f)) with those exact same comparisons.
  The canonical compositor is cancelled on both sides to put both arrows
  in omega_h0. Applying that same compositor back recovers precisely the
  targets c_R a_h and t_f,omega_g(...) in the node's two displayed formulas.
- `chartPull` pulls either affine arrow along k and uses the specified
  source-etale locality and the equality `wk`. Consequently `lhs = aff`
  renders the first displayed formula and `rhs = it` renders the second.
  The next conjunct `total = iterated` states the equality of the affine
  right sides for these arbitrary d,e. `aff = it` records its chart pullback;
  `lhs = rhs` records the requested equality of the restricted arrows.
- `NormalizedInputs` explicitly states a_p=Gamma_p,R for every affine base
  and every rank; G_p R is constructible finite-Tor; and for every
  constructible finite-Tor H the actual twisted pullback and exceptional
  output are constructible finite-Tor. It states Gamma_p,H=theta(1 tensor
  Gamma_p,R). Since G_pe R satisfies the stated predicate, that input is
  included without a flatness assumption on G_pe R.
- The same predicate gives Gamma_0,H=identity_H after `zeroSource` and the
  canonical identity exceptional and pullback comparisons, for every such H.
  It also gives the explicit coefficient-unit rank-zero normalization.
  `zeroSource` consists only of the identity-pullback map, unit comparison,
  and tensor right unitor. Ordered Tate concatenation is assembled with these
  unit constraints in rank zero; it introduces no extra comparison for an
  empty block.
- The last conjunct is the literal equality
  `(-1 : ℤ) ^ ((2 * d) * (2 * e)) = 1`.
  The two further ctf conjuncts retain omega_g and f*omega_g in the domain
  of the global restricted tensor route.

Dependency declarations used include:

- `Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates`:
  `NestedAffineCoordinates.chartOrdinaryOrientation`, its uniquely normalized
  ordinary presentation; `NestedAffineCoordinates.chartDualizingUnit`;
  `NestedAffineCoordinates.chartTraceProjection_smooth`;
  `NestedAffineCoordinates.compositionEtalePowerAdd`, with the re-exported
  `compositionEtalePowerAssembly`, `compositionEtalePowerZero`, and
  `compositionEtalePowerSuccessor`.
- `Sheaf.Paper.PurityDiagonalDualizingData`: `diagonalTwistEtale`,
  `diagonalOrdinaryDualizing`, `diagonalAffineMate`,
  `diagonalEtaleLocality`, `diagonalDualizingCongr`.
- `Sheaf.Paper.DiagonalAffineTraceCoordinates`:
  `DiagonalAffineTrace.ordinaryTranspose` and `OrdinarySource`.
- `Sheaf.Paper.PurityFiniteExceptionalComposition`:
  `finiteExceptionalComposition`, the conjugate of the specified lower-shriek
  compositor.
- `Sheaf.Paper.SmoothPurityMap`: `smoothPurityEtaleTheta`,
  `smoothPurityUnitIso` and its finite tensor/pullback conventions.
- `Sheaf.Paper.DualizingSigmaCocycleLocality`:
  `AlgebraicGeometry.ProEtale.DualizingLocality.restriction`.
- Mathlib and the recorded affine-tower module supply affine spaces,
  `resLE`, the ordered coordinate isomorphism, projections, maps,
  Noetherianity, derived tensor hom and its symmetry/unitors.

The owning landed nodes of the additional helper interfaces are added to
stmt_deps: `def-sp-nested-affine-orientation-coordinates`,
`def-pur-diagonal-affine-trace-coordinates`,
`def-pur-finite-exceptional-composition`, and
`def-pur-diagonal-dualizing-data`. Traversal of their statement/proof
closures found no path to the item. Existing proof-dependency modules are
imported, including the ordered-adjoint regrouping and affine composition
interfaces; `det-sp-purity-bc-factors` currently has no recorded module.

Edge cases checked: d=0; e=0; both zero; r=1; empty opens and empty source;
nonflat ctf input G_pe R; non-Cartesian outer chart square. Naturals retain
all dimensions, rank-zero Gamma is given by actual identity constraints,
and no nonempty chart, positive dimension, or flatness assumption is added.

Searches for an exact existing statement:

- msearch leanfinder: "For nested etale affine charts of smooth morphisms
  diagonal orientations equal ordered affine integration composites" returned
  eight unrelated affine/diagonal declarations, no match.
- msearch loogle: "AlgebraicGeometry.ProEtale.derivedTensor,
  AlgebraicGeometry.AffineSpace" returned zero hits; the first identifier was
  unknown to that index.
- msearch grep: "nested.*orientation|orientation.*nested|affine.*integration"
  in AlgebraicGeometry returned zero hits.
- msearch leansearch: "smooth purity composition nested affine charts ordered
  integration" returned eight unrelated manifold and standard-smooth results.
- Local rg in Mathlib, WeilConjectures and Sheaf, and the item-id search in
  WeilConjectures, found the component canonical constructions but no theorem
  with these two nested-chart equalities. The model-orientation equation is
  a different beta/delta expression; it was not substituted for this statement.

Original-delivery validation: scompile compiled both the sandbox and library module cleanly
(17.2 s and 13.1 s on the final source before delivery metadata). An earlier
required-import failure in the shared build was repaired upstream during this
session; the same minimal module-mode import subsequently compiled. No live
source or launcher script was edited, and no local/global lake build was run.

## Second reading by NK

Self-contained second reading by the dispatcher-started worker, following the
explicit instruction not to start another agent. I reopened the node, its
seven-step proof and the latest blueprint proof (1), and checked the final
module from hypotheses through the expanded `Statement`.

The early draft did not express the two arrow equalities and was discarded,
not delivered. The final statement uses explicit arrows and actual canonical
transports. In the second reading I checked the direction of the inverse
compositor in `iterated` and `rhs`, and of the two unit conversions in `r`:
both routes end at the same restricted omega_h0. I added the arbitrary-H
rank-zero identity, rather than only the unit case, and explicitly retained
ctf for omega_g and f*omega_g. The final normalization is not tautological:
Gamma is constructed from integration independently of the orientation.

No remaining mismatch, node fault, or STATEMENT-DISPUTED issue was found.


## Repair of return 84288e793d21

H2 is repaired by the new definition node
`def-sp-nested-affine-orientation-coordinates`. Its own module is publicly
imported by `NestedAffineOrientation`. The item now cites this definition
instead of `lem-pur-diagonal-dnc-chart-normalization` and
`thm-pur-composition-coherence`, precisely the two additions whose removal the
return authorizes. The implementation modules are imported by the definition
interface to re-export their constructions, not to assume either theorem's
conclusion. All seven aliases are listed in the definition node's
`lean.declarations`. The item uses the new qualified aliases at all five call
sites: ordered concatenation, inverse orientation, affine smoothness evidence,
and both coefficient-unit conversions. The accepted theorem signature and its
`Statement` clauses are unchanged. No statement correction is needed.

## New nodes

`def-sp-nested-affine-orientation-coordinates` owns the transparent re-export
interface in `Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates`.
Its source is the latest composition-factors proof (1), which uses the
specified diagonal orientation and ordered shifted Tate concatenation.
`chartOrdinaryOrientation` retains every original finite-type, separatedness,
smooth-rank and structure-map binder and returns the exact original choice of
the normalized ordinary representative from
`PurityDiagonalDualizingObject.existsUnique_diagonalDualizingObject`.
`chartDualizingUnit` retains its compactification binder and canonical unit
conversion. `chartTraceProjection_smooth` delegates the existing named
smoothness proof for every base and natural rank; no proof is postponed here.
`compositionEtalePowerAssembly` retains all coefficient-category hypotheses
and the actual zero/successor input isomorphisms, and is the original recursive
assembly with its unit and associator constraints.
`compositionEtalePowerZero`, `compositionEtalePowerSuccessor`, and
`compositionEtalePowerAdd` retain all coefficient-ring, annihilator, scheme,
and rank binders and literally delegate the published constructions.
All universes are explicit; `autoImplicit` is false. These are public aliases,
not private copies or new arbitrary choices.

New-node searches: LeanFinder with "ordinary diagonal dualizing orientation
and ordered shifted Tate tensor powers" returned eight unrelated group-action,
representation, shift-sign and tensor-power results. LeanSearch with
"canonical etale diagonal orientation normalized unit ordered Tate powers
addition" returned eight unrelated power-series, unit, torus and etale
results. The msearch grep for the exact helper families returned zero hits.
Local rg found no exact helper in Mathlib or WeilConjectures, and located the
published Sheaf helpers now re-exported. Exact declaration-owner searches in
the DAG found no node recording assembly, zero, successor or the smoothness
helper; blueprint_refs found zero nodes for "ordinary diagonal orientation
ordered Tate powers". The raw outputs are in the new node's mathlib_searches.
The related model-orientation coordinate node uses some of these helpers but
does not own/re-export this seven-declaration interface. No construction was
reimplemented. The new node cites the actual unique diagonal-orientation
existence result, alongside the underlying definition nodes, rather than the
two unused comparison/coherence theorem statements.

Repair second reading by NK: I compared the aliases against the full published
signatures and bodies, and checked each main-file replacement. Unfolding each
alias gives exactly the pre-return expression, including proof irrelevance for
the smoothness evidence; the node's `lean.statement` is the file's signature
verbatim. The zero and successor identifications remain those of the original
ordered powers, so d=0, e=0 and both-zero cases retain their original tensor
unit constraints. Empty bases, the nonflat exceptional input and the
non-Cartesian outer square are unaffected. No new sorry, hypothesis, theorem
clause, or STATEMENT-DISPUTED issue is introduced.


Repair validation: scompile.py compiled both delivered modules against the live
published build. The library compile took 5.5 seconds for the coordinate
interface and 14.4 seconds for NestedAffineOrientation, with no unexpected
warnings or errors. The corresponding sandbox compilations also passed.
