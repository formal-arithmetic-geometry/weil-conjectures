## Worker report

The module `Sheaf.TraceFormula.ValuationExceptionalLocalCriterion` states
`AlgebraicGeometry.valuation_exceptional_local_criterion`, with its sole proof `sorry`.
Two real auxiliary constructions, listed in `lean.declarations`, provide the residue-field
structure on the scheme-theoretic fibre and its canonical inclusion after scalar extension.
Neither construction chooses an arbitrary map or takes a reduction. No statement correction,
new node, or dependency repair is needed. The item gains the already landed definition nodes
`def-trf-semistable-marked-point` and `def-trf-projective-line-tree` in `stmt_deps`.

Source read: Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
https://arxiv.org/pdf/0707.3953v3, Lemma 4.4.2 and proof, printed pp. 30–31;
§1.2 (multipointed and semistable curves), Appendix B (trees and ordinary points), and
Lemma 5.1(i). The PDF was read online; the node already records the outstanding local
archival-copy request. Its six-step proof plan is retained and included in the theorem's
docstring. The target is a split child, not a blueprint unit statement.

### Every hypothesis and clause

- The separably closed field is `(K : Type u) [Field K] [IsSepClosed K]`.
- The actual embedded valuation ring is `(V : ValuationSubring K)`. Its existing definition
  requires membership of each element or its inverse. This also gives the field of fractions
  canonically as K (including the case V = K); no arbitrary embedding or generic-point map
  is assumed. The structure map of the generic point is
  `Spec.map (CommRingCat.ofHom V.subtype)`.
- Finiteness of the chain of primes is `[Finite (PrimeSpectrum V)]`. Linearity of the prime
  ideals is automatic for a valuation ring, so this encodes the whole finite-chain condition.
- T is written explicitly as `Spec (.of V)`. P is the source pair (Y,E), Q is the target
  pair (C,D). Both have the recorded `MultipointedCurve` type, which retains flatness,
  finite presentation (including quasi-compactness and quasi-separatedness), pure relative
  dimensions 1 and 0, the marking closed immersion, and its structural compatibility.
- The smooth generic curve and etale generic marking are `hgenericSmooth` and
  `hgenericEtale`, using the second projections of the canonical generic pullbacks.
- The map is `(q : P.Hom Q)`. Its two maps, their base equations, and their marking square
  are exactly the dependency structure. `hq : q.IsEtaModification ...` is its recorded
  eta-modification predicate: both proper maps, schematically dense isomorphism opens on
  both parts, and isomorphisms on the two generic fibres.
- `(x : Q.X)` is the target point, and s is everywhere the expression `Q.x x`, avoiding
  a redundant independent base point and an equality hypothesis. `hx` says that the point
  `Q.x.asFiber x` is closed in the actual fibre `Q.x.fiber (Q.x x)`.
- Normality is `hnormal`, requiring every stalk of Q.X to be an integrally closed domain.
  It makes no global irreducibility assumption. The project's `IsNormalScheme` bundles
  `IsIntegral` and therefore would impose a stronger hypothesis on disconnected curves;
  it is not used here. No substitute normality predicate is defined.
- Z is precisely `q.curve.fiber x`, the existing residue-field pullback; `hdim` requires
  its topological Krull dimension to equal 1. The empty fibre and zero-dimensional fibres
  are thereby excluded exactly as in the node. No additional purity hypothesis is imposed.
- `hsemi` places every point of Z in the semistable locus by applying the recorded
  `MultipointedPair.IsSemistableAt` to its image under `q.curve.fiberι x`.
- Semistability at x in the left side is the same predicate for `MultipointedPair.ofCurve Q`.
  That predicate means semistability of the marked pair on an open neighbourhood, using
  its pulled-back marking. Its semistability definition includes the scalar-compatible
  ordinary-double-point completed local ring, etale marking, and marking in the smooth
  locus. Thus it uses the already defined open semistable locus, without replacing it by
  a pointwise condition omitting marking neighbourhoods. The node's explanation of this
  locus is explanatory; no unrelated global semistability assumption is added.
- `q.exceptionalFiberScalar x` is Z -> Spec kappa(x) -> Spec kappa(s). Its composite uses
  `q.curve.fiberToSpecResidueField x` and `Spec.map (Q.x.residueFieldMap x)`.
- The geometric Z is the pullback of this actual Z along
  `Spec (AlgebraicClosure (T.residueField s)) -> Spec (T.residueField s)`. Its structure
  map is exactly the `pullback.snd` passed to `IsProjectiveLineTree` in the right side.
- `IsProjectiveLineTree` requires this geometric scheme itself to be reduced and connected,
  nodal with its scalar-compatible completed local rings, and to have projective-line
  components over its specified algebraically closed field. Its finite incidence
  multigraph has one edge per node and one vertex per component: the equation is
  `number of nodes + 1 = number of components`. Loops and parallel nodes are retained.
- `q.exceptionalGeometricFiberι x` is the canonical inclusion into the geometric Y fibre,
  constructed by `pullback.map` from `q.curve.fiberι x`, identity on Spec Omega, and the
  residue-point map to T. The proof fields are only the existing pullback and residue-map
  compatibilities. Its domain is the same geometric Z used in the tree clause.
- The first count is explicitly `(range inclusion ∩ closure ((range inclusion)ᶜ)).encard`,
  with closure and complement taken in the geometric Y fibre. The parentheses fix that
  this is the closure of the complement, as required for the boundary.
- The second count is the intersection of that range with the range of
  `P.markingBaseChange (Orgogozo.geometricPoint T s)`. This is exactly the geometric
  E_s intersection Z. `Set.encard` counts points, including the infinite case, so a finite
  cardinality convention cannot turn an infinite intersection into zero.
- The sum of those two counts is at most 2; the entire conclusion is an iff, with the
  tree and bound conjoined. Both counts occur after the same algebraic closure of kappa(s).
  There is no use of `Z_red`, reduced-induced subschemes, or a set substituted for Z.

### Dependency declarations inspected and used

The declarations and their defining signatures/docstrings were opened before writing:

- `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve`.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `MultipointedCurve.Hom`, `Hom.IsEtaModification`, `Hom.curveBaseChange`,
  `MultipointedCurve.markingBaseChange`, and the companion semistability predicate.
- `Sheaf.AlgebraicGeometry.SemistableMultipointedPair`: `MultipointedPair`,
  `MultipointedPair.ofCurve`, `IsMultipointed`, and `IsSemistable`.
- `Sheaf.TraceFormula.SemistableMarkedPoint`: `MultipointedPair.restrictCurve` and
  `MultipointedPair.IsSemistableAt`.
- `Sheaf.TraceFormula.ProjectiveLineTree`: `curveNodes` and `IsProjectiveLineTree`.
- `Sheaf.Paper.OrgogozoInductionData`: `Orgogozo.geometricPoint`,
  `Orgogozo.IsOrdinaryDoublePoint`, `nodeRing`, and `localScalar`. These retain the
  `AdicCompletion` and `MvPowerSeries (Fin 2)` notions from the original statement deps.
- Mathlib `Field`, `IsSepClosed` (`Mathlib.FieldTheory.IsSepClosed`),
  `ValuationSubring` (`Mathlib.RingTheory.Valuation.ValuationSubring`),
  `Spec` and `Spec.map` (`Mathlib.AlgebraicGeometry.Scheme`),
  `Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`, and `asFiber`
  (`Mathlib.AlgebraicGeometry.Fiber`), and `CategoryTheory.Limits.pullback`.
- Mathlib `Flat`, `LocallyOfFinitePresentation`, `Smooth`, `Etale`, `IsProper`,
  `IsReduced`, `ConnectedSpace`, and `topologicalKrullDim`, in the recorded Mathlib
  modules. Structural clauses are inherited from the recorded multipointed and
  modification interfaces, rather than redefined locally.
- The projective-line object is the existing `AlgebraicGeometry.ProjectiveLine` from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, used inside the tree predicate.
  The recorded `ProjectiveLine.TwistData` in `ProjectiveSpace.TransitionUnits` was also
  read; no twist datum is relevant to the tree criterion.

All already stated proof dependencies are imported nonpublicly, except the multipointed
curve definition already provided by public imports. The three proof-only prerequisites
without Lean records in the node snapshot are `lem-trf-proper-normal-geometric-connectedness`,
`lem-trf-sepclosed-valuation-geometric-components`, and
`lem-trf-valuation-curve-projective-preparation`; they introduce no missing object into
this statement and are not restated. No imports for these unstated proof-only nodes exist.

### Edge cases

Checked empty marking (its range contributes zero), V = K (allowed; a nontrivial
one-dimensional contracted generic fibre is excluded by the eta-isomorphism hypothesis),
disconnected normal target (allowed), arbitrary finite valuation height and positive
characteristic (no DVR, perfection or characteristic-zero restriction), and nonproper or
nonseparated source and target structure maps (allowed; properness belongs to q).
The dimensions exclude the empty fibre. A single projective line has zero nodes and one
component and passes the tree count; a loop or a parallel pair does not. The count allows
one boundary and zero or one marking, or two boundary points and no marking. Nilpotent
structure is retained by every fibre and base change, and can prevent the tree predicate
from holding. Every scheme and field is in the common `u` universe, with no independent
smaller universe for test fields or points.

### Searches

Used the prescribed `msearch.py Q138 lem-trf-valuation-exceptional-local-criterion` wrapper.

- LeanFinder: “A normal curve over a finite height valuation ring is semistable at a
  contraction point if and only if its scheme theoretic fibre is an exceptional projective
  line tree”. Eight Weierstrass reduction/minimal-model hits, with returned signatures
  read; none states a general relative marked-curve contraction criterion.
- LeanSearch: “A normal curve over a valuation ring is semistable at a point precisely
  when the exceptional fibre of a modification is a projective line tree with at most
  two boundary or marking points”. Eight Weierstrass good-reduction, minimal-model or
  normal-form hits; none matches this theorem.
- Loogle: `IsValuationRing, IsFractionRing` was invalid (unknown `IsValuationRing`), so it
  was not used as absence evidence. The repaired query `ValuationRing` returned twelve
  existing valuation-ring declarations. The actual embedded-ring notion is the inspected
  `ValuationSubring`, which is reused.
- Mathlib grep: `semistable|rational.*tree|exceptional.*tree` under AlgebraicGeometry:
  zero hits. RingTheory grep located `ValuationRing` and `ValuationSubring`.
- Source-library `rg` for the item id: no declaration for this item (one incidental
  unrelated trace-isomorphism comment in the broad search output). Source-library and
  project grep for `IsProjectiveLineTree|IsSemistableAt|semistableLocus|SemistableLocus`
  found the two landed definition nodes and the proper-curve contraction theorem.
  Those are reused. The latter has the additional properness, algebraic-closure,
  equal-genus and marking-length hypotheses and is not this valuation criterion.
- `dag/lean_names_upstream.json` search for valuation/exceptional-criterion names and
  the proposed helper names found no matching declaration. No duplicate is introduced.

### Validation

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q138
lem-trf-valuation-exceptional-local-criterion <module>` succeeded for the delivered
module in both the wrapper's sandbox and library-path checks, with no diagnostics.
Every universe and variable is explicitly bound; the file also disables both auto-implicit
settings. All lines are at most 100 characters. The only postponed theorem is the main
DAG theorem; the auxiliary maps contain real data and structural compatibility proofs.

No independent second reading was performed by this worker. The maintainer performs the
independent review, as required by the current direct-delivery brief.

## Second reading by Q138

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
