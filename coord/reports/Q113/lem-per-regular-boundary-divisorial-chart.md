## Worker report

The module `Sheaf.AlgebraicGeometry.RegularBoundaryDivisorialChart` states
`AlgebraicGeometry.regularBoundaryDivisorialChart`, with its sole proof `sorry`.
There are no new definitions, new DAG nodes, dependency repairs or statement corrections.

The sources were read in the supplied ILO PDF: VI 1.1--1.5(i), printed pp. 69--70
(PDF pp. 75--76), VIII Remark 4.2.2(i), printed p. 118 (PDF p. 124), and
IX Proposition 2.1 and its proof, printed p. 133 (PDF p. 139).
VI supplies the divisorial log structure and log regularity; IX explicitly supplies the
strict-local chart by a subset of a regular parameter system, without a field base.
The theorem docstring carries all eight proof steps of the node.

Clause-by-clause comparison:

- A regular Noetherian scheme is `(Y : Scheme.{u}) [IsNoetherian Y]`
  and `(_hY : IsRegularScheme Y)`. Mathlib's Noetherian scheme class includes
  local Noetherianity and quasi-compactness. The recorded regular-scheme predicate
  includes local Noetherianity and stalkwise regularity. No base field, excellence,
  connectedness, nonemptiness, or equicharacteristic hypothesis is added.
- The boundary is `(T : Y.IdealSheafData)` with the recorded
  `IsStrictNormalCrossingsBoundary T` hypothesis. This interface includes its
  effective Cartier, reduced and regular-intersection conditions.
- The complement V and its inclusion j are exactly
  `(Scheme.openComplementOfIsClosedImmersion T.subschemeι).toScheme` and `.ι`.
  The conclusion supplies `hV : DenseRange j`, needed to apply the recorded
  log-regular-pair definition; this is a conclusion, not an additional assumption.
- `IsDivisorialFineSaturatedLogRegularPair Y V j hV` states that the prescribed
  divisorial presheaf is a sheaf, satisfies the unit condition, has fs charts, has
  precisely V as triviality locus, and satisfies the regular-quotient and
  characteristic-rank dimension conditions at every geometric point.
- The existential `M : EtaleLogStructure Y` makes the same structure available
  through the general fs-log interface. The presheaf isomorphism
  `e : M.monoidSheaf.obj ≅ divisorialLogPresheaf j` and its structural-map
  compatibility identify this M with the canonical divisorial construction.
  An arbitrary unrelated log structure cannot satisfy that compatibility.
- `M.IsFineSaturated` and `M.trivialityLocus = Set.range j` render the fs and
  precise triviality-locus clauses explicitly; local Noetherianity is already
  supplied by the scheme hypothesis. These are the components of the recorded
  `FineSaturatedLogScheme`, without choosing any new scheme or construction.
- Geometric points are quantified as all `Ω : Type u` with `Field Ω`,
  `IsAlgClosed Ω`, and `y : Spec (.of Ω) ⟶ Y`, as in the dependency interfaces.
  Their A is the recorded `strictLocalRing Y y`, the actual ring point fibre.
- `r : ℕ`, `W : Y.Etale`, and `w : (Scheme.pointSmallEtale y).fiber.obj W`
  give a pointed étale neighbourhood. The monoid domain
  `ULift.{u} (Multiplicative (Fin r → ℕ))` is exactly the free additive monoid
  N^r, written multiplicatively and lifted to the section universe.
- `β` maps that monoid to M's actual sections on W. `M.IsChart W β`
  requires the pushout chart condition at every geometric point of W,
  rather than just a generation condition at the selected point.
- The bijectivity of `p ↦ Associates.mk (M.toEtalePrelogStructure.germ y W w (β p))`
  says that the induced canonical homomorphism to M's characteristic monoid
  at y is an isomorphism. `Associates` is precisely the recorded quotient by units;
  this is not an arbitrary isomorphism with an unrelated monoid.
- `hA : IsRegularLocalRing (strictLocalRing Y y)` supplies the local and
  Noetherian instances for the parameter-system predicate. Each `t i` is explicitly
  equated with the structural image of the germ of β at the i-th standard basis
  vector. Thus the same chart generators occur in every subsequent clause.
- `∃ s, IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ s)` says those
  ordered generators form a prefix of a regular parameter system, reusing the
  dependency predicate and hA's explicit local/Noetherian instances.
- `M.nonunitIdeal y = Ideal.span (Set.range t)` gives exactly the asserted
  nonunit ideal. `IsRegularRing (A ⧸ Ideal.span (Set.range t))` and
  `ringKrullDim A = ringKrullDim (A ⧸ Ideal.span (Set.range t)) + (r : WithBot ℕ∞)`
  give the quotient regularity and dimension formula. The log-regular-pair
  conjunct is the final 'in particular' clause with the characteristic-group rank.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtaleLogStructure`, its
  `IsChart`, `IsFineSaturated`, `trivialityLocus`, `nonunitIdeal`, and the underlying
  `EtalePrelogStructure.germ` and `stalkAlpha`. The full definitions were read;
  `IsSaturatedLogBlowup` itself is not needed for the conclusion.
- `Sheaf.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`.
- `Sheaf.AlgebraicGeometry.LogRegularPair`:
  `IsDivisorialFineSaturatedLogRegularPair`, `divisorialLogPresheaf`,
  `divisorialStructuralMap`, and `strictLocalRing`.

All recorded proof-dependency modules are imported non-publicly when not already
public statement dependencies: PointedEtaleStalk, AffineStrictLocalRingComparison,
the upstream regular-local-domain module, StrictHenselizationCotangentDimension,
StrictHenselizationRegular, RegularLocalUFDBoundaryFactorization,
Mathlib.RingTheory.LocalRing.Module, Mathlib.RingTheory.RegularLocalRing.Defs,
RegularLocalGeneratorsRegularSequence and RegularLocalQuotientKernelParameters.
No import cycle was found. The recorded signatures and proof docstrings of the local
algebra inputs were read, including the actual Mathlib cotangent and Nakayama lemmas.

Edge cases checked: T empty is allowed by the boundary predicate, r = 0 has a
singleton free monoid, an empty t-list and zero generated ideal, and the parameter
extension s is an arbitrary full parameter system. The quotient is A and the
dimension equality adds zero. A geometric point off a nonempty boundary has the
same r = 0 case. Empty Y has no geometric points; the universal chart condition is
vacuous and its open complement is dense. No global finite-dimension assumption is
made: a Noetherian scheme can have unbounded local dimensions, and r is chosen
separately at each point. Mixed characteristic is included. The monoid ULift is a
universe lift, with no restriction on the scheme universe.

Searches before writing:

- `msearch.py leanfinder`, query "The divisorial log structure of a strict normal
  crossings boundary on a regular Noetherian scheme has free monoid charts and is
  log regular": eight hits, primarily smooth local-chart and normalization results;
  none states this result.
- `msearch.py leansearch`, query "A strict normal crossings divisor on a regular
  Noetherian scheme defines a log regular divisorial structure": eight hits,
  Noetherian scheme and normalization facts; no exact match.
- `msearch.py loogle`, query
  `AlgebraicGeometry.EtaleLogStructure, AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`:
  no hits; the external index does not know the side-project declaration.
- `msearch.py grep`, query `divisorial|LogRegular|StrictNormalCrossings`:
  zero Mathlib hits.
- Direct `rg` in the upstream project, side-project `lean/Sheaf`, Mathlib and the
  upstream name index checked the concepts and the proposed declaration name.
  Upstream has no divisorial-log counterpart. Side modules give the exact definitions
  used above. `Sheaf.TraceFormula.DivisorialLogChart.sncDivisorialLogChart` was read
  in full: it assumes smoothness over an algebraically closed field and therefore
  cannot serve as this node's regular-Noetherian, arbitrary-base theorem. Its chart
  also asserts only the selected stalk condition; the present statement asserts
  the required neighbourhood chart. The inverse free-characteristic boundary theorem
  is also not this implication. The proposed declaration name has no existing hit.
- Direct `grep -rn` for the item id in the upstream project found no declaration.

No STATEMENT-DISPUTED or source correction is needed. The datum of M is identified
with the already constructed divisorial presheaf, rather than being defined from
an unproved existence theorem. The only postponed proof is this node's theorem.

Validation: `scompile.py Q113 lem-per-regular-boundary-divisorial-chart` compiled
the delivered module cleanly in both sandbox and named-library mode (2.8 s and
2.9 s). No warnings were emitted. Every universe is explicit and
`autoImplicit` is false; the only theorem proof is `sorry`. The canonical
open-complement declaration is imported from
`WeilConjectures.ConstructibleSheaf.OpenClosedStratification`, whose definition
is the open complement of the range of the given closed immersion.

## Second reading by Q113

No second reading by a worker: the dispatcher requests direct delivery without
starting other agents. The maintainer supplies the independent mathematical review.
