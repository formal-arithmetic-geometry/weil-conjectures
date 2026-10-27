## Worker report

Q11 states lem-pur-adic-operation-domains-source-comparison in
`Sheaf.Paper.AdicOperationDomainsSourceComparison`, namespace
`WeilConjectures.AdicOperationSource`. Every new theorem has only `sorry` as proof.
Every helper definition has actual data, and each postponed proof has its source and
natural-language proof in its docstring. The H2 repair adds one existing:true
definition-ownership node and replaces two statement dependencies, as detailed below.
The node's mathematical statement and the entire Lean module are unchanged.
The item has several independent assertions; `lean.declarations` records all of them.

Hypotheses and objects, clause by clause:

- `P : PurityFiniteSetting` supplies the finite-field datum, coefficient prime distinct
  from the characteristic, fixed coefficient closure and valuation/uniformizer conventions.
  `E`, `F`, `L` with `Field`, `Algebra (Padic P.coefficients.l)` and `FiniteDimensional`,
  and algebra maps `ι`, `j`, render finite coefficient extensions. In particular the
  literal subfields of the fixed closure are obtained by taking their carriers and
  inclusion algebra maps. This uses exactly the coefficient categories of the dependencies.
- `X`, `Y : Scheme.{u}` and their `Over (Spec (.of P.field.k))` instances render the
  two k-schemes. The named geometry section instances require locally finite type,
  quasi-compactness and separatedness of both structure maps, and an over-base,
  separated finite-type morphism `f`. `d : ℕ` and `SmoothOfRelativeDimension d f`
  say smooth of nonnegative pure relative dimension. The `include` command retains
  these hypotheses in each geometry theorem, even when not present in its conclusion.
- The ambient category is `DerivedCategory (scalarReductionSource l E W)`, over the
  recorded completed coefficient sheaf. Constructible objects are exactly
  `sfIntegralConstructibleCategory`; the full uniform finite-Tor category is exactly
  `finiteTorConstructibleIntegralCategory`. Nothing replaces these by the finite-level
  or rational categories. The small-site and module universes remain those of the
  dependency APIs; no equality of site object and morphism universes is added.
- `sourceFunctor` is literally completed `integralDerivedPullback`, followed by the
  existing `sfIntegralTwistingFunctor` with `(d : ℤ)`, followed by shift `2*d`.
  `sourceFiniteTor` is its restriction on objects and maps, with named membership
  theorem `source_preserves`. `P.shiftedTateUnit` is the existing T, and `sourceUnit`
  uses the normalized pullback-unit identification, never an arbitrary isomorphism.
- For compact support and exceptional inverse image, `S` is the *specified operation
  system* already used to define these notions by `def-weil-exceptional-inverse-image`.
  Its `ring.operation c (.integral {carrier := E})` has the actual full finite-Tor
  domain, adjunction, unit, counit, additive and exact structures. `c` exposes the
  compactification used by the recorded construction. `ring.integralLeft` and its
  normalization identify its left functor with the recorded compact-support functor.
  These parameters select the node's specified adjunction data, rather than assuming
  a new unrelated adjunction or replacing G by an arbitrary functor.
- `TorInterval` quantifies every `n : ℕ` at positive exponent `n+1` with the existing
  `HasProEtaleTorAmplitude`; reductions are the recorded derived reductions.
  `r ≤ s` retains the interval convention. `operationDomains` binds natural bounds
  `DX DY` and `topologicalKrullDim ≤ (D : WithBot ℕ∞)` and gives P the interval
  `[r,s+2DX]`, G the interval `[r-2DX,s+2DY]`.
  `source_preserves` gives H the interval `[r-2d,s-2d]`.
- Derived-complete constructibility is explicit for H in `source_preserves`, and for
  the two adjoint functors by their finite-Tor-category codomains, whose object
  property includes `sfIntegralConstructible`. `operationDomains` asserts the
  two triangulated predicates; it retains the existing restricted adjunction.
- Exactness of P (and G) is part of the recorded `Operation.leftExact/rightExact`.
  `operationDomains` asserts `op.F.Linear`, `op.G.Linear`, and a linear equivalence
  whose underlying equivalence is *equal* to the specified adjunction's Hom equivalence.
  Its last clause uniquely characterizes the existing right shift by the counit
  `CommShift` equation for the fixed left shift. `source_exact_linear` asserts H
  exact and integral-linear on the full category, and pins its shift by the signed
  cochain pullback coordinates, their descent, and `sourceShift`.
- `unitDomains` uses `shiftedTateUnitDomain`: both unit and T are finite-Tor
  constructible, unit interval `[0,0]`, and T interval `[-2d,-2d]`. It includes the
  target unit by the same predicate at twist/shift zero.
- C is always `completedDerivedScalarExtension`, the ordinary derived tensor functor.
  `scalar_preserves` asserts complete constructibility, the finite-Tor domain, and
  the unchanged common interval for every algebraic finite extension, with no
  unramified assumption. `scalarConstructible` and `scalarFiniteTor` are its literal
  full-subcategory lifts. `scalar_exact` gives exactness with the *published canonical*
  scalar shift; inclusion shift maps are explicitly inserted on both sides.
- `pullbackScalar` is strict pullback/scalar balancing conjugated by the specified
  `CompletedLineTensor.chi` on each complete input, in the C L to L C direction.
  `sourceComponent` is canonical scalar shift, then ordinary twist beta, then the
  shifted twisted pullback comparison. `source_naturality` is its square on every
  derived morphism, and `sourceComparison` uses exactly those components.
  `sourceFiniteComparison_existsUnique` restricts those same components to D^b_ctf;
  `sourceFiniteComparison` selects the uniquely component-normalized natural isomorphism.
- `source_composition` writes the exact displayed cocycle in Lean composition order.
  Its alpha is `(CompletedLineTensor.associatorData ...).derived`, the ordinary
  representative/counit-normalized tensor associator. No tower associator is chosen.
  `source_identity` gives the identity case under `CompletedLineTensor.ordinaryUnit`.
- `source_shift` spells out commutation with *canonical* shifts, not existence of
  unspecified shifts making the square commute. Pullback shifts are required to
  descend the signed cochain formulas; their existence is a conclusion of
  `source_exact_linear`. Line shift is the existing termwise derived shift;
  the final even-shift interchange uses `shiftFunctorComm`. The inherited inclusion
  shift comparisons are inserted explicitly. Together with source/scalar exactness
  this is exactly the exact-natural-isomorphism clause.
- `source_at_unit` identifies a at `constantWeilIntegralObject` with the specified
  `P.shiftedTateScalarIso`, after the canonical coefficient-unit maps in Y and
  `sourceUnit` in X. Its right side is C(sourceUnit) followed by q.
- `compactScalarModel` is `Iso.refl`: the completed ordinary scalar and the
  compact-support API's pbc scalar are definitionally the same universal K-flat
  witness in this size convention. `compactSupportComparison` is exactly
  `PurCompactSupport.recordedComparisonIso` on the actual recorded functors;
  it therefore keeps the dependency's unit, composition, proper/open, projection,
  finite-reduction and shift normalizations. `compactSupport_exact` explicitly
  states its underlying canonical mate commutes with the canonical shifts.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, its field and coefficient data.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, the actual coefficient quotient rings.
- Mathlib smooth, finite type and proper morphism modules:
  `SmoothOfRelativeDimension`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`; the coefficient sheaf construction
  is reexported by the completed scalar and reduction modules.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, its full category;
  `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleIntegral` and its category;
  `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower` (the existing reduction convention).
- `Sheaf.Paper.DerivedPullbackTensorHom`: `integralDerivedPullback`,
  `constructibleIntegralPullback`, `integralPullbackScalarComparison`;
  `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: `sfIntegralTwistingFunctor`.
- `Sheaf.Paper.QcqsCompactSupportRealization`: the actual compact-support realization;
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: `System`, `Operation`,
  `integralTriangulated`, `RingSystem.integralLeft` and its normalization.
- Mathlib triangulated and linear APIs: `ObjectProperty.IsTriangulated`,
  `Functor.IsTriangulated`, `Functor.Linear`, `NatTrans.CommShift`, `LinearEquiv`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: the ringed derived scalar API;
  `Sheaf.Paper.IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`;
  `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: `completedDerivedScalarExtension`,
  `completedScalarComparison`, `completedCoefficientMap`, finite-free completeness.
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`: `recordedSupport`,
  `recordedComparisonIso`, `finiteTorIntegralInclusion`, and the existing normalization
  interfaces and equations. Mathlib `topologicalKrullDim` is the dimension convention.
- Supplementary already-landed statement interfaces are added to `stmt_deps`:
  `def-pur-shifted-tate-unit-scalar-data` owns the seven existing helpers in
  `PurShiftedTateUnitScalarCoherence` (T, q, residue inverses, scalar shifts, coefficient
  units and the base inclusion), without citing the coherence theorem. The landed
  `def-sf-integral-constructible-linear-structure` owns the constant-section linear
  instances in `SfIntegralConstructibleLinear`; `CompletedLineTensorCoherence` supplies chi, intrinsic
  completeness, ordinary alpha and unitors; `ConstantGeometricStalkUnit.integralUnit`
  supplies the canonical pullback-unit identification; `IntegralPullbackShiftCoordinates`
  supplies signed shift/descent normalization; `IntegralTwistDerivedScalarCanonical`
  supplies ordinary beta; `IntegralOperationsScalarComparisons` supplies theta.
  A traversal of statement and proof dependencies verified none reaches this item.

Edge cases checked before and during elaboration: empty schemes allow DX=DY=0
(the dimension is WithBot, never a substituted negative integer); d=0 keeps the
interval unchanged; r=s is allowed; all positive reduction exponents are covered;
zero objects are not excluded; coefficient identity and repeated fields are included;
ramified extensions have no same-index flatness hypothesis; arbitrary integer input
shifts and the even final shift are included. No irreducibility, nonemptiness,
positive dimension, unramifiedness or extra universe equality has been assumed.
No statement is believed false; there is no STATEMENT-DISPUTED issue identified.

Actual searches:

- `msearch.py ... leanfinder "Completed integral constructible finite Tor operations compact support exceptional pullback coherent coefficient source comparison"`:
  eight unrelated algebraic-geometry limit results, no matching statement.
- `msearch.py ... loogle "CategoryTheory.Functor.CommShift"`:
  twelve general CommShift results; usable generic shift API, no combined statement.
- `msearch.py ... grep "adicOperation|sourceComparison|HasProEtaleTorAmplitude" CategoryTheory`:
  zero matches in that Mathlib subdirectory.
- `msearch.py ... leansearch "Adic constructible derived complete finite Tor amplitude six operations scalar extension"`:
  ordinary adic-completion/scalar results, no matching completed operation theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for sourceComparison, operation-domain
  names and Tor-amplitude interfaces, and the exact node id in the upstream Lean:
  no existing theorem stating the whole item. Existing scalar, shift, twist and
  compact-support helpers found there are reused, not redefined.
- Current blueprint read under `literature/blueprint/latest/`, purity transport proof
  Steps 2-3; the node's twelve-step extracted proof supplied the detailed clauses.

Validation: every delivered Lean file compiled separately with the prescribed
`scompile.py` against the live published library. The previous module-mode sandbox
and named library module compiled with no errors or non-sorry warnings. This repair
repeats the prescribed compile and dry run; its results are recorded below.

## Second reading by Q11

The dispatcher explicitly prohibited starting other agents; no independent worker
has been invented. Q11 performed a second clause-by-clause self-reading with the node,
full dependency signatures and the module open; the maintainer's independent reading
is the separate review requested in the brief.

This reading caught and repaired inherited full-subcategory shifts that are not
definitionally the ambient shifts: explicit inclusion commShiftIso maps now occur in
all normalization equations. It also moved scalar exactness outside the smooth-map
section, so it does not require a dummy smooth morphism, and made the finite-Tor
restriction of a a uniquely component-normalized actual natural isomorphism. The
compact-support scalar model was verified by an actual `Iso.refl` declaration, and
its comparison is the exact existing recordedComparisonIso. No mismatch with the
node's hypotheses or clauses remains identified.

Dry run: `deliver2.py Q11 lem-pur-adic-operation-domains-source-comparison --no-push`
returned `OK (dry run): commit b14d272dbb3 passes the preflight and compiles; nothing pushed`.


## Returned delivery repair: H2

Returned immutable head: `6048593f72b0`. The maintainer independently accepted every
mathematical clause and all edge cases, and requested definition ownership repairs.
The retained sandbox was compared with the current main node: only the intended
`lean` and added `stmt_deps` fields differed; its mathematical statement, proof,
proof dependencies and remaining fields agreed. The repair is based on that current
main record and retains its existing dependencies. The delivery wrapper creates the
new commit on current main, rather than stacking it on the returned delivery.

1. Removed `lem-pur-shifted-tate-unit-scalar-coherence` from the item's added statement
   dependencies and replaced it with the new definition node
   `def-pur-shifted-tate-unit-scalar-data`. That node has `existing: true` and owns
   exactly the seven definitions named in the return in the already-published module
   `Sheaf.Paper.PurShiftedTateUnitScalarCoherence`: `PurShiftedTate.unitIso`, `shiftIso`,
   `baseInclusion`, and `PurityFiniteSetting.shiftedTateResidueInverse`, `shiftedTateUnit`,
   `shiftedTateUnitDomain`, `shiftedTateScalarIso`. Its primary Lean signature is copied
   verbatim from `def shiftedTateScalarIso` through the result type. No coherence
   theorem, new choice or new Lean declaration is part of this ownership node.
2. Removed `lem-weil-integral-constructible-linear` from the added statement
   dependencies and replaced it with the landed
   `def-sf-integral-constructible-linear-structure`, whose record explicitly owns
   `sfIntegralCoefficientLinear` as well as `sfIntegralConstructibleLinear` in
   `Sheaf.Paper.SfIntegralConstructibleLinear`. The exact instance remains unchanged.
3. Included all four recommended definition dependencies:
   `def-weil-constant-coefficient-objects` (the regular completed unit),
   `def-weil-constant-weil-structure` (the constructible constant-unit wrapper),
   `def-weil-integral-derived-reduction` (the actual derived reductions), and
   `def-pur-integral-operation-complex-models` (the actual pullback complex model).
   Their current records and declarations were opened and read. The other four
   supplementary theorem dependencies remain: they construct the normalized
   associator/unitors, pullback unit, ordinary twist comparison and scalar/pullback
   comparison, exactly as accepted by the return.

A read-only traversal of the DAG verifies that the new definition's dependencies and
the five landed definition dependencies do not reach this item. The new node has the
item's chapter and unit, empty proof and proof_deps, no mathlib_match, all required
search and blueprint metadata, and `import_flags: []` because it serves this reachable
item. No existing dependency node is edited. The item's TeX statement is unchanged,
so no statement_change is needed. No Lean byte changed; its SHA256 is
`6cfff40c44b10cb03a998bb07cdb4c4d1e2af968455f78c092b4c4b767e5846f`.

## New nodes

`def-pur-shifted-tate-unit-scalar-data` records the existing completed coefficient-unit
multiplication u, canonical ordinary scalar shift s, lifted base inclusion, canonical
residue inverses, shifted Tate unit T, the UnitDomain predicate, and q defined as
shift followed by beta and twisted u. It is an ownership record for the exact seven
published definitions, with `existing: true` and no module copy. Its source is the
current blueprint purity transport proof, Steps 2 and 4, together with the explicit
normalized helper construction before the shifted-Tate coherence theorem. Its
statement defines the domain predicate rather than asserting it or any coherence
law. The u and s maps keep the theorem-constructed coefficient-unit and universal
shift normalizations of their existing definitions; beta is the fixed ordinary
comparison supplied by the twist theorem.

Actual new searches: LeanSearch query "Definitions of shifted Tate unit and canonical
scalar extension unit and shift comparisons for completed integral coefficients"
returned eight Witt-vector or general shift-adjunction results. LeanFinder query
"Shifted Tate unit integral coefficient scalar comparison q canonical shift
multiplication on the coefficient unit" returned eight PreTilt, Witt-vector and
Weierstrass results. The exact Mathlib grep
`shiftedTateUnit|shiftedTateScalarIso|PurShiftedTate` returned zero hits. An earlier
broader grep also included `Tate.*unit` and returned 25 irrelevant matches because
its case-insensitive search matched the substring in "state"; that broad result was
not treated as an exact match or used instead of the precise grep.

The same exact-name search in upstream `lean/WeilConjectures` found no construction;
in `lean/Sheaf` it located the definitions in the published shifted-Tate module.
A declaration-record scan found their theorem-node record, but no definition-node
owner. Blueprint search `shifted Tate unit` returned `def-sf-orientation` and
`def-weil-exceptional-inverse-image`, neither of which defines this data. The new node
records these actual searches and reuses the exact Lean definitions rather than
introducing any duplicate notion.

Repair second reading by Q11: the new node's statement matches the seven signatures
and bodies, including the arbitrary-scheme scope of u/s, the k-scheme scope of the
residue inverses/T/q, every positive reduction, and the fact that UnitDomain is only a
predicate. It covers d=0, empty schemes, identity extensions and ramification with no
additional hypothesis. The item now cites the requested definition owners. Its Lean
and each previously accepted mathematical clause are byte-for-byte unchanged.

Repair validation: the prescribed scompile.py accepted the unchanged module with no
errors or non-sorry warnings. The repaired packet, including the seven existing
declaration probes, passed deliver2.py --no-push: `OK (dry run): commit 66c8df4c24d
passes the preflight and compiles; nothing pushed`.
