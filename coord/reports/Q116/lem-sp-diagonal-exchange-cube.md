## Worker report

The module `Sheaf.Paper.DiagonalExchangeCube` states
`WeilConjectures.diagonalExchangeCube`, with its proof postponed by `sorry`.
Its five helpers are real constructions or explicitly written propositions belonging
to the diagonal-cube interface. No independent exchange, inverse, orientation,
or unspecified right adjoint is introduced. The returned-delivery repair changes only
the definition-owner citation and corresponding imports; see the correction
record below. The accepted mathematical statement is unchanged.

The source read is the current `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`, Proof (1), together
with all six expanded proof steps in the assigned DAG node.

Hypotheses and objects, clause by clause:

- `D : FiniteFieldDatum` supplies the prime characteristic, finite field and its
  fixed algebraic closure. `C : D.CoefficientDatum` supplies the coefficient prime,
  its primality and inequality with the characteristic. `r` and `hr : 1 ≤ r`
  give precisely the positive exponent. The coefficient is literally
  `ULift (ZMod (C.l ^ r))`, the standard size lift of Z/ell^r, with no replacement
  by a ramified coefficient-extension quotient. `d : ℕ` permits d=0.
- `aY`, its separated/local-finite-type/quasi-compact instances, and `f` with
  separated/quasi-compact/smooth-relative-dimension instances express the
  separated finite-type k-scheme setting; the structure of X is `f ≫ aY`.
  The definition explicitly installs `SmoothOfRelativeDimension.smooth d f`;
  its smoothness instance supplies local finite type of f. `aY'` and its three corresponding
  instances express the same assumptions on Y'. `hv` says v is a k-map.
  No property of v such as flatness or smoothness is assumed.
- X' is exactly `pullback f v`, u is `pullback.fst f v`, and f' is
  `pullback.snd f v`. The two self-products are the actual `pullback f f` and
  `pullback f' f'`, with their named projections and `pullback.diagonal`.
  `diagonalCubeMap` is the actual universal `pullback.map` induced by (u,u,v).
- In `diagonalCubeComparisons`, `sq₁` and `sq₂` state that the canonical q with
  each primed projection is Cartesian over u. Thus in particular the first
  pair is the canonical pullback of the original pair. `hΔ` preserves the
  specified diagonal section. The section identities themselves are those of
  `pullback.diagonal`, not extra unconstrained sections.
- The five `SmoothOfRelativeDimension d` clauses give f' and all four
  projections their prescribed dimension. Each diagonal has the existing
  `PurityConventions.IsRegularOfPureCodimension` predicate: regular generators
  of length d near every source point, with an empty sequence permitted at d=0.
  Closedness is the canonical instance from separatedness. This avoids the
  older predicate which requires positive codimension, and the global length-zero
  weak-regular predicate which incorrectly excludes proper clopen components.
- `diagonalCubeWitnessed` quantifies over every ordinary pro-etale derived input
  with constructible cohomology, a bounded interval and finite Tor amplitude,
  using the recorded fixed-module constructibility and Tor declarations.
  A common interval is equivalent to independent finite intervals by enlargement.
  It retains a bounded-below etale complex with bounded constructibility and its
  actual comparison isomorphism. For every compactification it asserts both
  invertibility of the raw proper/open compact-support exchange and equality
  to its canonical witnessed transport. This appears for the four squares
  defining b_f, b_f', b_p1 and e_1.
- The four existential isomorphisms b, b', bp and e are pinned down by their
  hom-equalities to `Etale.dualizingComplexBaseChangeMap`. The latter is the
  published mate of inverse compact-support exchange under the specified
  constructible adjunction, followed by exceptional image of the canonical
  coefficient-unit comparison. Thus these are the required counit maps.
- `diagonalCubePullbackIso` is a composite of the canonical derived pullback
  compositors for an equality of scheme maps. The first equation states
  q*(b_f) followed by b_p1 equals the compositor followed by p2'*(e_1) and b_f'.
  Both sides are explicitly mapped by derived comparison into the ordinary
  pro-etale derived category of W'. These are the canonical etale-origin
  coordinates, not a different completed or unrestricted exceptional category.
- The second equation starts with u*(Delta*omega_p1), uses the compositor from
  `hΔ`, then Delta'*(bp), then kappa_f'. Its other side is u*(kappa_f) then e.
  The two kappas are explicitly the diagonal pullback `mapIso b.symm` (respectively
  `mapIso b'.symm`), followed by `leftDerivedUpperStarCompSectionIso` applied to
  `pullback.diagonal_snd`. This is the literal body formerly accessed through
  `finiteDiagonalRestriction`; no theorem conclusion is used.
  Again both sides are explicitly in the ordinary pro-etale category of X'.
- `diagonalExchangeCubeStatement` installs the Noetherian and compactness facts
  deduced from aY and uses Nagata's existing instance. There is no extra
  `HasCompactification` assumption in the theorem's signature. These local
  instances, the deduction of smoothness, and nonzero modulus are construction
  details inside a definition; the theorem contains
  no let binder, hidden cast, or auto-bound variable.

Dependency declarations used (source signatures and docstrings inspected):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison` and upstream
  `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps`:
  `finiteComparedDualizing`'s canonical etale-origin convention and
  `Etale.dualizingComplexBaseChangeMap` / `rightDerivedUpperShriekBaseChangeMap`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence`:
  `Etale.leftDerivedUpperStarCompSectionIso`, composed explicitly after diagonal
  `leftDerivedFunctor.mapIso` of the inverse mate. The former theorem-module
  wrapper `PurityFiniteSetting.finiteDiagonalRestriction` is not used.
- `Sheaf.Paper.PurityConventions` (landed node `sk-def-purity-conv`):
  `PurityConventions.IsRegularOfPureCodimension`, including d=0.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, the recorded intrinsic
  stratification/local-constancy/finite-geometric-stalk predicate.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`:
  `Scheme.HasFixedCoefficientProEtaleTorAmplitude`, the actual universal
  degree-zero-sheaf tensor test, at independent original site universes.
- `Sheaf.Paper.CompactSupportExchangeTransport`, through the landed definition node
  `def-pur-compact-exchange-witness-transport` (Q55, `c3276c46f03`):
  `compactExchangeTransportComparison`, `compactExchangeTransportSource`,
  `compactExchangeTransportTarget`, and `compactExchangeTransportAtWitness`.
  These are the existing definitions, used without modifying their source module.
  The raw `rightDerivedLowerShriekOfCompactificationBaseChangeMap` comes from
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange`.
- Mathlib `SmoothOfRelativeDimension`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsPullback`, `pullback`, `pullback.map`, `pullback.diagonal`;
  upstream `Etale.leftDerivedUpperStarComp`, canonical site comparison;
  `ZMod`, `ULift` and Nagata compactification. The base-change convention node
  points to module base change but explicitly directs scheme consumers to
  these actual categorical pullbacks.
- Plain proof imports are `Sheaf.Paper.ExchangeFunctoriality`, the recorded
  regular-diagonal theorem, `PurityFiniteSettingComparisonHypotheses`,
  `CohomologicalSmoothnessTheorem`, `ProEtaleConstructibleOrigin`,
  `IntegralFinitePullbackComposition`, Mathlib `Adjunction.Mates` and
  `Morphisms.Etale`, plus `PurityDiagonalBaseChangeCompared`. The transport
  definitions use the public import of `CompactSupportExchangeTransport` recorded
  by their existing definition owner. The compact-support finite-level theorem is publicly
  imported by ExchangeFunctoriality. The base-change property Mathlib modules
  are publicly available from the statement imports. This includes every
  recorded, stated proof dependency without an import cycle.

The added regularity dependency remains the landed `sk-def-purity-conv`. The
transport construction is cited through the already landed definition node
`def-pur-compact-exchange-witness-transport`; its source module and the transport
theorem record are unchanged from the base. The diagonal theorem remains
a proof dependency, and is removed from statement dependencies. The transport
theorem conclusion is not required by any helper signature.

Edge cases checked: identity v gives the canonical pullback square and unit
compositors; d=0 uses empty regular generators near a clopen diagonal; empty
schemes have no source-point regularity obstruction; r=1 is permitted; all
variables and the universe u are explicitly bound, with coefficients at u+1
and schemes at u. The finite ring is nonzero because ell is prime and r positive.
The coefficient size lift adds no coefficient extension or completion.

Searches: msearch.py leanfinder queried “The diagonal section dualizing comparison
commutes with counit-defined exceptional base change by pasting the Cartesian cube”
and returned 8 hits about exponentiable morphisms and the elementary categorical
diagonal of a composite; none is this sheaf-theoretic statement. Loogle query
`CategoryTheory.Adjunction, CategoryTheory.IsPullback` returned 0 hits. Mathlib
msearch grep `diagonal.*(exchange|dualizing)|dualizing.*diagonal` returned 0 hits.
LeanSearch queried “Naturality of the diagonal section dualizing comparison under
arbitrary base change” and returned 8 hits on linear dual base change, product
diagonals, global sections and cartesian monoidal functors, none this statement.
Direct rg with diagonal/exchange variants in `lean/Sheaf` and `lean/WeilConjectures`
found no such statement (the coefficient-exchange module is a different notion).
`PurityDiagonalSectionPasting` was also inspected: it concerns the composite tower
f,g and its tensor/section comparison, not this arbitrary-v base-change cube;
the identical inverse-mate chain is now written explicitly here.
Searching the exact node id in upstream source returned no hit. Existing
pullback, mate, diagonal-restriction and regularity constructions were reused.

## Second reading by Q116

A separate clause-by-clause rereading of the node and the final module was made
within this worker; no other agent was started, following the dispatcher brief.
The maintainer's independent delivery review remains required. The rereading
checked both equation directions, the q/p2 versus p1 square orientations, hDelta's
symmetry in the second compositor, and the inverse direction in both kappas.
It caught the dimension-zero mismatch in the older global regularity predicate;
the published neighbourhood-of-source predicate resolves it without changing the
node. It also replaced an initial etale-origin-only domain abbreviation with the
recorded intrinsic fixed-module constructibility and finite-Tor predicates, and
made raw compact-support invertibility explicit. The four mate hom-equalities
prevent accidental replacement by arbitrary endpoint isomorphisms.


## Repair of return L at 4a097ac96061

The previous extraction duplicated the already landed definition node
`def-pur-compact-exchange-witness-transport` (Q55, `c3276c46f03`), present on
the delivery base. I missed that owner in the earlier search. Its full statement,
existing:true Lean record, and the four recorded source definitions were reread:
C is the normalized proper/open comparison, S and T are the same endpoint paths,
and the witness transport is exactly alpha.inv, S.inv, the comparison image of
the etale exchange, T.hom, alpha.hom. It asserts neither exchange invertibility
nor witness independence. This is precisely the data used by diagonalCubeWitnessed.

The repair deletes the duplicate node `def-sp-compact-exchange-transport` and
module `Sheaf.Paper.CompactExchangeTransportDefinitions` from the sandbox delivery.
The replacement copies of `CompactSupportExchangeTransport.lean` and
`lem-pur-co-smooth-exchange-transport.json` are also removed: their live base
versions remain untouched. The item now cites the landed definition owner in
both its statement text and stmt_deps, and publicly imports its recorded module
`Sheaf.Paper.CompactSupportExchangeTransport`. The correction explanation and
Lean note are updated to describe this reuse. No new node or dependency module
is delivered.

Everything else from the accepted immutable head is preserved. In particular,
removing the extraction import and promoting the original module import are the
only changes to the Lean file. The two inlined kappas, four mate hom-equalities,
two equations, all hypotheses and the single sorry proof remain byte-identical.
The identity, dimension-zero, empty-scheme and r=1 cases therefore remain covered.
The current base still has the original item statement and no Lean record; this
repair retains the original correction baseline and proof dependencies.

## Statement corrected

The old statement remains verbatim in `statement_change.old_statement`. The
mathematics is unchanged: only the kappa definition citation is replaced by its
derived-pullback definition citation, and the witnessed-exchange sentence cites
`def-pur-compact-exchange-witness-transport`. The old stmt_deps remain recorded in
`old_stmt_deps`. `lem-pur-diagonal-base-change` is removed from stmt_deps while
remaining in proof_deps, and the transport construction is represented by the
already landed definition owner. The current source is the latest blueprint,
Proof (1), with the assigned DAG's expanded argument. No proof step, proof
dependency, hypothesis or equation changes.

The complete current citer audit has exactly one node:

- `det-sp-purity-bc-factors`: holds true. It uses the identical diagonal cube,
  hypotheses, specified mates and equations. Reusing the landed definition owner
  and retaining the explicit kappa chains leaves that use unchanged. The citer
  is not edited.

The return repair was reread against the item node, the owner node and the final
Lean file within this worker, as required by the no-subagent dispatcher brief.
The earlier claim that no definition node owned the transport data is withdrawn;
the landed Q55 definition is the exact match. The maintainer's independent review
of immutable head `4a097ac96061` already accepted the mathematics, which this
repair keeps unchanged.

## Validation

The repaired item module passed `scompile.py Q116 lem-sp-diagonal-exchange-cube`
against the live published library with no errors or unexpected warnings. The
repair comparison verified that the only Lean changes from the returned head
are replacement of the extraction-module import and promotion of the original
transport-module import to public. The theorem signature and every definition
body remain unchanged. The duplicate node/module and both dependency replacement
copies are absent from the delivery. The complete citer audit still has exactly
`det-sp-purity-bc-factors`, marked holds:true.
