## Worker report

The module states the finite integral coefficient-extension rectangle, its whole-system
version, its ramified finite reductions, its normalized total-limit identification,
naturality, and canonical-refinement independence. All theorem proofs are `sorry`.
Definitions contain actual composites or propositions specifying those composites;
there is no arbitrary exchange map, scalar map, or endpoint-only choice.
The statement and proof of the assigned node are unchanged. The new definition node
`def-coef-finite-free-system-data` is added to stmt_deps as the owner of the existing
coefficient towers and normalized geometric comparison data used in the signature.
The finite-free restriction theorem is retained only in the original proof dependencies.

Clause-by-clause correspondence (namespace `WeilConjectures.IntegralScalarExchange`):

- Finite-field conventions: `D : FiniteFieldDatum.{u}` includes the algebraic closure
  of the finite field and its characteristic; `_hl : l ≠ D.p`, `[Fact l.Prime]`.
  Finite coefficient fields: `E F`, `Field`, `Algebra ℚ_[l]`, `FiniteDimensional`,
  and the injective field embedding `i : E →ₐ[ℚ_[l]] F`. General finite models and
  an embedding avoid choosing another algebraic closure or excluding identity extensions.
- `h`, `hr : PurCompactSupport.Ramification l E F i h`, `hp : 1 ≤ h` express the
  ideal equality of uniformizers, not equality of chosen generators.
- `X.Over`, `Y.Over`, separated, locally finite type and quasi-compact structure
  morphisms express separated finite-type k-schemes. `f.IsOver` and the analogous
  three properties express the separated finite-type k-morphism. The existence of
  `c : Compactification f` supplies the chosen open/proper factorization.
- `g`, `x`, `b` are underlying-scheme morphisms with `IsIso`; neither g nor x has
  an `IsOver` premise. `c'`, `sp : ChosenCartesianSquare b c'.g c.g g`, and
  `sj : OpenImmersionSquare x c'.i c.i b` express the isomorphism base change of
  both compactification factors, hence of f. `sj` includes the actual pullback
  witness, and proper Cartesian data uses the dependency's chosen square.
- The input is the published `DerivedCategory (scalarReductionSource l E X)`
  with `finiteTorConstructibleIntegral l E X M`. This includes derived
  completeness, bounded constructibility and the common reduction/Tor intervals.
- Completed rings are `PurCompactSupport.completed l E/F`. Compact support is
  exactly `image`, separately derived proper image after exact open extension.
  Pullback is `pull (completed ...)`. Ordinary completed scalar tensor is
  `pbcDerivedExtend (completedCoefficientMap ...)`, as in the recorded coefficient
  comparison. No exceptional inverse image, purity map or Weil datum is introduced.
- `square`, `openInverse`, `exchange` expand the dependency's specified geometric
  word in this coefficient convention: the canonical inverse-image compositor,
  the proper direct-image adjunction mate, then the inverse open-unit transpose.
  `openInverse_isIso` delays only the Cartesian open comparison's proof.
- `comparison` and `scalarPull` are imported, not copied. The latter is the
  uniquely adjoint-conjugate comparison for the section-normalized restriction
  square, hence the balanced scalar association. `left` is C(xi), then c_f', then
  P_f'(J_x). `right` is J_g, then G_g(c_f), then xi_F. Composition uses Lean's
  left-to-right `≫`; this reverses the printed multiplication order, not the maps.
  The main theorem's first conjunct is precisely their equality at M.
- `FiniteLeft`, `FiniteRight` substitute `finite l E (n+1)` and
  `finite l F (h*(n+1))` and `finiteChange`. Their input is actual quotient tensor
  of M. Thus zero Lean index means exponent one; no positive exponent is omitted.
  `finiteCoherent` supplies the same canonical constant coefficient compositor.
  Scalar maps are the same imported proper/open comparison and balancing maps.
- `Systems` works in the ordinary derived category of modules on the ringed
  sequence site. `A`, `B`, `aTransition`, `bTransition`, `systemInclusion` are the
  actual dependencies' constructions: B is O_F/(image(pi_E))^(n+1), identified
  by ramification with the F exponent h(n+1). It retains every quotient transition.
  `Scalar` is the universal K-flat tensor model with its normalized adjunction,
  not an unconstrained functor. `Systems.comparison` explicitly orders the proper
  scalar mate before the open scalar identification; `Systems.pullScalar` is
  normalized adjunction conjugation. `Systems.left/right` are the two entire-system
  natural transformations. `strictScalarIsomorphismExchange` asserts their equality
  before evaluation or limit, for the canonical `Geometry` and `Compatibility`
  quantified as `G` and `hG`, with their types owned by the new definition node. Since this is an
  equality of natural transformations on the ambient system category it applies
  in particular to the normalized actual reductions in the node. No faithfulness
  of evaluation or restriction is presumed.
- `sourceProjection` and `targetProjection` use the independently fixed coefficient
  square, quotient-adjunction unit, proper/open reduction and pullback balancing.
  `StrictLimitEquation` gives a simultaneous flat K-flat presentation P,Q,v of
  the common strict map. Its epsilon families are pinned to these projections,
  and identify the SAME strict map with each finite composite at h(n+1).
  It requires the actual identity-completion units to be isomorphisms, and
  `IsCofinalRoosMap` pins BOTH cone coordinates to the selection/block maps.
  The last two equations identify the Roos map of that strict map with EACH
  integral composite. This expresses the specified total derived limit, including
  ramification/cofinality, and not arbitrary operation/limit commutation.
- `rectangle_naturality` writes the naturality equation for both integral paths
  and every input morphism. System naturality is built into NatTrans equality.
- `rectangle_refinement` writes the two transport equations using the imported
  `refinementComparison` and the commuting refinement/base-change square. It
  permits arbitrary primed k-structures for stating those existing comparisons;
  it imposes no linearity of x,g. Such structures can in particular be transported
  from X,Y. `scalarPull_finiteTor` supplies the target comparison domain, rather
  than adding a finite-Tor hypothesis. The imported refinement cocycle gives common
  refinement independence. The strict word uses the same geometric generators;
  the finite-free compatibility interface preserves their pasting and inverses.

Dependency declarations read and used (including their exported constructions):

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-pbc-cartesian-square`: `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, `AlgebraicGeometry.ChosenCartesianSquare`.
- `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.RefinementCategory`, `AlgebraicGeometry.Compactification.Refinement`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.QcqsCompactSupportRealization`, `WeilConjectures.sfQcqsCompactSupportRealization`.
- `lem-pur-weil-semilinear-exchange-reindexing`: `Sheaf.Paper.SemilinearExchangeReindexing`, `WeilConjectures.semilinearExchangeReindexing`.
- `lem-pur-compact-support-integral-coefficient-comparison`: `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`, `WeilConjectures.PurCompactSupport.integralCoefficientComparison`.
- `lem-pur-integral-operations-scalar-extension`: `Sheaf.Paper.IntegralOperationsScalarComparisons`, `WeilConjectures.scalarOperationsOrdinary_tower`.
- `lem-pur-normalized-scalar-comparison-realization`: `Sheaf.Paper.NormalizedScalarComparisonRealization`, `WeilConjectures.normalizedScalarComparisonRealization`.
- `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.
- `def-coef-finite-free-system-data`: `Sheaf.Paper.FiniteFreeSystemRestriction`,
  `WeilConjectures.FiniteFreeSystemRestriction.Geometry`, with the 25 existing
  declarations listed in the new node. The existence theorem is not used in the signature.

The recorded `Sheaf.Paper.NormalizedScalarComparisonRealization` source is absent
from both the local read clone and the server (`scompile.py --source` returned
`Module source unavailable`). It is not imported or privately recreated. The
present statement uses the published normalized `scalarPull` adjunction square
and explicit projection/quotient/Roos normalization instead of requiring the
missing theorem or its tensor-operation package as data. This does not assume
that theorem's conclusion or replace its maps by arbitrary isomorphisms. There
is no change to that dependency's record, since no replacement interface for its
broader tensor theorem is needed to type this node.

Searches for an existing statement:

- msearch LeanFinder: “finite integral coefficient scalar extension commutes with
  compact support exchange for scheme isomorphisms on strict coefficient systems”:
  eight hits, scheme isomorphism and normalization lemmas, no matching rectangle.
- msearch Loogle: `CategoryTheory.Adjunction, CategoryTheory.NatTrans`: zero hits.
- msearch grep `semilinear|compactSupport|uniformizer`, Mathlib/AlgebraicGeometry:
  four StructureSheaf hits, no derived-system coefficient exchange.
- msearch LeanSearch: “Finite integral change of coefficients preserves the proper
  mate followed by open extension exchange on derived systems before total inverse
  limit”: eight hits (finite/proper, integral base change, inverse-system results),
  no such comparison. Raw search summaries are in the sandbox searches.jsonl.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for scalar/exchange/semilinear/
  uniformizer and the exact node id: related coefficient, strict-tower and
  reindexing APIs found and used; no existing declaration states this rectangle.
  The item id has no pre-existing Lean declaration. No second Lean definition is
  introduced; local helpers expand the composites and normalization clauses of
  this node, and are all listed in lean.declarations. The returned-delivery repair
  below registers the existing system data through a definition-level DAG node.

Edge cases checked against the signatures and formulas: E=F and i=id; g=x=b=id;
non-k-linear underlying-scheme automorphisms; j=id and p=id; empty schemes and
zero inputs; h=1 and h>1; n=0 (exponent 1) and all larger quotients. There is no
restriction to unramified extensions, no equality of chosen uniformizers, no
fixed basis in the statement, and no purity/Weil structure. The system ambient
category retains the successor site-object universe and its smaller morphism
universe. The existing normalized scalar model uses coefficient universe u+1;
finite field models can always be lifted to it, without identifying site sizes.

No statement correction and no STATEMENT-DISPUTED finding.

## Second reading by Q29

The dispatcher explicitly forbids starting other agents, so this is a separate
self-audit pass, not a claim of an independent agent's review. The maintainer's
independent delivery review remains required. I reopened the DAG statement and
Lean together and checked each clause against the mapping above.

The audit found and repaired: the first version only stated the integral component;
I added actual entire-system NatTrans equality, ramified finite components,
source/target projection normalization, cofinal Roos equations, naturality and
refinement equations. It initially phrased the target refinement finite-Tor domain
as a premise; I removed that extra premise and supplied scalarPull_finiteTor.
The system scalar map was initially the single pasted scalar mate; I expanded it
to the ordered proper mate followed by the open identification as the statement
requires. The cofinal presentation now requires invertibility of the independently
fixed completion units as well as the selection/block quasi-isomorphisms.

All variables and universes are explicitly bound, autoImplicit and relaxedAutoImplicit
are false, every theorem is sorry-only, each declaration has a source/blueprint
docstring and every line is at most 100 characters. The one module's full declaration
list is in the node record. No source or library file was changed directly.


## New nodes

`def-coef-finite-free-system-data` records the existing definitions in
`Sheaf.Paper.FiniteFreeSystemRestriction` with `existing: true`, primary declaration
`WeilConjectures.FiniteFreeSystemRestriction.Geometry`, and 25 declarations listed
in its Lean record. It defines the lower and upper quotient towers and reductions,
actual inclusion and restriction functors, finite-type separated scheme objects,
section-normalized ordinary scalar squares, their derived pullback/direct-image/open
mates, the conditional geometric comparison data and its generator-compatibility
predicate, and the fixed compactification functor and comparison. It asserts no
existence of `Geometry` or `Compatibility`. The source is the current blueprint's
`prop-pur-weil-equivariance-compatibilities.proof.md`, constituent coefficient
transport, expanded by the already published module. The nearest blueprint ancestor
and via chain were checked with `blueprint_refs.py ancestor`.

The three search kinds were run again for this node. LeanSearch query
“Coefficient quotient towers for finite extensions of p adic fields and restriction
of scalars on strict semilinear sheaf systems with geometric comparison data” returned
eight results (analytic scalar restriction and ordinary scalar towers), no exact data.
LeanFinder query “Finite free coefficient system data quotient towers restriction
scalars proper open geometric comparisons” returned eight results (submersive
presentations and ordinary finite/quasi-finite algebra), no exact data. Mathlib grep
`FiniteFreeSystemRestriction|systemInclusion|quotientTransition` in CategoryTheory
returned zero results. The new node records these exact queries and result names
from searches.jsonl. The same searches in WeilConjectures yielded no matching names;
Sheaf grep found the exact published constructions in FiniteFreeSystemRestriction.
DAG grep found only the theorem node's multi-declaration record, with no definition
owner; blueprint search “finite free system” returned zero matches. Thus the node
registers existing data and writes no duplicate Lean module.

The node-to-Lean correspondence is: finite p-adic extensions and their embedding
are the explicit `l`, `E`, `L`, field/algebra/finite-dimensional binders and `i`;
positive levels are `A`, `B`, `aTransition`, `bTransition`, `levelMap`, and `sheafMap`;
the whole-system map and restrictions are `systemInclusion`, `U0`, `U`, and
`coefficientModule`; finite-type separated objects are `Spaces D`;
sectionwise identity and its adjoint normalization are `OrdinarySquare.push_section`
and `.mate`; exact localization and the two geometric mates are
`OrdinarySquare.derivedPull`, `.derivedPush`, and `.derivedOpenInv`;
invertibility and the structural coefficient map are the fields of `Geometry`;
the conditional isomorphisms are `Geometry.pushIso` and `.openIso`;
the preservation equations are precisely the identity, composition, clopen,
beta, alpha and gamma fields of `Compatibility`; compactification is `compact`
and its restriction comparison is `Geometry.compactIso`. Definitions contain real
data or specify a type of data, never an arbitrary inhabitant. The quotient
compatibility helper is the existing `levelMap_transition`, not a new sorry.

Edge cases: the node defines the data types without an existence claim, including
empty schemes and identity maps. The upper quotient uses the image of the lower
uniformizer and needs no ramification index. Index zero is exponent one; all
transition maps are retained. Maps between Spaces are arbitrary underlying-scheme
maps, and coefficients remain in universe u+1 with schemes in universe u.

## Returned delivery repair

H2 at immutable returned head `75b30eb5bce5` is repaired: the additional statement
dependency `lem-coef-finite-free-system-restriction` is replaced by the new definition
node `def-coef-finite-free-system-data`. The theorem's `Nonempty (Assertions ...)`
conclusion never occurs in the delivered signatures: `G` and `hG` are quantified
arguments, and their types and all system constructors are the registered existing
definitions. The item lean.note now explains this distinction. Its original
proof dependency on the finite-free theorem is preserved.

Comparison with the current shared node shows only the authorized `lean` change
and the one new definition dependency; the statement, proof and all original
statement dependencies are unchanged. The Lean module is unchanged from the returned
delivery, whose remaining mathematical clauses the independent reviewer accepted.
The new definition node and its full existing declarations were reread against the
source module; no mathematical or universe correction was needed. The advisory
primed k-structure and integral/system universe observations remain documented above.
