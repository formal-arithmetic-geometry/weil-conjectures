## Worker report

The module Sheaf.Paper.CompactSupportLimitEquationRealization states the normalized
whole-strict-tower realization equation. All definitions contain actual data. Its only
postponed theorem is compactSupportLimitEquationRealization, with the nine-step source
argument in its docstring. There is no statement correction and no disputed statement.

Hypothesis and clause correspondence:

- The finite field is `D : FiniteFieldDatum.{u}`; `l`, its primality instance,
  `E`, its finite-dimensional extension of `Padic l`, and `hl : l ≠ D.p` give the
  integral coefficient convention. `GeneratorReduction.constantRing` is O_E and
  `constantIdeal` is the uniformizer ideal. Natural index n means exponent n+1,
  so there is no zero quotient level or missing positive level.
- Scheme indices are `Over (Spec (CommRingCat.of D.k))`, so every geometric arrow
  is over k. `Expression.geometric` gives finite type and quasi-compactness at each
  vertex and the separated finite-type inverse-image/support maps.
  `SeparatedWord` additionally requires separation over k at every vertex and at
  the ambient scheme of every supplied compactification.
- `IsWord` excludes tensor constructors; the remaining constructors are the input
  (empty word), completed pull, proper push, quasi-compact open shriek, and the
  explicitly supplied compactification. A compact-support letter requires its open
  factor to be quasi-compact. No factorization is chosen in this delivery.
- `Expression.domain` retains complete constructible integral inputs, normalized
  strict reductions, compatible etale-origin witnesses (`Origins`), and common
  cohomological and Tor bounds (`LevelBounds`) at every strict intermediate
  object, including the compactification's open prefix. `IntegralDomain` explicitly
  retains the corresponding complete finite-Tor constructible integral intermediate
  objects, also including each open prefix. Every path composition retains the
  same conditions on its intermediate word.
- `GeneratorReduction.U` is exact restriction of the whole varying-coefficient
  strict system to constant-ring towers, followed by the published exact small-site
  model. `towerObject` applies this functor to the actual strict interpretation of
  the word. This is a model for tilde-W Res R(K): the single-letter identifications
  are the existing normalized `systemPullScalarIso`, `systemDirectScalarIso` and
  `systemOpenScalarIso`, recursively composed. They are normalized respectively by
  adjunction, identity on direct-image sections, and the open-adjunction mate.
  No finite evaluation is used to define a tower object or morphism.
- `GeneratorReduction.H` is exact derived Res from completed to constant scalars.
  `constantReduction`, `constantLimit`, and `rho` are the published reduction,
  derived limit of strict constant towers, and K-flat-normalized coefficient
  comparison. `reductionComparison` composes inverse rho with inverse recursive
  `Realizations.reduction`. `corner` is literally the constant completion unit
  followed by `constantLimit.map reductionComparison.hom`. The recursion being
  imported is normalized by the actual reduction-limit counit and the stipulated
  pull/proper/open reconstruction equations, not by an arbitrary corner choice.
- `Path.exchange` indexes the actual ordered proper-exchange/open-beta map
  `compactificationExchange`. Both the open and proper faces are Cartesian; the
  integral arrow is the corresponding `ringedCompactificationExchange` transported
  by the specified completion units. Thus its proper factor is the supplied mate,
  and its open factor the canonical strict open comparison.
- `Path.pullComp` uses the normalized strict pullback compositor and the actual
  ringed compositor transported by completion. `Path.refinement` uses
  `systemRefinement` (identity direct-image normalization, gamma, proper compositor,
  and equality transport) and inverse of the published unit-normalized integral
  `PurCompactSupport.refinementComparison`. The original refinement square is not
  required to be Cartesian. `Path.inverse` takes only unique inverses of isomorphisms;
  no invertibility claim beyond the node is added to the equation conclusion.
- `Path.identity`, `comp`, `expansion`, `pull`, `push`, `shriek`, and `compactSupport`
  include the empty path, finite concatenations, unfolding a supplied factorization,
  and all displayed outer operation-word whiskerings. Generator constructors accept
  an arbitrary inner expression, hence also include input-word substitution.
- `EquationLaws` first asserts that both corners are isomorphisms. Its first universal
  clause is exactly `H.map a ≫ corner_target = corner_source ≫ L.map (U.map s)`,
  in Lean's left-to-right composition order. Its second clause states that equality
  of the two actual derived constant-tower maps implies equality of the completed
  arrows. Consequently the same clause applies to every parallel refinement-exchange
  diagram and refinement cocycle path. There is no hypothesis about equality after
  finite evaluation and no faithfulness assumption on evaluation or total limit.

Dependency declarations read and used:

- Sheaf.SixFunctors.IntegralSystemExpressionDomain: Expression, evaluate, geometric,
  inputReduction, domain, Good, Origins, LevelBounds and both interpretations.
- Sheaf.SixFunctors.IntegralCompactificationSystemRealization: Realizations and its
  normalized reduction/comparison fields, compactificationExchange and
  ringedCompactificationExchange; compactOpen and compactProper.
- Sheaf.SixFunctors.IntegralSystemCanonicalBridge: CanonicalBridge.push, ringedOpen,
  ringedPullComp, ringedPushComp and Expression.completionMap.
- Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison: H, U, constantDatum,
  constantReduction, constantLimit, rho, and the normalized letter scalar comparisons.
- Sheaf.SixFunctors.SemilinearProperOpenMatePasting: sId.
- Sheaf.Paper.IntegralCompactSupportCoefficientComparison:
  PurCompactSupport.refinementComparison (uniquely open-unit normalized).
- Sheaf.Paper.SfCbcCompactSupportCompositionLimit: sfCbcSite and its normalized
  constant completion-unit/reduction/limit calculus.
- Sheaf.Paper.FiniteTorAmplitude: finiteTorConstructibleIntegral.

The original stmt_deps were read, including their full recorded signatures/docstrings:
exchangeFunctoriality, ConstantCompletion.equivalence, directImageRlimIso,
completedOpenExchangeComparison, completedCompactSupportExchange, PurityFiniteSetting,
completedReductionTower, StrictTower.Towers, completedRlim_computation and
SuppliedExchangeProjection.ExchangeProjectionStage. Their geometric, coefficient,
proper/open and strict diagram conventions are used through the more explicit existing
expression/realization declarations listed above. The landed definition owners and the three definition registrations described below
are cited in stmt_deps. The two theorem-only dependencies identified in the H2 return
are removed; no existing dependency record is altered.

Edge cases checked: an empty word is Expression.var, an empty path is Path.identity;
identity and composite refinements retain normalized proper identity/composition maps;
the zero input and empty schemes require no nonzero or nonempty assumptions; all
positive levels including n=0 (exponent one) occur; no tensor operation enters IsWord;
noncartesian refinement squares remain allowed; the unrelated noncartesian proper
base-change square is excluded by the explicit proper Cartesian face. Inverses use
IsIso certificates, never arbitrary choices or lifts of finite-level arrows.

Searches: msearch.py leanfinder, query "Derived inverse limit realization of compact
support operation words and paths commutes with completed exchange maps", returned
8 unrelated inverse-system/path results. Loogle query "NatTrans, Functor.map_comp"
returned no hits (unknown NatTrans). Mathlib grep "Path|path" in CategoryTheory/PathCategory
returned ordinary generic paths only. Project rg searches for the item id in
lean/WeilConjectures and lean/Sheaf found no existing declaration. Further rg searches
for compact-support, refinement, word reconstruction, strict-tower normalization and
constant completion found the dependency interfaces above; none states this item's
constant-coefficient path equation with the specified corners. The wrapper's exact
search responses are recorded in searches.jsonl. The source blueprint paragraph was
read under literature/blueprint/latest, together with the item's nine-step auxiliary
proof; the Stacks constituents are 0941, 099N, 07A7 and 0F7B--0F7F.

## Second reading by Q07

The dispatcher explicitly forbids starting another agent, so this is a separate second
reading by the same worker, not an independent-worker review. The initial broad
CanonicalPair interface admitted arrow kinds beyond this item and did not explicitly
expose compactification refinements. Replaced it by an explicit Path inductive with
only the displayed generators, identity factorization expansion, inverses, composition
and unary contexts. Added the proper Cartesian face and explicit integral intermediate
finite-Tor/completeness domain. Checked direction of refinement (d to c is gamma;
c to d is its inverse), order of the proper compositor, and the displayed equation.
The maintainer's independent review remains the delivery's independent review.

## Returned H2 repair

Returned immutable head: ef70cb067cb6. Compared the retained sandbox node with current
shared main: only stmt_deps and lean differed, so all current statement/source/proof
metadata is retained. Delivery wrappers reconstruct the repaired commit on current main.

1. The item no longer cites lem-sf-constant-semilinear-generator-comparison or
   lem-pur-compact-support-integral-coefficient-comparison as statement dependencies:
   it uses their existing definitions, not either theorem's conclusion. Added explicit
   definition ownership for every construction identified by the return, as listed below.
2. Added def-pur-integral-compact-support-coefficient-data directly to stmt_deps, owning
   PurCompactSupport.image/completed and their coefficient notation.
3. Covered GeneratorReduction.inverseOrZero by its own existing-definition node. The
   original definition's data remains the classical if-IsIso inverse/zero branch.
4. Addressed the advisory by deleting `IsIso s ∧ IsIso a ∧` from EquationLaws. The
   conclusion now states precisely the square and parallel-path cancellation. Path.inverse
   still requires IsIso certificates, as it must to represent an inverse path. The two
   corner-isomorphism clauses remain, since the node explicitly calls the corners isos.

## New nodes

`def-sf-constant-completed-reduction-transport` registers existing:true in
Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison. It owns constantRing,
constantIdeal, constantDatum, ordinaryH/H, ordinaryU/U, constantReduction,
constantLimit, their strict/ordinary tower helpers, RhoNormalized and rho. Its statement
specifies exact scalar restriction and the whole-K-flat-representative normalization of
rho. The choice uses rho_existsUnique, which determines the isomorphism uniquely; it is
not data from an undetermined existence assertion. It follows the coefficient constituent
of the current blueprint and Stacks 0941, 06YY, 07A4 and 099N. The main generator-comparison
theorem is not asserted or owned by this definition node.

`def-sf-integral-support-refinement-comparison` registers existing:true in
Sheaf.Paper.IntegralCompactSupportCoefficientComparison. It owns geometricPushComposition,
refinementPull, refinementRestriction, refinementProperOpen and refinementComparison.
Its statement records the proper compositor and open-unit/proper-counit normalization
that uniquely determines gamma, followed by the actual inverse-gamma/proper-image formula.
It follows the blueprint compact-support constituent and Stacks 03D8, 0D6D and 0F7B--0F7D.
The coefficient-comparison theorem's conclusion is not used or owned by this definition.

`def-sf-comparison-inverse-or-zero` registers existing:true in
Sheaf.SixFunctors.GeneratorReductionStatement and owns inverseOrZero. It states its
literal ambient total definition (unique inverse if invertible, zero otherwise), including
arbitrary object and morphism universes; it introduces no extra invertibility assertion.
It is the ambient inverse convention of the normalized completion comparisons in the
blueprint constituent proof.

Each new node includes the exact searches performed with the launcher wrapper: LeanSearch
for normalized constant/completed strict reduction (8 unrelated algebraic normalization
hits), LeanFinder for normalized refinement (8 unrelated topological adjunction hits),
Loogle CategoryTheory.inv (the ordinary inverse only), and Mathlib grep
inverseOrZero|RhoNormalized|refinementProperOpen (no hits). Repository and Sheaf rg found
precisely the existing constructions. DAG searches found theorem-only ownership and uses,
with no definition owner. Blueprint searches returned general coefficient/refinement
notions, not these normalized helpers. Therefore these nodes register the existing
constructions without duplicate definitions or new Lean modules.

## Second reading by Q07 (repair)

Reopened the retained item, its EquationLaws, all three new nodes, and their existing
source definitions. Checked H/U are exact scalar restrictions, constantDatum uses the
actual uniformizer, and rho is uniquely pinned by RhoNormalized before any path equation.
Checked refinementComparison is inverse proper composition then proper pushforward of
inverse refinementProperOpen, whose unique transpose condition is the open unit. Checked
inverseOrZero is the actual existing total definition. Removed both theorem-only stmt_deps,
added the three definition nodes and image/completed's existing definition owner, and
removed the advisory's extra IsIso conclusion. The item statement and its geometric,
coefficient, complete/finite-origin/amplitude domains, corner formula, path generators,
whiskering, and strict-map equality/cancellation conclusions are unchanged. No subagents
were started, as the dispatcher forbids them; the maintainer provides independent review.
