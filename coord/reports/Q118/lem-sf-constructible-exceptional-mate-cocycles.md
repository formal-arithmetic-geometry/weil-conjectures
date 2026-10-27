## Worker report

The module `Sheaf.Paper.ConstructibleExceptionalMateCocycles` states
`WeilConjectures.ConstructibleExceptionalMateCocycles.constructibleExceptionalMateCocycles`.
There is one postponed theorem, with the DAG proof expanded in its docstring. All
helper definitions contain real data: the predicates spell out equations, and
`scalarIdentification` lifts an actual ambient natural isomorphism through the
existing fully faithful inclusion. There is no choice from a bare existence theorem.

Hypothesis and clause audit:

- The finite field, algebraic closure, characteristic and coefficient prime are
  `D : FiniteFieldDatum` and `B : D.CoefficientDatum`; `B.different` is ell != p.
  `FieldStage B.l` retains a finite-dimensional field extension of `Padic B.l`;
  `Stage.finite E n` uses positive `n : ℕ+`, its valuation ring quotient and
  specified uniformizer through the existing coefficient construction.
- The four coefficient categories are the dependency's `C B.l B.Qbar X s`.
  Finite stages are actual small pro-etale finite-Tor constructible full
  subcategories; integral stages are the derived-complete category with common
  finite-reduction Tor bounds. Rational and closed stages are the existing raw
  scalar localization and common-stage categories. No category is redefined.
- `S` is the specified six-operation family, uniformly in finite coefficient field
  and positive level, as in the compositor dependency. `P,Q,R,T,U,V,IX,IY : System` retain
  the actual specified compact supports, exceptional adjoints, coefficient maps,
  etale-origin/strict-system constructions, shifts and compactification refinements.
  They are construction data of the operations named by the node, not additional
  admissibility assumptions. The existing existence results supply these systems.
- `X,Y,Z,W : SixFunctorSpace D` are finite-type schemes over the fixed algebraic
  closure; their structure maps carry the four explicit `IsSeparated` binders.
  `f,g,h` are over-base morphisms, with `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact` on each underlying map. Composites use the recorded instances.
- Compactifications `cf,cg,cx,ch,cgh,cfgh` present f,g,gf,h,hg,hgf. The identity
  compactifications are specifically `Compactification.ofIsProper (𝟙 X.obj.left)`
  and the analogous one on Y. Each of `alpha,beta,gamma,delta,unitLeft,unitRight,
  unitX,unitY : LeftCompositors` fixes finite composition by `finiteAlpha`, integral
  composition by `integralAlpha`, and the rational/common-stage normalizations.
  These present respectively (f,g), (g,h), (gf,h), (f,hg), (id,f), (f,id),
  (id_X,id_X), and (id_Y,id_Y). No arbitrary left isomorphism is substituted.
- `OperationTransposition` applies at every stage of each of the four systems.
  `Transposition` has exactly the forward equation with `eta ≫ G.map a` and the
  reverse equation with `F.map b ≫ epsilon`. `d.q.inv.app K ≫ TY.map a` is the
  transported arrow. `FieldComparison` wraps precisely the existing comparison
  with both unit/counit equations; all ring comparisons instantiate it using
  their recorded scalar shift structures, as do the recorded field comparisons.
  The categorical implication applies to any comparison with these same equations;
  in particular it applies to every specified allowed coefficient passage.
- `Composite` gives successive Hom transposition in both directions, the composite
  unit `eta_f ≫ G_f.map eta_g`, and composite counit
  `F_g.map epsilon_f ≫ epsilon_g`. Its last two equations identify the original
  unit/counit with these expressions using `exceptionalIso.inv` and `alpha`.
- The dependency defines `exceptionalIso` by `conjugateIsoEquiv` applied to
  inverse alpha. Therefore every `.inv` in this module is literally the node's
  `c_{g,f}`, rather than a chosen comparison of isomorphic objects.
- `Associative` is an unconditional conclusion at every `s : Stage B.l` for
  `alpha.alpha cf cg cx s`, `beta.alpha cg ch cgh s`,
  `gamma.alpha cx ch cfgh s`, and `delta.alpha cf cgh cfgh s` themselves.
  `U` is the system for g followed by h; `V` is the triple-composite system.
  The underlying scheme morphisms for the two triple bracketings are definitionally
  equal in this API, as the successful compile checks when `V` and `cfgh` are
  used for both `gamma` and `delta`. The functor associator is still explicit.
  Each exceptional map is the `.inv` of `exceptionalIso` for that actual left
  compositor. There is no free GH/AGH operation, no free b/c/d, and no left
  associativity premise. `AssociativityTransport` was deleted.
- `Unital` now takes the actual operations of `IX` and `IY` for identity maps
  at the specified proper identity compactifications. Its `left` and `right`
  arguments are `unitLeft.alpha` and `unitRight.alpha`; these are never replaced
  by compositors manufactured from arbitrary unit isomorphisms. The identity units
  `i,j` are existential conclusions, characterized by the actual identity-self
  compositors `unitX.alpha` and `unitY.alpha`. This characterization fixes them
  uniquely: the identity-support functor is isomorphic to the identity and hence
  whiskering by it is faithful. The next two equations assert the left unit laws
  for the actual (id,f) and (f,id) compositors. The last two equations are the
  required right identity laws for their actual `exceptionalIso.inv`, using the
  conjugate identity identifications. Thus existence and compatibility of the
  specified units are asserted, rather than assumed or supplied as free data.
- `RingCoefficient` is an unconditional conclusion for every `Allowed` ring change:
  finite quotients, integral reductions, ramified finite extension with its retained
  ramification exponent, integral scalar extension, identity and composition.
  It uses the three systems' actual `.ring.comparison` maps. At shared endpoints
  `scalarIdentification` reconciles scalar presentations through their normalized
  ambient derived scalar-extension realizations. These maps are the canonical
  full-subcategory lifts, with no faithfulness of finite evaluation assumed.
- `FieldCoefficient` states unconditional equations for the actual
  `.fields.rationalizationComparison`, `.fields.rationalComparison`, and
  `.common.commonComparison`, using the published localization, scalar and
  common-stage inclusion functors. Field reduction is not invented. Common-stage
  independence is retained by the existing System comparison cocycles.
- `SquareTransport` quantifies genuinely well-typed `TwoSquare`s and their side
  identifications. Its premise is equality of the transported original squares;
  its conclusion is equality of their transported `mateEquiv` images. Substituting
  identity or pasted comparison squares states the last clause, including all
  well-typed such equations. Mathlib's two mate-pasting laws already identify the
  mate of a paste with the paste of the mates. No square mate is asserted invertible.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`;
  its operation-stage module supplies `SixFunctorSpace` and the finite and higher
  operation fields. These bind the actual operation datum.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its public Data
  module: `WeilConjectures.ConstructibleExceptionalCoefficients.System`,
  `exists_system`, `Operation`, `Comparison`, `FieldComparison`, `C`, `Stage`,
  `RingStage`, `Allowed`, `Scalar`, and the rationalization/scalar/common functors.
  These are the recorded exceptional-inverse-image and coefficient-adjunction
  interfaces, shared by all four coefficient stages.
- `Sheaf.Paper.ConstructibleExceptionalCompositor`:
  `WeilConjectures.ConstructibleExceptionalCompositor.exceptionalIso`,
  `LeftCompositors`, `constructibleExceptionalCompositor`, `finiteAlpha`,
  `integralAlpha`. These fix the actual inverse right compositor and left maps.
- `Sheaf.SixFunctors.FiniteExceptional`:
  `WeilConjectures.FiniteExceptional.finite_exceptional`, especially its two last
  clauses, exactly the displayed finite unit/counit equations. The module is imported.
- `Sheaf.SixFunctors.RationalOperations`:
  `WeilConjectures.coef_rational_operations`, `RationalOperations.Conclusion`,
  `ExceptionalIdentification` and `ScalarCompatibility`; the preserved actual
  unit/counit identifications are the ones used by the existing System. Imported.
- The integral dependency's recorded module is
  `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`, imported as recorded.
  Its old `boundedConstructibleIntegral_rightDerivedUpperShriek` name is stale:
  the current source explicitly locates the integral exceptional theorem in
  `WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint` under
  `AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint`.
  I read that full statement/docstring and confirmed the current recorded-module
  source with `scompile.py --source`. This consumer uses the already published
  small-pro-etale coherent integral `System` interface, so it does not reference
  the stale name or reconstruct an etale integral functor. No dependency rebind is
  needed to type this consumer, and no claim of exact equality of the old etale
  interface with the pro-etale coherent construction is made.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `AlgebraicGeometry.ProEtale.originComposition` and its unit/associativity laws,
  imported for the proof. Mathlib's `Adjunction.comp`, `comp_homEquiv`,
  `comp_unit_app`, `comp_counit_app`, `mateEquiv`, `unit_mateEquiv`,
  `mateEquiv_counit`, `conjugateIsoEquiv`, `conjugateEquiv_id`,
  `conjugateEquiv_comp`, `mateEquiv_vcomp`, `mateEquiv_hcomp`, and the
  changing-adjunction mate formulas are the recorded Mathlib dependencies.
  Their full source definitions and signatures were read.
- The three proof-only nodes `lem-sf-adic-exceptional-compositor-coefficients`,
  `lem-sf-finite-exceptional-compositor-coefficients`, and
  `lem-sf-completed-shriek-composition-laws` have no recorded module in the base.
  Their statements were read; they are not needed to type these equations, so
  their absent modules are omitted. They remain genuine stage-3 prerequisites.

Edge cases checked before and during writing: empty schemes and zero objects
(the full-subcategory Hom identities still type); identity f or g (both explicit
Unital equations); minimal positive quotient n=1; quotient n=m (Allowed.identity
and coefficient units); nonflat finite quotient (no flatness binder); ramified
extension (Allowed.ramified retains en); rationalization (no reduction functor on
field categories); arbitrary common finite coefficient stage (commonComparison
and its cocycle); triple composites (explicit associator direction); independent
side functors and noninvertible original square (SquareTransport does not assume
or conclude mate invertibility). Every universe is explicitly bound; autoImplicit
is disabled. The existing universe convention is reused without forcing a small
site's object and morphism universes equal.

Searches, 2026-10-24 (raw metadata is in searches.jsonl):

- msearch LeanFinder: "Constructible exceptional adjunction coefficient change
  preserves Hom transposition and inverse exceptional compositors satisfy
  associative cocycles" returned eight categorical primitives, including
  `mateEquiv`, the two composition-conjugacy formulas and iterated mates; no exact
  geometric coefficient statement.
- msearch Loogle: "CategoryTheory.Adjunction.comp,
  CategoryTheory.conjugateEquiv_comp, CategoryTheory.mateEquiv" returned zero hits.
- msearch grep, CategoryTheory: "exceptional.*[Cc]ocycle|[Cc]ocycle.*exceptional|
  homEquiv.*comp" returned 25 related Hom/composition occurrences, not this node.
- msearch LeanSearch: "Adjunction coefficient change preserving units counits
  commutes with transposition and composition" returned eight adjunction primitives,
  including `Adjunction.comp` and `comp_unit_app`, not the geometric statement.
- rg of lean/WeilConjectures and lean/Sheaf for the item ID and
  "exceptional.*[Cc]ocycle|[Cc]ocycle.*exceptional" found finite quotient cocycles,
  smooth-purity reduction compatibility, and compactification comparisons. Reading
  them distinguishes their statements from this combination of exceptional inverse
  compositors, both transpositions, all coefficients, and arbitrary square transport.
- Direct Mathlib source reads of Adjunction/Basic and Adjunction/Mates found the
  recorded primitive definitions, which this module reuses rather than duplicates.

No statement correction, new independent notion, or disputed mathematical statement
is introduced. Helper predicates simply name the clauses of this node. All helper
and theorem declarations are listed in lean.declarations and have source docstrings.

## Second reading by Q118

The dispatcher explicitly forbids starting another agent; this is a separate self-audit,
not an independent worker review. The maintainer's delivery review supplies the
independent reading requested by the brief.

I reread the node and complete revised module against the return. Forward and
reverse transposition retain the accepted q-inverse orientations. Composite retains
both Hom maps and the rederived unit/counit equations with c = exceptionalIso.inv.
The four actual left compositors now occur in the unconditional associative clause;
I checked both paths begin at V.G and end at (T.G ⋙ Q.G) ⋙ P.G. The inverse
associator on the first path has this direction. For identity composition, I checked
that IX and IY have the actual identity morphisms, the compactifications are the
specified proper identity compactifications, and each right compositor is the mate
of unitLeft or unitRight itself. The identity units are concluded and normalized
by the identity-self compositors, with the actual left unit laws also concluded.
There are no free identity operations/isomorphisms in the theorem conclusion.
RingCoefficient, FieldCoefficient, and SquareTransport retain their accepted
statements and actual comparisons. All data remain real constructions; the one
postponed theorem is the assigned DAG node and has a full proof docstring.

## Repair of returned delivery a8f40e1493e5

H3 (all requested points): the previous associative and unit clauses were insufficient.
The conditional generic conjugation statement has been removed. Added U and V,
beta/gamma/delta, and their compatible compactifications, then asserted Associative
for the four actual exceptionalIso.inv maps with no premise. Added the specified
identity systems IX/IY and all actual identity compositors. Replaced the arbitrary
I,J,i,j clause by existence of the identity units normalized by actual identity-self
compositors, their left unit equations, and both right identity equations for the
actual (id,f) and (f,id) compositors. The accepted transposition, Composite,
RingCoefficient, FieldCoefficient and SquareTransport clauses were preserved.

The completed-shriek-laws proof node still has no Lean record on current main.
Its laws are not needed as statement parameters: this delivery directly asserts
the actual unital and associative exceptional conclusions, with their proof plan
using those completed-shriek laws. No conditional predicate takes their place.
Thus no additional postponed theorem or definition from that node is needed to
type this statement, and it remains a genuine stage-3 proof prerequisite.

Compared the retained sandbox node against current shared main: only `lean` differs;
the main module is not present on main. The old sandbox signature in the retained
node was the returned version; this repair changes its deficient clauses and updates
that signature. The delivery wrapper rebases the new commit on current main. No
source file in the read-only repository was edited and no direct git command ran.

Validation: scompile.py passed both sandbox (44.1 s) and library module (28.2 s)
checks with no errors or warnings. The exact theorem signature has been refreshed
in lean.statement, deleted AssociativityTransport has been removed from the
recorded declarations, and all module declarations are listed. The prescribed
deliver2.py --no-push run printed OK at dry-run commit 003c23015e0, passing
server preflight and per-file compilation; nothing was pushed in that run.
