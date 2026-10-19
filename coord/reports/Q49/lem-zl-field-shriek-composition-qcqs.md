## Worker report

The module `Sheaf.Paper.FieldShriekCompositionQcqs` states compact-support composition
at both field coefficient choices. All theorem proofs are `sorry`. Its definitions
are actual adjunction/composition expressions or choices from uniqueness statements;
none has postponed data.

Source read: `literature/stacks-project/more-etale.tex`,
`lemma-shriek-composition` (Tag 0F7J), its compatible tower, four displayed
identifications and common-refinement argument. Also read Bhatt--Scholze,
Definition 6.7.6, Lemmas 6.7.7 and 6.1.13 in the supplied PDF (printed pp. 43, 56).
These define separately derived proper image after exact open extension, show
constructibility/compactification independence, and show that open extension commutes
with homotopy limits. The field passage is the additional obligation explicitly
identified in the node, not attributed to the finite-torsion Stacks statement.

Hypotheses and clauses:

- The fixed finite field, its algebraic closure and characteristic are `D :
  FiniteFieldDatum.{u}`; `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` are precisely the
  coefficient-prime convention. `coefficientPrimeUnit l D hl` derives invertibility;
  it is not an extra input assumption.
- `X,Y,Z : Scheme.{u}` have `Over (Spec (.of D.k))` instances. Each structure
  morphism has `LocallyOfFiniteType` and `QuasiCompact`, the definition of finite
  type. These schemes are Noetherian and therefore quasi-separated; the node's
  quasi-separatedness restriction is automatic here. There is no `IsSeparated`
  instance on any structure morphism.
- `f : X ⟶ Y`, `g : Y ⟶ Z`, their `IsOver` instances and the `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` instances render the two separated finite-type
  morphisms over k. The composite has the inherited instances. The three
  compactifications `cf,cg,cfg` are universally quantified, so the comparisons apply
  to the choices already fixed in the compact-support definition.
- A finite extension is `E : Type u` with `Field`, `Algebra (Padic l) E`, and
  `FiniteDimensional (Padic l) E`. Its category is the recorded raw
  `sfRationalConstructibleCategory l E X`. A finite subextension of the independently
  sized algebraic closure `Ω : Type v` is `E₀ : Padic.FiniteCoefficientFields l Ω`;
  `Coefficient l Ω E₀` is its recorded small coefficient model. Thus every finite
  subfield inside the closure is covered, without equating the closure and scheme
  universes. No Karoubi completion is used.
- The integral functors are `sfCompactSupportFiniteIntegralFunctor`; the rational
  functors are `sfCompactSupportFiniteFunctor`. These are the published normalized
  Roos realization and its tensor extension, not new functors with the same objects.
  `sfFieldShriekCompositionIntegral_existsUnique` gives their actual normalized
  integral compositor. `sfFieldShriekCompositionRational_existsUnique` gives the
  natural isomorphism `F_cf ⋙ F_cg ≅ F_cfg`, with every component the localization
  of that integral component (HEq handles the definitionally distinct presentations).
  The chosen definitions select only from these uniqueness predicates.
- The compactification formula is part of `SfIntegralCompositionSpec`. For a compatible
  tower `d : Compactification g`, `e : Compactification (f ≫ d.i)`, `e.restrict.Z`
  is V, `pullback.fst e.g d.i` is b, `e.restrict.i` is c, `e.restrict.g` is p_Y,
  `e.i` is a, `e.g` is p and `d.g` is q. The relation a=bc is
  `e.restrict_i_fst`; the cartesian square is `e.isPullback_restrict`.
  `sfCompositionPullSquare` uses the canonical completed pullback compositors;
  `sfCompositionLambda` is unit--square--counit exchange followed by inverse open
  unit; `sfCompositionGamma` is exactly the open adjunct of its inverse.
  `sfCompletedCompositionOnTower` applies q, then the proper compositor, then the
  open compositor. The invertibility witnesses are existential conclusions in the
  comparison specification, not additional geometric or input hypotheses.
- For arbitrary choices of compactifications the same specification quantifies over
  every compatible common refining tower and every triple of refinement arrows.
  Its `ρf,ρg,ρfg` satisfy `SfCompletedRefinementSpec`, fixing each open adjunct by
  the proper counit/open unit and then the actual proper compositor. The equation
  conjugates the displayed tower map by precisely these refinement comparisons
  and the normalized recorded Roos realizations. Thus it specifies the canonical
  map and independence of choices; it is not just an unspecified natural isomorphism
  or an assertion about finite reductions.
- The algebraically closed category is the literal recorded `Pair l Ω X`, namely
  `generalAlgebraicallyClosedConstructibleCategory l Ω X`. The theorem
  `sfFieldShriekCompositionQbar_existsUnique` applies to every triple of the
  published normalized `SfCompactSupportCoefficientAction` constructions. Their
  existence is `sfCompactSupportFiniteFieldIndependence`. The structures fix all
  finite maps (`finite_eq`), literal output pairs (`value_eq`) and the tensor-unit
  coefficient mates (`integralBeta_spec`, `rationalBeta`); they are choices of the
  operation from the definition, not arbitrary functors or extra assumptions on K.
  Its natural isomorphism has at every `(E₀,K)` the image of the rational compositor
  under `inclusion E₀`. Naturality is on the whole common-stage category, hence on
  arbitrary representatives and arbitrary common overfields, not only inclusions
  of finite stages.

Dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum` and coefficient conventions.
- `def-weil-scheme-morphism-properties` is a convention record; its Mathlib
  `Scheme.Over`, `Hom.IsOver`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`
  notions are used directly.
- `Sheaf.Paper.IntegralRationalQbarCompactSupport`: the three unchanged
  `sfIntegralCompactSupportValue`, `sfRationalCompactSupportValue`,
  `sfQbarCompactSupportValue`, via the dependency module described below.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `Pair`, `Stage`, `inclusion`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization` (same objects and tensor Hom groups).
- `WeilConjectures.Compactification.Refinement` and `.Comp`: `Compactification`,
  `Refinement`, `restrict`, `comp`, `restrict_i_fst`, `isPullback_restrict`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the reexported actual
  coefficient ring and uniformizer constructions, and positive-level finiteness.
- The recorded finite-level declaration
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification` was read
  with `scompile.py --source WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`.
  The intrinsic realization used by the integral tower is its published equivalent
  constant-ring module presentation (`sfIntrinsicCompactSupport`,
  `sfAmbientCompactSupportCandidate`), not a redefined finite-level functor.
- Added the already landed definition nodes `def-weil-compact-support-finite-action`
  and `def-weil-compact-support-coefficient-action`, and their recorded finite-field
  independence theorem, to `stmt_deps`; the source records and complete signatures
  of their functors and normalizing structures were read.
- Added the already landed `lem-pur-compact-support-integral-coefficient-comparison`
  to `stmt_deps`. Its `PurCompactSupport.completed`, `image`, `pull`, `push`,
  `openDerivedAdjunction`, `geometricPullComposition`, `geometricPushComposition`,
  `completedPull_comp`, `refinementRestriction`, and finite reduction/image mates
  supply the actual canonical construction. The field and rational categories
  themselves are reused without alteration.

All recorded proof-dependency modules are imported. Nodes without a recorded module
(in particular integral-compactification-system-realization and formal refinement
coherence) have no import to add; they remain stage-3 proof obligations and are
explicitly named in the proof docstrings. No hypothesis standing for their conclusions
was added to the theorem. The main statement's canonical arrow is specified directly
using already published completed ringed-site adjunctions; it does not require a
new unrecorded system-map interface in its statement.

Edge cases checked: empty schemes and zero inputs are allowed; identity f or g and
identity refinements are allowed; no nonempty or nonzero input assumption appears.
The coefficient prime can be any prime distinct from p, including l=2.
Finite positive quotients are indexed by n+1 throughout; n=0 is the residue level,
not a forbidden zero exponent. Trivial coefficient extensions and arbitrary finite
stages are retained. Neither source nor target scheme must be separated over k
(e.g. the doubled-origin line is permitted). No independent site-universe equality,
finite Tor assumption, etale-origin witness input, or chosen lattice is imposed.

Searches actually run with `msearch.py Q49 lem-zl-field-shriek-composition-qcqs`:

- `leanfinder`: "Composition of compact support direct image functors on constructible
  l-adic sheaves is canonically naturally isomorphic to direct image of the composite".
  Eight hits: ordinary module pushforward/restriction and site pushforward compositors;
  none is the field-coefficient compact-support comparison.
- `loogle`: `"Shriek"`: zero hits.
- `grep`: `lowerShriek|compactSupport` in `Mathlib/CategoryTheory`: zero hits.
- `leansearch`: "For separated finite type morphisms of qcqs schemes, compact support
  direct image with l-adic field coefficients composes canonically". Eight hits on
  separatedness, finite morphisms, quasi-separatedness and finite-type composition;
  none states the sheaf operation.
- `rg` across source `WeilConjectures`, project `lean/Sheaf`, side framework and
  `dag/lean_names_upstream.json`: found the generic formal lower-shriek compositor,
  finite-level/origin compositors, and the finite integral/rational/coefficient action
  modules used here. The generic formalism needs a supplied six-functor package;
  finite-level statements have different coefficient categories. None states this node.
  `rg` for this node id in upstream returned no declaration. Exact proposed names
  were absent in the DAG name list and existing Lean.

No new definition node and no statement correction. No STATEMENT-DISPUTED flag.

## Dependency modules

`def-weil-integral-rational-qbar-compact-support`: the original record supplied only
object values. The published finite-action module supplies normalized functor maps,
but the available `PurCompactSupport.recordedIdentification` restricts the input
category to finite Tor and assumes separated structure morphisms. Those binders
cannot be supplied from this node. `Sheaf.Paper.QcqsCompactSupportRealization`
reexports the original value definitions and all their constructions unchanged,
and adds the corresponding natural realization on the full integral constructible
category without separated structure morphisms. Its predicate spells out exactly
the same actual finite scalar mates and chosen Roos projection normalization.
The theorem postpones only the proof of the uniquely specified identification;
`sfQcqsCompactSupportRealization` takes that unique natural isomorphism. No arbitrary
map or bare Nonempty choice supplies its data. Only this dependency's `lean` field
is changed.

Independent maintainer review is supplied by the dispatcher workflow; no subagent
was started, as required by the task brief.

## Validation

The prescribed `scompile.py Q49 lem-zl-field-shriek-composition-qcqs` invocation
compiled both delivered modules in dependency order, including their sandbox and
library forms, and exited successfully. No error or unexpected warning remained.
Theorems retain the stage-2 `sorry` proofs; definitions contain actual data.

`deliver2.py Q49 lem-zl-field-shriek-composition-qcqs --no-push` returned OK:
commit `978e20a83b` passed the maintainer preflight and per-file compilation.
The first preflight metadata errors were repaired: the complete primary signature
is recorded, including named arguments, and the dependency declaration list names
only declarations defined in its delivered module.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
