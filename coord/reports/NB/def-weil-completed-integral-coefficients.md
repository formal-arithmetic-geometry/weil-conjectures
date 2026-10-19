## Worker report

The module `Sheaf.Paper.CompletedIntegralCoefficients` defines the constant finite
coefficient ring sheaves, their reduction sequence, its inverse limit and projections,
the completed-coefficient module category and its derived category, cohomology objects
of cochain complexes, and restriction along each projection. All data are explicit
applications of the dependency constructions and Mathlib. There are no postponed
proofs, new axioms, or `sorry` terms in this definition module.

Hypothesis and clause correspondence:

- The global finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{d}`.
  The main definition takes this datum explicitly. `l : ℕ` with `[Fact l.Prime]`
  fixes the prime, and its explicit `_hl : l ≠ D.p` enforces the required distinction
  from the characteristic. Subsequent definitions use the same `D` and `hl`.
  The finite rings and their constant sheaves do not need the finite-field context;
  their helper definitions therefore work before this convention is imposed.
- `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` are exactly a finite extension of the l-adic field.
  The ring of integers, uniformizer, quotient rings, and reductions are the recorded
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, and `coefficientExtensionTransition`, rather than
  independently chosen objects.
- Positive integers are represented by `n : ℕ` with exponent `n + 1`.
  Thus `integralCoefficientSheaf ... 0` has coefficient ring `A_{E,1}`.
  `integralCoefficientSheafTransition ... n` uses the recorded ring reduction
  at exponent `n+1`, from `A_{E,n+2}` to `A_{E,n+1}`.
- `Y : AlgebraicGeometry.Scheme.{t}` is arbitrary. Its site is exactly the recorded
  dependency's `Scheme.ProEt Y` with `Scheme.ProEt.topology Y`.
- `integralCoefficientSheaf` applies `constantSheaf` to the quotient commutative
  ring and then `sheafCompose` with `forget₂ CommRingCat RingCat`. This is the
  same constant-ring construction as `Scheme.proEtaleDerivedCategory`, with the
  coefficient size enlarged when needed. `constantSheaf` is defined as the constant
  presheaf followed by `presheafToSheaf`, as required by the node.
- Coefficients use `ULift.{t+1}` into `Type (max u (t+1))`. The lifted reduction is
  `ULift.ringEquiv.symm.toRingHom.comp (reduction.comp ULift.ringEquiv.toRingHom)`.
  It is the original quotient reduction under canonical ring equivalences.
  Functoriality of `constantSheaf` and `sheafCompose` supplies the sheaf map.
- `integralCoefficientSheafSystem` uses `Functor.ofOpSequence` to obtain the
  full `ℕᵒᵖ` diagram from the successive reductions. Its identities and composites
  are those of that existing constructor, with no extra coherence hypotheses.
- `completedIntegralCoefficientSheaf` is literally
  `limit (integralCoefficientSheafSystem l E Y)` in sheaves of rings.
  `completedIntegralCoefficientProjection ... n` is its `limit.π ... (op n)`.
  Existence follows from the existing limits on ring sheaves. No surjectivity
  statement about these projections is included.
- `completedIntegralModuleSheaves` is the dependency's `ringedSiteModules` of
  that completed sheaf. Thus it is exactly `SheafOfModules` of the inverse limit,
  with Mathlib's inherited category and abelian structure. It is not the category
  for the discrete constant valuation ring.
- `completedIntegralDerivedCategory` is `DerivedCategory` of this module category,
  using `HasDerivedCategory.standard`. This is localization of cochain complexes
  at quasi-isomorphisms, as in the abstract-derived-category dependency.
- `completedIntegralCohomology` takes any cochain complex of these modules and
  any `r : ℤ`, returning `K.homology r`, the abelian-category cohomology object.
  No claim is made about a different cohomology theory or different t-structure.
- `completedIntegralRestrictScalars ... n` is exactly the recorded
  `SheafOfModules.restrictScalars` applied to the limit projection. Its source
  is the category of modules over the finite constant quotient ring sheaf;
  its target is modules over the completed sheaf. Exactness is not asserted here.

The three size helpers do not introduce mathematical hypotheses or postponed
statements. They apply existing Mathlib terms: `essentiallySmallSelf`,
`hasSheafifyEssentiallySmallSite`, and
`GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`. Mathlib's
ordinary concrete sheafification instances use the site's exact universe, so the
helpers transport these instances through its small model in the larger coefficient
universe. The original site still has object universe `t+1` and morphism universe
`t`; neither is identified with the coefficient-field universe. The `letI` terms
occur only in instance bodies, not in statement signatures. These are direct
applications of established instance transports, not new mathematical proofs.

Dependency declarations used and inspected:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  prime/characteristic conventions.
- `Sheaf.NumberTheory.Padics.CoefficientExtension` (publicly imported through
  `FiniteFieldFiber`): `Padic.coefficientExtensionRing` and
  `Padic.coefficientExtensionTransition`; the definitions reduce to the recorded
  valuation ring and powers of the ideal generated by the recorded uniformizer.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; its full local and current
  server source were read to retain its exact site and constant-sheaf encoding.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`, retaining the inherited abelian structure.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`:
  `SheafOfModules.hasLimitsOfShape` and
  `SheafOfModules.evaluationPreservesLimitsOfShape` for module limits;
  `Mathlib.CategoryTheory.Sites.Limits`: `Sheaf.createsLimits` and
  `Sheaf.hasLimitsOfSize`, with `CategoryTheory.Limits.limit` and `limit.π`,
  for the ring-sheaf case in the repaired dependency record.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`; cochain-complex homology
  is the existing `HomologicalComplex.homology` from this import closure.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, whose source, target, object formula, and
  additive instance agree exactly with the node's final clause.

Edge cases checked before finalizing: the lowest index is exponent one; exponent
zero is never a term of the sequence. The scheme may be empty, and no nonempty,
connected, finite-type or separated hypothesis is imposed on it. Every integer
cohomological degree is permitted. The extension may have degree one or be ramified;
its transitions are the original quotient maps in every case. Independent site,
field and global-datum universes remain independent. No nonzero or surjectivity
hypothesis on the completion is used. Ring-sheaf limits remain valid for the zero
ring on an empty site. The coefficient convention excludes only `l = D.p` as the
node requires.

Searches for an existing definition:

- `msearch.py ... leanfinder "inverse limit of constant finite quotient ring sheaves
  completed integral coefficient sheaf"`: eight hits, concerning `AdicCompletion`
  and de Rham period rings, none for ring sheaves on a pro-etale site.
- `msearch.py ... loogle "constantSheaf, limit, SheafOfModules.restrictScalars"`:
  zero hits; the service reported unknown identifier `constantSheaf`.
- `msearch.py ... grep "completedIntegral|coefficientExtension|adic.*Sheaf"`:
  ten hits, principally `Scheme.ellAdicSheaf`. That declaration is an abelian-group
  sheaf for Z_l, not the required ring sheaf for arbitrary finite E.
- `msearch.py ... leansearch "inverse limit completed integral coefficient sheaf
  on pro etale site"`: unavailable, service Internal Server Error; no verdict is
  inferred from this failed search.
- `rg -n "completedIntegral|coefficientExtension|def-weil-completed-integral-coefficients"`
  in upstream `WeilConjectures` and project `lean/Sheaf`: the coefficient extension
  declarations and their consumers, no completed-ring-sheaf construction.
  The upstream node-id search found no declaration. The finite-field, pro-etale,
  module-sheaf, inverse-limit and change-of-rings source modules were then read
  directly. New declaration names were checked against those sources.

Validation: every server compile uses `scompile.py`, nice 19, two threads, the
60-second per-file limit. The final module compiled without errors or warnings
in about three seconds. The delivery dry run is recorded separately by its tool
output. No statement correction or statement dispute is needed.

## Dependency modules

`def-pur-sheaf-inverse-limit`: lean-only repair to existing Mathlib declarations;
no new module. Its old `mathlib_match` named only `SheafOfModules.hasLimitsOfShape`,
which does not type a limit of ring sheaves, although its statement explicitly
includes rings. Its new primary declaration is the existing
`CategoryTheory.Limits.limit`, with `limit.π` recorded alongside. Module-sheaf limits and sectionwise
preservation, and general sheaf `createsLimits`/`hasLimitsOfSize`, supply the
instances for its two specializations.
For ring values the latter instances compute limits as limits of underlying
presheaves, hence sectionwise; the standard ring-limit instances supply the value
category. The definition is the same categorical limit for all cases of the node.
Only `lean` was changed; its statement and Mathlib match remain intact.

## Second reading by NB

I independently read the sandbox node and all twelve declarations in
`Sheaf.Paper.CompletedIntegralCoefficients`, the seven dependency node statements
and their recorded interfaces, the blueprint source at order 1455, and Stacks
`sites-modules.tex`, Lemmas `lemma-limits-colimits-abelian-sheaves` (03CO) and
`lemma-limits-colimits` (03DB). The source introduces an arbitrary scheme, not
necessarily a finite-type geometric fibre. The node already separates the
construction from the source's surjectivity claim and correctly calls the ring
sheaf category a category, rather than an abelian category. No additional global
source hypothesis is needed for this definition.

Object/hypothesis/clause checklist, with the Lean rendering and verdict:

1. Global finite-field datum, prime l different from p: `D : FiniteFieldDatum.{d}`,
   `l : ℕ`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` in the main definition;
   subsequent constructions retain `D hl`. I opened `FiniteFieldFiber.lean`:
   `D.p` is the prime in the stated finite-field tuple. Match.
2. Arbitrary finite extension E of Q_l, valuation ring, chosen uniformizer,
   positive-power quotients and their reductions: `E : Type u`, `[Field E]`,
   `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`, and the imported
   `Padic.coefficientExtensionRing` / `coefficientExtensionTransition`. I opened
   their definitions in `CoefficientExtension.lean`: the former is the quotient
   by the power of the singleton-generated uniformizer ideal; the latter is
   `Ideal.Quotient.factor` for successive powers. No extra norm, embedding into
   an algebraic closure, or finiteness instance on E is assumed. Match.
3. Every positive exponent n: Lean's index `n : ℕ` denotes exponent `n+1`.
   `integralCoefficientSheafTransition ... n` applies the dependency transition
   at `n+1`, giving exponent `n+2` to exponent `n+1`. All positive exponents
   occur, once each. Match.
4. Arbitrary scheme Y and its small pro-etale site: `Y : Scheme.{t}` and
   `Scheme.ProEt.topology Y`. I opened `ProEtaleDerivedCategory.lean` and the
   framework inventory `coord/pefw-upstream-framework.md`; the same recorded
   small site and constant-CommRingCat-then-forget encoding are used. Match.
5. Constant ring sheaves, their module categories, and reduction sheaf maps:
   `integralCoefficientSheaf` applies `constantSheaf` in CommRingCat and
   `sheafCompose` with `forget₂ CommRingCat RingCat`; Mathlib defines
   `constantSheaf` as constant presheaf followed by `presheafToSheaf`.
   `integralCoefficientSheafTransition` applies these functors to the quotient
   map conjugated by `ULift.ringEquiv`. The finite-level module category is
   `SheafOfModules (integralCoefficientSheaf ... n)`, explicitly present as the
   source of `completedIntegralRestrictScalars`. Match.
6. The entire inverse system, inverse limit in ring sheaves, and projections:
   `integralCoefficientSheafSystem` is `Functor.ofOpSequence` of the reductions;
   its constructor produces the composites and identities. The completion is
   literally `limit` of this diagram and the projections are `limit.π ... (op n)`.
   No arbitrary cone or arbitrary map replaces either construction. Match.
7. Abelian category of modules over that limit, rather than over the discrete
   constant O_E: `completedIntegralModuleSheaves` is `ringedSiteModules` applied
   to `completedIntegralCoefficientSheaf`. I opened `RingedSiteModules.lean`:
   it is precisely `SheafOfModules` with the inherited category and abelian
   instance, not a different module notion. Match.
8. Derived category as localization of cochain complexes at quasi-isomorphisms:
   `completedIntegralDerivedCategory` uses `DerivedCategory` of exactly that
   module category with `HasDerivedCategory.standard`. The definitions in
   Mathlib's `DerivedCategory.Basic` localize the integer-indexed cochain
   complexes at `HomologicalComplex.quasiIso`. Match.
9. Cohomology of any complex in every integer degree: `completedIntegralCohomology`
   takes `K : CochainComplex (completedIntegralModuleSheaves ...) ℤ`, `r : ℤ`,
   and returns `K.homology r`. This is the abelian-category kernel/image quotient
   in the node, without a boundedness or constructibility assumption. Match.
10. For each positive level, restriction from finite-level modules to completed
    modules along the canonical projection: `completedIntegralRestrictScalars`
    is `SheafOfModules.restrictScalars (completedIntegralCoefficientProjection ... n)`.
    I opened `ChangeOfRings.lean`: its direction is modules over the target ring
    to modules over the source ring, preserving the underlying abelian sheaf.
    There is no additional exactness or surjectivity claim. Match.

Universes and edge cases: `d`, `t`, `u` are independently bound; site objects
remain in universe `t+1` and morphisms in `t`. `ULift.{t+1}` puts the original
quotient in coefficient universe `max u (t+1)` via an actual ring equivalence.
The three public instance helpers are direct applications of existing Mathlib
small-model transports (`hasSheafifyEssentiallySmallSite` and
`WEqualsLocallyBijective.ofEssentiallySmall`), whose signatures and surrounding
assumptions I read in `Sites.Equivalence`. They impose no new hypothesis. There
is no free variable or universe, file-local notation, private definition, or
file-local instance. The index zero is exponent one, not the zero coefficient
ring at exponent zero; no positive level is lost. The indexing diagram is the
specified nonempty sequence, so an empty indexing set is not an input here.
The empty scheme and zero module/zero complex are allowed. All cohomological
degrees, l = 2, the degree-one extension, and ramified extensions are included.
The only characteristic exclusion is the node's l different from D.p.

Independent existence searches used different wording from the first reader:

- LeanFinder via `msearch.py`: `adic completion sheaf of rings constant quotient
  inverse sequence`; eight adic-completion algebra/module hits, no site-valued
  completed coefficient construction.
- Loogle via `msearch.py`: `SheafOfModules.restrictScalars`; four hits, including
  the exact scalar-restriction functor and its additive instance, read directly.
- Grep via `msearch.py`: `padicIntegersSheaf|completed.*Coefficient|integralCoefficientSheafSystem`;
  no indexed hit. Independent `rg` searches of the upstream WeilConjectures,
  Mathlib AlgebraicGeometry, and project Sheaf sources for completion and
  inverse limits of constant coefficients found ingredients, not this definition.
- LeanSearch via `msearch.py`: `sheaf of rings inverse limit constant quotients
  valuation ring`; service unavailable (Internal Server Error), not negative
  search evidence.
- In addition I read the newer framework's exact
  `AlgebraicGeometry.ProEtale.padicIntegersSheaf` declaration in the group clone's
  `lean/WeilConjectures/CategoryTheory/RingObjects/EllAdic.lean`. It is a
  `continuousMapRingSheaf` for `PadicAlgCl.integers`, assumes an embedding
  `Algebra E (PadicAlgCl l)`, and fixes E in `Type`. It supplies neither this
  diagram of quotients nor its canonical limit projections. Identifying its
  continuous-function construction with the required inverse limit needs a
  comparison theorem; it is not an exact existing declaration for this node.
  This also refines the first report's search discussion: the newer framework
  does have integral ring sheaves, although no exact match for this construction.

Dependency repair review: there are no new nodes or dependency modules. The
`def-pur-sheaf-inverse-limit` delta changes only `lean`. I read its full node
and its Stacks sources. The old `SheafOfModules.hasLimitsOfShape` record cannot
serve the ring-sheaf clause. The replacement `CategoryTheory.Limits.limit` and
`limit.π` are the existing categorical constructions for both specializations.
I checked the sectionwise module limit/evaluation instances in
`ModuleCat.Sheaf.Limits`, and `Sheaf.createsLimits` / `hasLimitsOfSize` in
`Sites.Limits`: ring-sheaf limits are created in presheaves, whose limits are
pointwise. Thus the repair preserves the full notion and does not introduce a
second inverse-limit definition. No statement correction or citer audit is
required.

Mismatches and changes: no mathematical or Lean mismatch was found. I preserved
the correct module and node records. The second reading adds the independent
clause audit and the newer-framework search distinction to this report. Every
definition has real data; the module contains no theorem, axiom, or sorry.
All declaration docstrings identify order 1455 and this blueprint node; there
are no postponed proof steps because this is a definition node.

Validation: reran `scompile.py NB def-weil-completed-integral-coefficients
lean/Sheaf/Paper/CompletedIntegralCoefficients.lean`. It compiled cleanly on the
server in 3.1 seconds with nice 19, two threads and the 60-second per-file limit;
its three side dependencies also compiled cleanly. The primary `lean.statement`
is verbatim the definition's written signature, and all twelve delivered
public declarations are listed in `lean.declarations`.
