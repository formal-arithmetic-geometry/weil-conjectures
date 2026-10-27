## Worker report

Delivered module: `Sheaf.Paper.LisseLatticeHeartLift`; main declaration:
`WeilConjectures.LisseLattice.lisse_lattice_heart_lift`.
It states the lattice existence and the unique specified rationalized local lifts.
There is one postponed theorem, with the node's nine-step proof plan in its docstring.
Every helper has real data, or is a structure/predicate explicitly spelling out the
objects and comparisons named in the item. No helper theorem, arbitrary map, chosen
nonunique object, or new independent mathematical notion is introduced.

Hypotheses and coefficient objects:

- The finite-field datum is `D : FiniteFieldDatum.{u}`. The prime is `l` with
  `[Fact l.Prime]`, and `hl : l ≠ D.p`. The finite coefficient field is
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]`. Its ring and uniformizer are the recorded
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`.
  As with the recorded coefficient dependency, the abstract finite extension is used;
  no extra choice of embedding in the algebraic closure affects this assertion.
- `X : LisseRealization.Base D l hl` is exactly a scheme over `Spec D.k` whose
  structure map is locally of finite type and quasi-compact. Its definition adds no
  separation condition. The inherited `LisseRealization.baseInvertible` supplies
  the residue-field unit instances required by the recorded lisse predicate; these
  are consequences, not new hypotheses.
- `B_X` is `completedIntegralCommRingSheafUnrestricted l E X`, with the ordinary
  module category `integralTowerModules`, definitionally the recorded
  `scalarReductionSource` in these universes. Finite levels have exponent `n+1`.
- The literal `A_X` is `WeilConjectures.LisseLattice.rationalRing l E X`: the item-owned
  specialization of `ringedLocalizationRingOfUniverses` at `uniformizerSection`.
  The latter is the image of the constant uniformizer through the recorded
  `integralConstantToCompletionOfUniverses`; `coefficientMap` is the corresponding
  `ringedLocalizationRingUnitOfUniverses`. All three are concrete definitions.
  `RealizationAt.completion` identifies B with the continuous integral presentation,
  normalized by `residues` at EVERY finite projection. `localization` identifies
  literal A with `rationalCoefficientSheaf`; `localization_unit` is the equation
  from B to A. Thus the displayed tensor functor is extension along the specified
  localization, expressed after an equivalence of coefficient presentations.
  Quantifying over all modules in the continuous presentation is equivalent to
  quantifying over all literal A-modules, by restriction along this ring isomorphism.
- `RationalModules` is the existing ordinary `pbcModules` category, not a category
  of constructible or lisse modules. `DerivedCategory` is the ordinary unbounded
  derived category. `RealizationAt.integral` identifies Q followed by J with the
  inclusion followed by the actual `pbcDerivedExtend`. `fractions` gives exactly
  the node's formula on every pure tensor (scalar-first order, as in raw Q).
  `RealizationAt` deliberately has no full-faithfulness, degree-zero image,
  lattice-existence, or rational-lisse-image field. In particular the full existing
  `LisseRealization.At` is NOT an assumption.
- `Realizations` bundles these canonical presentations and the ordinary etale
  tensor restriction comparisons. The equation `balance_sections` fixes the latter
  on pullbacks of every pure tensor, so it is not an arbitrary natural isomorphism.
  Existence of this data is asserted in the conclusion; the lattice assertions hold
  for every normalized presentation. These auxiliary choices express the canonical
  constructions in the question rather than assume a realization theorem.
- The sole sheaf hypothesis is `L.IsFiniteLocallyFree`. The existing definition uses
  locally free local-generators data with finite index sets on each cover member;
  it allows different ranks and empty index sets.

Every clause of the conclusion:

1. `Nonempty (Choice l E a X.scheme L)` gives N, alpha, the index type I,
   the family `Y : I → X.Etale`, its covering condition `cover`, and
   `quasiCompact : ∀ i, QuasiCompact (Y i).hom`, followed by M_i, their
   `IsFiniteLocallyFree` condition, and beta_i. No finite or nonempty index type
   is imposed. In particular the empty scheme is not excluded.
2. `Choice.constructible` is exactly
   `IsIntegralStratifiedFinitelyPresented X (pbcIntegralDatum l E)` applied after
   `pbcRestrict (purCoefficientIso ...).hom`. That existing predicate explicitly
   uses a finite locally closed stratification and a pro-etale covering sieve on
   each stratum, with completed-constant realizations of finitely presented
   R-modules. It permits torsion. The normalized PBC-to-B comparison is existing.
3. `alpha` has source `(pbcExtend (completion.hom ≫ integralRationalCoefficientMap)).obj N`.
   Each `beta i` has the same source with M_i on Y_i and target the ACTUAL ordinary
   pullback of L. `pbcExtend` is sheaf tensor extension, not a completed tensor.
4. `∀ c : Choice ..., c.Assertions ...` is essential: it covers EVERY choice of
   N, alpha, charts, M_i, beta_i, rather than only one constructed collection.
   `Assertions` first quantifies `hN : sfIntegralConstructible ... (single N)`.
   Its local clauses quantify `hNi` for the ordinary restriction of N and `hMi`
   for M_i. Thus integral membership is a conclusion, not a precondition in Choice.
5. The first conjunct is the exact recorded `sfRationalHeartProperty` on Q(N[0]).
   `singleComparison` is a concrete arrow from J(Q(N[0])) to the single complex
   of ordinary scalar extension: the integral natural isomorphism, followed by
   `pbcComplexCounit`, followed by `mapCochainComplexSingleFunctor`. Its `IsIso`
   assertions express the actual degree-zero identifications; an unrelated
   choice of degree-zero isomorphism is not used.
6. `integralPull` is actual ordinary inverse image followed by tensor along the
   completed coefficient map. This coefficient map is constructed from the
   existing `completedCoefficientMap` and normalized `purCoefficientIso` on each
   side. On the etale charts this is precisely N restricted to Y_i. It is not
   replaced by a generic completed pullback object without a restriction map.
7. `Choice.specified` is `(a.balance ...).symm` followed by the ordinary pullback
   of `alpha` followed by `(beta i).symm`. Its direction is from A⊗N|Y_i to A⊗M_i,
   namely beta_i inverse after alpha restricted. The balanced comparison is the
   previously normalized pure-tensor comparison.
8. The local clause is `∃! e : Q(N|Y_i[0]) ≅ Q(M_i[0]), ...`. Its first equation is
   `J.map e.hom ≫ comparison_M = comparison_N ≫ single.map specified.hom`.
   Its second equation is the corresponding equation for `e.inv` and
   `specified.inv`. They assert equality of derived morphisms, rather than just
   equality on cohomology, existence of an unspecified isomorphism, or equality
   after forgetting module structures. Since the comparisons are isomorphisms,
   these equations say exactly what the images under J are. Requiring the inverse
   equation does not weaken uniqueness: it is forced by the first for an isomorphism.
9. The final conjunct is the exact existing `IsRationalLisse` predicate on Q(N[0]).
   Together with the earlier standard-heart conjunct this is the prescribed lisse
   rational heart. There is NO `N.IsFiniteLocallyFree` field or assertion.

Dependency declarations used (publicly imported directly or by the named public
reexports):

- `Sheaf.Paper.RationalLocallyFree`: `WeilConjectures.IsRationalLisse`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeartProperty` and its integral
  and rational standard-class definitions.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`, `scalarReductionSource`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalCoefficientEquiv`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its reexports:
  completed integral Ring/CommRing sheaves, finite projections, constant map.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its reexports:
  the finite extension ring, valuation ring and uniformizer.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the exact
  `SheafOfModules` category. `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`.
- The scheme-properties dependency is a convention record, not a declaration;
  the named notions `Scheme.Over`, `LocallyOfFiniteType`, `QuasiCompact`, and
  `Etale` are used through `LisseRealization.Base` and `Scheme.Etale`.
- `Sheaf.Paper.LisseRationalRealizationData`: `Base`, `baseInvertible`,
  `coefficientPull`, `ordinaryPull`. Only these infrastructure declarations are
  used; neither `At` nor the realization theorem is assumed.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`:
  `ringedLocalizationRingOfUniverses` and `ringedLocalizationRingUnitOfUniverses`,
  owned by `def-weil-pbc-ringed-section-localization`. Together with the recorded
  completed-constant map, these define the item-owned `uniformizerSection`,
  `rationalRing` and `coefficientMap`. `SmoothLisseIntegralLattice` is no longer
  imported or cited as a statement dependency.
- `Sheaf.Paper.IntegralStratifiedPerfectModels`:
  `IsIntegralStratifiedFinitelyPresented`, owned by
  `def-weil-pbc-integral-stratified-perfect-models`. The characterization theorem
  remains a proof dependency, not an owner of this definition.
- `Sheaf.Paper.IntegralCoefficientCompletenessTransport` (public in
  `CompletedCoefficientPresentationTransport`): `purCoefficientIso`, whose
  Ring-level image is `integralDetailedCoefficientComparison`.
- `Sheaf.Paper.BoundedConstructibleTower`: `pbcModules`, `pbcRestrict`, `pbcExtend`,
  `pbcDerivedExtend`, `pbcComplexCounit`, `pbcTensorSection`.
- `Sheaf.Paper.ContinuousRationalDerivedRealization`: `ContinuousRational.modulePull`,
  `moduleUnit` and the constant-section E-action on rational modules and derived Homs,
  owned by `def-per-continuous-rational-realization-data`. The existence theorem
  is not cited as the owner of these definitions.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`, with rank permitted to vary.

The six additional statement dependencies are already existing, recorded definition
nodes owning these construction interfaces. Their dependency closures were checked: none
returns to this item. No dependency record is repaired and no new node is required.
The proof-dependency imports are retained as the stage-3 plan. The currently unstated
`lem-tw-lisse-localization-restriction` has no recorded Lean module to import; this
module uses the actual coefficient, ordinary tensor, and normalized restriction
interfaces directly, so it needs no assumption of that unstated theorem.

Searches for an existing declaration:

- `msearch.py ... leanfinder "A finite locally free rational coefficient sheaf has a
  constructible integral lattice and its chosen local isomorphisms lift uniquely to
  rational constructible heart objects"`: eight hits, including finite generators,
  finite presentation and `Condensed.finFree`; none states this lattice/heart/lift result.
- `msearch.py ... loogle "SheafOfModules, IsLocallyFree"`: no hits; Loogle reported
  unknown identifier `IsLocallyFree` in that query.
- `msearch.py ... grep "IsLocallyFree|IsFiniteLocallyFree"
  Algebra/Category/ModuleCat/Sheaf`: hits in the ordinary Mathlib locally free API,
  no rationalized constructible lattice theorem.
- `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `lisse.lattice.heart|LatticeHeart|latticeHeart`; and `grep -rn` in
  `lean/WeilConjectures` for the item id: no exact result. Existing global and
  etale-local lattice modules were read, but neither has the specified unique
  rationalized lifts or the full target statement.
- The declared namespace and theorem name were checked in `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declarations.

The source PDF was read locally using `pdftotext`: 6.8.3 defines finite locally free
lisse modules, 6.8.4(6) gives etale-local integral lattices, 6.8.10 permits finitely
presented integral local models, 6.8.11(3) gives degree-zero constructibility,
6.8.13 gives the global constructible (not necessarily lisse) lattice, and
6.8.14(2) supplies the rational Hom comparison. These support the node as written.

Edge cases checked: empty X and an empty chart family; rank zero; different ranks
on different components; nonseparated finite-type schemes; nonreduced schemes;
torsion allowed in the constructible integral lattice; arbitrary alpha and beta,
including rescaling by powers of the uniformizer. No monomorphism N→L or global
integral local freeness is accidentally imposed. The uniqueness condition concerns
rational isomorphisms, so integral t-power torsion does not invalidate it.
All universes and variables are explicitly bound with `autoImplicit false`.
The small pro-etale site retains object universe u+1 and morphism universe u;
coefficients/modules use the common u+1 lift already fixed by the dependencies.

Validation: `scompile.py Q39 lem-tw-lisse-lattice-heart-lift <module>` passed both
sandbox and library-name compilation with no errors or warnings after the line-width
repairs. No local/global library build was run. No statement dispute or statement
correction is needed.

## Second reading by Q39

A second self-reading checked the node and module clause by clause, especially
quantification over every lattice choice, orientation beta inverse after alpha,
uniqueness as an isomorphism, the inverse-image equation, rank zero and varying
ranks, the completion/localization normalization, and the absence of separation
or global integral local-freeness assumptions. It found no remaining mismatch.
Compiler-directed repairs qualified the two overloaded coefficient declarations,
renamed the reserved field name `at` to `realization`, and shortened three lines.
The dispatcher's explicit instruction prohibits starting another agent; this is
therefore a self-reading, not a claimed independent review. The maintainer's
independent delivery review remains required.


## Returned-delivery repair

The maintainer independently checked immutable head `ef8b99d83999` and accepted the
mathematical statement and all of its clauses. This repair addresses exactly its
three H2 ownership findings:

1. Replaced `lem-per-continuous-rational-derived-realization` in `stmt_deps` with
   `def-per-continuous-rational-realization-data`, whose record explicitly owns
   `ContinuousRational.modulePull`, `moduleUnit`, and the coefficient actions.
   Its module is now also an explicit public import. No realization theorem is
   assumed or added to the statement.
2. Replaced `lem-weil-pbc-integral-stratified-perfect-characterization` in
   `stmt_deps` with `def-weil-pbc-integral-stratified-perfect-models`, which owns
   `IsIntegralStratifiedFinitelyPresented` in the already imported Models module.
   The original characterization proof import and the constructibility predicate
   are unchanged.
3. Removed `lem-a1-smooth-lisse-integral-lattice` from `stmt_deps` and removed its
   module import. Added `def-weil-pbc-ringed-section-localization`. The item now
   defines its own `uniformizerSection` by the recorded constant-to-completion
   map, then `rationalRing` and `coefficientMap` by the recorded ring localization
   constructor and its unit. `RealizationAt.localization` and `localization_unit`
   use these exact concrete constructions. The three helper names are listed in
   `lean.declarations`, and their docstrings name this item and BS 6.8.2.

Compared the retained sandbox node with current shared main before editing: only
`stmt_deps` and `lean` differed; all other node fields matched. This repair retains
all other node fields and the complete theorem signature and assertions. The
wrapper rebases the repaired delivery onto current main; no direct Git mutation
or shared-source edit was performed. There is still exactly one `sorry` theorem.
No new definition node, dependency-module repair, or statement correction is needed.

A second self-reading of the repair checked all three replacements against the
current owning nodes and their full declarations. The direct rational ring and
unit definitions unfold to the same section-localization construction used before,
with the same coefficient size u+1 and site object/morphism universes u+1/u.
The previous independent maintainer review supplies the mathematical clause review;
no claim of a newly spawned independent reviewer is made.

Repair validation: prescribed `scompile.py` passed both sandbox-name and library-name
compilation with no errors or warnings. The only elaboration repair was qualifying
`CategoryTheory.Functor.whiskerRight` after dropping the smooth-lattice import.
The theorem signature was checked verbatim against `lean.statement`; the node differs
from current main only in the authorized `stmt_deps` and `lean` fields.
