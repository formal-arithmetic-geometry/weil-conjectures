## Worker report

This delivery defines the four geometric-point fibre functors of
`def-weil-finite-coefficient-point` in `Sheaf.Paper.FiniteCoefficientPoint`.
The public entry points are `WeilConjectures.pointFiniteFibre`,
`pointIntegralFibre`, `pointRationalFibre`, and `pointQbarFibre`.
The primary binding is the fourth entry point; `lean.declarations` lists all four
and every construction and proof obligation in the module. No equivalence of
these fibre functors is asserted: that is the separate node
`lem-weil-point-fibre-equivalence`.

The original sandbox contained two Lean files and recorded Mathlib searches,
but neither node copies nor a report. No delivery result was present. I retained
those files, checked them against the dependency declarations and source, repaired
compilation, and supplied the records and report.

### Hypotheses and clauses

* The global tuple is the existing `D : FiniteFieldDatum.{u}`; its fields encode
  prime p, positive a, q = p^a, a q-element field and its fixed algebraic closure.
  The prime is `l : ℕ` with `[Fact l.Prime]`; `hl : l ≠ D.p` remains an argument
  of all four fibre functors, via their finiteness witness. `pointFibreBaseIsAlgClosed`
  uses `IsAlgClosure.isAlgClosed D.k₀`, so algebraic closedness is derived from
  the global datum, never assumed separately.
* A finite coefficient extension is `E : Type u` with `[Field E]`,
  `[Algebra ℚ_[l] E]` and `[FiniteDimensional ℚ_[l] E]`. Its integer ring,
  uniformizer and quotient ring are exactly the existing
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing l E n`; none is chosen afresh here. The fixed closure
  in clause 4 is `Ω` with `[Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`.
  A field contained in that closure appears as an actual finite intermediate field
  in `Padic.FiniteCoefficientFields l Ω`; the first three constructions also work
  on any equivalent model of such a finite extension.
* The scheme s is literally `Spec (.of D.k)`. The source categories are the
  recorded `intrinsicFiniteTorsionConstructible` full subcategory,
  `sfIntegralConstructibleCategory`, `sfRationalConstructibleCategory`, and
  `generalAlgebraicallyClosedConstructibleCategory`, all at this same scheme.
  These use the small pro-etale site, with object universe u+1 and morphism
  universe u. Integral objects are modules over the completed coefficient sheaf,
  retaining derived completeness and the common interval for all reductions.
  Rationalization is raw Hom tensor localization, without Karoubi completion.
* Evaluation is `pointFiniteSections D.k A` or `pointIntegralSections l E D.k`:
  these are the dependency's final-object evaluation followed by restriction
  along the actual constant-section coefficient map. The latter uses the actual
  `integralConstantToCompletion`, rather than identifying the completed sheaf
  with the discrete constant sheaf. Their `mapDerivedCategory` functors descend
  termwise evaluation; the named exactness obligations invoke the recorded
  point-sections exactness theorem. The module introduces no alternative stalk.
* Clause 1 is `pointFiniteFibre (n : ℕ) (hn : 1 ≤ n)`.
  It restricts derived finite-coefficient evaluation to the source and lifts
  it to the existing `DerivedCategory.pointFiniteCohomology` full subcategory.
  `pointFibre_sections_mem` transports clause 1 of `point_sections_finiteness`
  from arbitrary complex representatives using the derived-factorization iso.
* Clause 2 is `pointIntegralFibre`, restricted to the existing
  `sfIntegralConstructibleCategory`. Its target is the existing
  `DerivedCategory.pointFgComplete` full subcategory for the uniformizer ideal.
  Its object is derived integral sections and its maps are derived evaluation.
  `pointIntegralFibre_linear` states O_E-linearity explicitly:
  the image of `a • f` is `ULift.up a` times the image of f.
  Boundedness, finite generation and derived completeness all remain in the
  target predicate; the second clause of `point_sections_finiteness` supplies them.
* Clause 3 starts with `pointFibreRationalAmbient`: exact integral sections
  followed by `ModuleCat.extendScalars (pointIntegralToField l E)`, descended
  termwise to derived categories. `pointIntegralRationalFibre` restricts this
  functor using clause 3 of `point_sections_finiteness` and the size equivalence
  described below. `pointRationalFibre_existsUnique` prescribes its object on
  every raw-localization object and its image of every pure tensor:
  `a ⊗ₜ f` goes to `sfRationalCoefficientEquiv l E a` times the integral
  rational fibre of f. The dependency's `sfRationalHomCoordinates` exchanges
  the scalar-first encoding for the node's f-tensor-lambda encoding.
  `pointRationalFibre` is selected from this uniquely specified functor;
  no arbitrary functor or arbitrary morphism is selected.
* Clause 4 keeps the actual finite intermediate field as the stage of its
  output object (`pointQbarFibreObj`). The source's recorded small field model
  `AlgebraicallyClosedCoefficients.Coefficient` is identified with that field
  by `Shrink.algEquiv`. `pointStageFibre` composes clause 3 with precisely this
  coefficient scalar extension.
* `pointRationalFibreScalar_existsUnique` fixes the scalar comparison by an
  explicit equation with the dependency's
  `pointRationalSectionsScalarExtensionIso`, after the specified size and
  coefficient identifications. It does not postulate an unspecified isomorphism.
  Its proof describes naturality on rational maps and transfer of the recorded
  unit and tower coherence. `pointStageCoefficientSquare` is the equality of
  the two actual coefficient inclusion composites; `pointStageTensorSquare`
  is built from the existing normalized tensor tower.
* `pointQbarFibreRepresentative` sends a common-stage representative u to
  inverse phi on its source, followed by the stage fibre of u, followed by phi
  on its target (Lean composes left to right). The exterior
  `pointFdQbarStageComp` maps express this same representative as an arrow
  between the original output pairs in the recorded target category.
  `pointQbarFibre_existsUnique` specifies the object formula and this formula
  on every `StageSystem.PairCategory.mkHom`. Its proof explains independence
  of representatives, identity and composition from scalar coherence.
  `pointQbarFibre` selects exactly that uniquely specified functor.

### Sizes and canonical constructions

The finite and integral target predicates already combine module and coefficient
size in one universe. Their actual section carriers have size u+1, as in the
recorded `PointSectionsFiniteness` module. Accordingly the first two targets use
`ULift.{u+1,u}` coefficients and the same existing predicates at size u+1.
These are the original coefficient rings with their ring equivalence, not an
extra mathematical hypothesis or a different finiteness condition.

The rational finite-stage target must agree with `PointFdQbar`, whose finite
field objects have module size u. `pointFibreModuleLift` is the explicit carrier
lift followed by the coefficient-ring identification. `pointFibreSizeLift`
restricts its derived functor to bounded finite-dimensional objects.
`pointFibreSizeLift_equivalence` supplies its equivalence: split a complex over
a field into its finite-dimensional cohomology, with finite support; those
spaces and their graded maps admit small models. `pointFibreSizeDescent` is
its equivalence inverse, determined up to the equality used downstream by its
unit and counit, as allowed by the project's non-hollow-definition rule.
The normalization `pointIntegralRationalNormalization` explicitly includes
that counit, the lift/coefficient cancellation and the pure-tensor comparison
with the scalar-extension dependency's ordinary rational sections.

Each remaining selected map is backed by `∃!` with all components prescribed
on elements, pure tensors or common-stage representatives. The helper theorems
have complete natural-language proof docstrings and carry this owning node's
blueprint tag. All theorem proofs remain `sorry`; all definitions contain real
construction data. No theorem is proved in this stage.

### Dependencies read and used

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and its identity.
* The recorded pro-etale ambient presentation is
  `WeilConjectures.SixFunctors.ProEtale.Derived.ModuleDerivedCategory`,
  `AlgebraicGeometry.ProEtale.ModuleDerivedCategory`. This is the equivalent
  sheaf-valued-module presentation. The actual source of our finite restriction
  is the recorded intrinsic finite-torsion module's `proEtaleDerivedCategory`
  (modules over the constant ring sheaf), already used by the recorded sections
  functor. No copy or additional small-site restriction is introduced.
* `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
* `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible` and `sfIntegralConstructibleCategory`.
* `Sheaf.Paper.CompletedIntegralCoefficientGerm`:
  `WeilConjectures.integralConstantToCompletion`, through the existing
  section coefficient maps.
* `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`,
  `sfRationalCoefficientEquiv`, `sfRationalScalarExtension`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`,
  `GeneralAlgebraicallyClosedCoefficients.Stage`, `stageSystem`, `stageTransition`;
  and its imported `AlgebraicallyClosedCoefficients.Coefficient` and
  `coefficientInclusion`.
* `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`:
  `Padic.FiniteCoefficientFields` and its finite-dimensionality instance.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory` and `DerivedCategory.Q`.
* `Sheaf.Paper.PointFiniteCohomologyComplexes`, `PointFgCompleteComplexes`,
  `PointFdComplexes`: `DerivedCategory.pointFiniteCohomology`,
  `pointFgComplete`, `pointFiniteDimensional`.
* `Sheaf.Paper.PointFdQbarCategory`: `DerivedCategory.PointFdQbar`,
  `pointFdQbarStage`, `pointFdQbarStageComp`; its normalized field scalar
  extension and tower maps are used, rather than restated.
* `Sheaf.Paper.PointProEtaleSectionsExact`:
  `AlgebraicGeometry.ProEtale.point_proEtale_sections_exact` and
  `pointModuleSections`, through the exact section restrictions.
* `Sheaf.Paper.PointSectionsFiniteness`: `WeilConjectures.point_sections_finiteness`,
  `pointFiniteSections`, `pointIntegralSections`, `pointIntegralToField`.
* `Sheaf.Paper.PointSectionsScalarExtension`:
  `pointSectionsScalarExtension`, `pointRationalSectionsScalarExtensionIso`,
  `pointCompletedDerivedSections`, `pointIntegralConstructible_iff`,
  `pointModuleDerivedRationalization`, `pointCoefficientFieldDerivedTensor`.

Dependency modules supply their own imported prerequisites. The main file's
six direct imports provide sections finiteness, sections scalar comparison,
raw rational categories, common-stage source, common-stage target, and the
explicit module carrier lift, respectively.

### Edge cases

The positive level binder allows n=1 and every larger n; no n=0 case was dropped
from the node. The zero complex is allowed in each full subcategory; boundedness
is cohomological, never a restriction to termwise bounded representatives.
All integer degrees and all raw-localization morphisms are retained, including
torsion objects which become zero after rationalization. No restriction to
perfect objects, free modules or nonzero objects is imposed. Arbitrary finite
coefficient extensions, the base field stage, identity inclusions, repeated
fields and arbitrary common-stage representatives are included. The coefficient
square and scalar comparison include identity maps and towers. `hl` retains
exactly l different from p, without excluding any further characteristic.
The site retains its distinct object and morphism universe levels.

### Searches

The resumed sandbox contains actual search logs from 2026-10-17, retained in
`searches.jsonl`. They include:

* LeanFinder: “Fiber functor from constructible proetale complexes at an
  algebraically closed point to finite dimensional coefficient complexes”,
  and “fibre functor from constructible proetale derived categories over an
  algebraically closed field to bounded finite module complexes”. Results were
  Galois-category fibre functors and condensed free-module constructions;
  none states these four functors.
* Loogle: `fiberFunctor, evaluation, mapDerivedCategory` reported unknown
  `fiberFunctor`. The usable query
  `CategoryTheory.Functor, CategoryTheory.ObjectProperty.lift` returned
  `ObjectProperty.lift` and its ordinary full-subcategory lemmas, which are used.
* LeanSearch: “proetale sheaf sections functor derived bounded constructible
  modules geometric point” returned `SheafOfModules.sectionsFunctor`,
  `evaluation` and generic sheaf sections. A later query about exact final-object
  sections returned site point fibre functors, not the coefficient construction.
* Mathlib grep through `msearch.py` for
  `fiberFunctor|fibreFunctor|point.*Sections` and
  `pointFibre|pointFiber|finiteCoefficientPoint|proEtale.*[Ss]ections`
  in AlgebraicGeometry returned no matches.
* Repeated direct `rg` in the upstream `WeilConjectures` and project `lean/Sheaf`
  for `pointFibre|pointFiber|finiteCoefficientPoint` found no existing construction.
  Searching the node id upstream found an etale duality reference in
  `SixFunctors/Etale/Derived/Point.lean`; reading it confirmed that it concerns
  finite etale coefficients and point duality, not these pro-etale integral,
  rational and algebraically closed fibre functors.

The existing sections and target definitions were reused. No new DAG notion is
needed, and there is no statement correction or STATEMENT-DISPUTED finding.
The current blueprint main snapshot has the same four evaluation stages as the
older source; the node's reviewed split moves equivalence to its separate lemma.

## Dependency modules

`lem-weil-point-sections-scalar-extension`: retained the sandbox's
`Sheaf.Paper.PointSectionsScalarExtension` repair. The base source explicitly
passed `integralScalarExtension.{u,u}` nine times, whereas its current published
interface has only universe u. These obsolete applications prevent elaborating
the recorded canonical completion isomorphism and scalar-extension statement.
The repair changes exactly those nine applications to `.{u}`. It preserves
all definitions, objects, normalization maps, hypotheses and naturality/unit/tower
clauses, including the identity extension. The node copy changes only `lean`,
with this explanation in `lean.note`. There are no new definitions or theorem
statements in this dependency repair. The consumer uses its actual rational
scalar-extension isomorphism in the defining equation of
`pointRationalFibreScalar_existsUnique`.

### Validation

Both delivered files are compiled separately in dependency order through
`scompile.py`, against the current published library and private side overlay.
The main-file repair makes the existing additive and exact section/tensor
instances explicit locally in `pointFibreRationalDownIso`; it adds no assumption.
The prescribed dry run and final delivery provide preflight and per-file
compilation checks. The maintainer performs the independent statement review.

## Second reading by Q154

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
