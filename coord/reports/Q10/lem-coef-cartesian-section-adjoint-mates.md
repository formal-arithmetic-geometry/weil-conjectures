## Worker report

Statement-only delivery for `lem-coef-cartesian-section-adjoint-mates`, in
`Sheaf.Paper.CartesianSectionAdjointMates`, namespace
`WeilConjectures.CartesianSectionAdjoint`. The sole postponed proof is
`cartesianSectionAdjointMates`. Its docstring follows all six current DAG assembly
steps. No definition has postponed data or an embedded postponed proof.

The current node, resolved stage-1 repair note, latest blueprint finite-exceptional
statement and proof, and dependency signatures/docstrings were read. The repair
note is stage 1 and resolved; its former enhanced route is not reinstated. The
existing ordinary-system interfaces cover the actual categories required here.

### Hypotheses and objects

| Node hypothesis or convention | Lean rendering |
| --- | --- |
| k is the fixed algebraic closure of a finite field | `D : FiniteFieldDatum.{u}` and `Spec (.of D.k)` |
| l is prime and differs from char k | `[Fact l.Prime]`, `hl : l ≠ D.p` |
| E is a finite extension of Q_l | `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]` |
| R, uniformizer, and A_n are the prescribed valuation-ring quotients | inherited `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionRing`; natural index n means exponent n+1 |
| X,Y are separated finite-type k-schemes | `Scheme.{u}`, `Over (Spec (.of D.k))`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on both structure morphisms |
| f is a separated finite-type k-morphism | `f : X ⟶ Y`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` |
| fixed compactification f=pj | `c : Compactification f`, with actual `c.i`, `c.g`, `c.comm` |
| ordinary unbounded derived category of strict semilinear systems | `coefficientSequenceDerived l E W`, the existing ringed sequence-site module presentation; its strict transition and exact evaluation are `coefficientSequenceDerivedTransition` and `coefficientSequenceDerivedEvaluation` |
| N consists of normalized systems with individually bounded constructible finite-Tor levels | existing `FiniteAdjunctionDiagram.domain`; it is `IsNormalizedCoefficientSequence` AND `∀ n, FiniteExceptional.domain ... n (e_n M)` |
| no common cohomological/Tor interval | no uniform-bound binder occurs; the boundedness and Tor existentials are inside the individual-level predicate |

### Conclusions and maps

| Node clause | Lean rendering |
| --- | --- |
| actual Rp_* j_! preserves N | existential `r : Realization ...`; `r.support` is ordinary exact open extension and universal total derived proper image; `r.F` is on precisely `domain.FullSubcategory`; `r.supportIso` identifies its actual object and arrow action |
| right adjoint existence is a conclusion | `r.G` and `r.adjunction : r.F ⊣ r.G` are fields of existential conclusion data, never hypotheses |
| construction from ambient etale systems and comparison | existential `EtaleOrigin`: actual etale `support.F`, `right`, `adjunction`; `source.comparison.R/P`, `target.comparison.R`; `leftComparison`, `rightComparison`, and `transpose` identify the restricted Hom bijection with the ambient adjunction under the actual comparison counit |
| specified e_n F = F_n e_n, e_n G = G_n e_n | `r.supportEvaluation n`, `r.exceptionalEvaluation n`, with F_n/G_n exactly `FiniteExceptional.F/G` |
| left evaluation canonical | `r.supportEvaluation_canonical` is derived evaluation of `supportIso` followed by `r.support.evaluation` |
| comparisons preserve counits and units | `r.counit`, `r.unit`, using precisely `FiniteExceptional.adjunction` |
| compact-support reduction formula | `r.supportTransition`; its `transition` is the scalar-extension adjunct of the actual strict transition, and its q is `FiniteExceptional.q` |
| exceptional reduction formula and canonical counit mate b | `r.exceptionalTransition`, using precisely `FiniteExceptional.b`; that definition is the finite adjunction mate of q inverse, and no independent b is introduced |
| b invertible | explicit `∀ m n h, IsIso (FiniteExceptional.b ... h)` |
| actual system units/counits and triangles | `r.adjunction` is an ordinary `CategoryTheory.Adjunction` on full subcategories of the ordinary system derived category; its triangle axioms are system-map identities |
| natural Phi in D(Tow(Ab)) | existential `Φ : Enriched r g s βX βY`; `Φ.iso : r.mappingSource ≅ r.mappingTarget`, with source/target defined by the dependency's actual `coefficientSequenceGlobalHom` bifunctors |
| Phi constructed from tensor-Hom, projection, actual counit | `Φ.internalIsIso` and `Φ.component` identify it with `r.globalMap`, which is derived sections of the inverse `r.enrichedMap`; that map is explicitly the closed transpose of the actual system projection, geometric counit, evaluation, and `r.ambientCounit` |
| finite derived mapping-complex adjunction | `Φ.finiteIso`, `Φ.finiteHom`, `Φ.finiteEvaluation` use `coefficientFiniteGlobalHom`, the uniquely normalized `coefficientFiniteHomEquiv`, and the same finite adjunction |
| degree-zero formulas | explicit forward `r.adjunction.homEquiv M N h = unit ≫ r.G.map h` and inverse `homEquiv.symm h = r.F.map h ≫ counit`; `Φ.finiteHom` pins the finite H-zero mapping action to this same specified finite adjunction |
| before Rlim: actual inverses and evaluations | `Φ.iso` inverse identities hold in the system mapping-tower derived category; `Φ.component` fixes the map before any limit |
| Rlim gives an iso in D(Ab) | explicit `IsIso (coefficientMappingLimit.map (Φ.iso.hom.app ...))` and both inverse equations for the mapped hom/inv |
| respects mates of specified actual transformations, including composition comparisons | `MateEvaluation`: universally quantifies an actual system transformation alpha (the other functor may be a composite), its specified counit-compatible finite evaluation, and asserts the finite evaluation of its actual `conjugateEquiv` mate and the inverse-mate identity |
| tensor-evaluation/transposes are actual system maps with finite evaluations | final `SystemTensorTransposeCoherence` on the concrete small pro-etale ringed sequence sites; its equations give evaluated closed transposes for normalized first Hom input, inverse identities, scalar-transition naturality, and K-flat representative independence |

The existing full-domain, geometry, realization, mapping and enriched definitions
are reused. `EtaleOrigin` and `MateEvaluation` are helper presentations of clauses
of this node, listed in `lean.declarations`, not new independent mathematical notions.
The added statement dependencies are the landed `def-coef-finite-adjunction-system-data`
and the new definition owner `def-coef-cartesian-section-data`. The three theorem
nodes rejected in H2 are no longer added as statement dependencies. The new module
publicly re-exports their existing definitions; no existence theorem is used merely
to name a presentation type. Traversal of both dependency edge types found no cycle.

### Dependency declarations used

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing` and its reexported coefficient constructions.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- The scheme-morphism-properties node is explicitly a convention: standard `AlgebraicGeometry.Scheme`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` are used.
- `WeilConjectures.Compactification.RefinementCategory`: `AlgebraicGeometry.Compactification` and its refinement category (no new compactification notion).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology` (object universe u+1, morphism universe u).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`: `SheafOfModules.coefficientSystemDerivedComparison` and its actual derived system/site-comparison interface, used through the sequence-site presentation.
- `Sheaf.Paper.NormalizedDVRTower`: the existing normalization convention and scalar restriction; the actual normalized sequence category uses `IsNormalizedCoefficientSequence`, not the older completed-ring tower encoding as a replacement category.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `WeilConjectures.finiteTorConstructibleEtale`; the pro-etale predicate is the reexported `finiteTorConstructible` used by `FiniteExceptional.domain`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`: `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`, included in the finite-domain predicate.
- `Sheaf.SixFunctors.FiniteExceptional`: `domain`, `F`, `G`, `Q`, `q`, `b`, `adjunction`, `finite_exceptional` in `WeilConjectures.FiniteExceptional`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`: `CoefficientDerivedSystemCalculus`, `coefficientSequenceGlobalHom`, `coefficientMappingLimit`, and exact sequence evaluations.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`, `conjugateEquiv`; b uses the former, `MateEvaluation` the latter.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`: `AlgebraicGeometry.ProEtale.derivedTensor`; sequence-site K-flat tensors are the existing `systemClosed` construction, not a second definition of tensor.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`: `SheafOfModules.systemLevelLeftExtensionTheory` (free-insertion proof dependency).
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded exceptional system and specified finite adjunction, used through `FiniteExceptional.G/adjunction`.
- `Sheaf.SixFunctors.FiniteAdjunctionSystemData`: `domain`, `evaluation`, `transition`, `Geometry`, `Support`, `Realization`, `SectionsPush`, `Realization.enrichedMap/globalMap`.
- `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`: `Enriched`, `Realization.mappingSource/mappingTarget`, finite mapping bifunctors. Its additional dualizing/integral conclusions are not asserted here.
- `Sheaf.Paper.SystemInternalHomRepresentability`: `Representability`, `ComparisonImage.P/R/derivedAdjunction`, `Et`, `coefficients`.
- `Sheaf.Paper.SystemAdjunctionTransposeCoherence`: `SemilinearSections.SystemTensorTransposeCoherence`.

The recorded proof-dependency modules are imported, including free insertion,
semilinear sections, compact-support projection, enriched projection-adjunction,
internal-Hom representability, transpose coherence and the etale-system adjoint.
`lem-coef-levelwise-normalized-adjoint-descent` has no Lean record in the current
read DAG, so it has no module to import; it is a future proof premise, not a
missing object in this statement. This delivery does not wait on it.

### Edge cases and searches

Checked: n=0 represents A_1, so no positive exponent is lost; m=n uses the
existing identity quotient/transition and its canonical finite mate. Zero systems
and empty schemes are included; no nonemptiness or dimension lower bound is
imposed. Bounds are permitted to vary arbitrarily with n. Nonflat quotient maps
are handled by the existing derived scalar adjunction, not an added flatness
hypothesis. The small pro-etale site's distinct object/morphism universes are
retained. The generic Bool site-selector universe ambiguity was removed by using
the concrete dependency-provided pro-etale interface, without changing sizes.

Searches run with the prescribed wrapper:

- leanfinder, `Adjoint compact support on normalized derived coefficient systems with finite exceptional adjunction and derived mapping towers`: 8 hits, including `CategoryTheory.Adjunction.derived`, `derivedε`, `derivedε_fac_app`, `derived'`, `derived'_counit`; none states this normalized coefficient-system theorem.
- loogle, `CategoryTheory.mateEquiv, CategoryTheory.Adjunction`: 12 hits, including `mateEquiv`, `mateEquiv_counit`, `unit_mateEquiv`, `mateEquiv_vcomp/hcomp`; these provide the ordinary categorical ingredients only.
- grep, `mateEquiv|evaluationAdjunction` in `CategoryTheory/Adjunction`: 9 hits in Mates and Evaluation, not this geometric system result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the node id and cartesian/normalized adjunction expressions: no existing declaration of the complete item; an existing proof docstring cites the node. Broader searches located the reusable `FiniteAdjunctionDiagram` interfaces and the existing enriched/transpose APIs, which are imported instead of copied.

No mathematical statement correction or disputed statement is needed. The item
changes only `lean` and `stmt_deps`. The new definition-node owner is described
below. No existing dependency declaration is replaced.

Validation before return: the original theorem compiled cleanly. The H2 repair
is compiled as two separate files in dependency order with `scompile.py`; the
final compile and delivery preflight are recorded by the prescribed wrappers.

## Second reading by Q10

Fresh solo reading of the node and final file, under the dispatcher instruction
not to start other agents; no independent second agent is claimed. Read the
existing `domain`, `Realization`, `Enriched`, their canonical map definitions and
the two new helper signatures against each clause above. The draft initially
closed its namespace before the mate helper and left a generic site-selector
universe metavariable; both were repaired. The final signature binds every
variable/universe explicitly with `autoImplicit false`, concludes existence of
all adjoint/map data, and uses the exact finite F/G/adjunction/q/b declarations.
No uniform bound, quotient flatness or pro-etale Brown assumption was introduced.
The natural map is pinned by `Enriched.component`, not chosen from finite fibers.
The ambient etale origin is pinned by a composite Hom transpose equation, not
merely by unnamed objectwise isomorphisms. The mate clause uses the actual given
transformation and actual counits before any derived inverse limit.


## New nodes

`def-coef-cartesian-section-data`, in `sec-six-functors`, unit
`sk-prop-sf-biduality-general`, owns `Sheaf.Paper.CartesianSectionData`. Its source
is the current blueprint finite-exceptional proof, paragraphs 2--3, together with
the retained ordinary strict-system RHom and counit refinement. It publicly
re-exports the exact existing `Enriched`, `Realization.mappingSource/mappingTarget`,
`finiteMappingSource/Target`, `SystemInternalHom.Representability`, `Et`,
`coefficients`, `ComparisonImage.P/R/derivedAdjunction`, and
`SemilinearSections.SystemTensorTransposeCoherence`. Its primary declaration is a
transparent abbreviation of `SystemInternalHom.Representability`, used by both
`EtaleOrigin.source` and `.target`. All its parameters are explicit, including the
universe; it retains precisely the original comparison structure and projections.
It defines a presentation type, without asserting inhabitation. No data, canonical
map, tensor or adjunction is redefined or chosen.

The new node's clauses match the public definitions: the coefficient tower and
etale category are `SystemInternalHom.coefficients/Et`; the actual comparison
functors and derived adjunction are `ComparisonImage.P/R/derivedAdjunction`; every
comparison/representing field is exactly `SystemInternalHom.Representability`;
the two system and finite mapping bifunctors are the four named mapping
definitions; enriched invertibility, its canonical component, finite degree-zero
normalization and evaluation squares are the six fields of `Enriched`; the five
coherence clauses are exactly the five conjuncts of
`SystemTensorTransposeCoherence`. No geometric or finiteness assumption has been
moved from a conclusion into a hypothesis. The generalized coherence definition
retains its original independent site and ring universes; the item's use retains
the concrete small pro-etale universes.

Searches for an owner: `grep` over definition-node JSON and
`tools/blueprint_refs.py search` found no owner of these declarations (both
`Enriched` and `SystemTensorTransposeCoherence` give zero blueprint matches).
The prescribed `msearch.py` LeanSearch query
"Normalized coefficient systems enriched mapping adjunction presentations etale
proetale internal Hom comparison tensor transpose coherence" returned eight
ordinary internal-Hom/adjunction hits, not this interface. Loogle for
`CategoryTheory.Adjunction, CategoryTheory.mateEquiv` returned twelve ordinary
mate results. Mathlib grep for
`SystemTensorTransposeCoherence|SystemInternalHom|FiniteAdjunctionDiagram`
returned zero hits. `rg` in `lean/WeilConjectures` found no exact declaration;
`rg` in `lean/Sheaf` located the three existing modules now publicly re-exported.
The exact wrapper outputs are retained in the node's `mathlib_searches`.

## Returned delivery repair H2

Compared the retained delivery with the current read-only DAG and the returned
head `7e4c744d38eb`. The mathematical theorem signature, its two helper meanings,
and its sole postponed proof are unchanged. The new definition module replaces
three direct public theorem-module imports. `EtaleOrigin` uses the definitionally
equal comparison abbreviation. The item now cites the definition owner instead
of adding `lem-coef-finite-adjunction-diagram-realization`,
`lem-coef-system-internal-hom-representability`, and
`lem-coef-system-adjunction-transpose-coherence` to `stmt_deps`.
The latter two remain in the existing `proof_deps`; the finite-realization theorem
was never in the base's six-step proof or its `proof_deps`, so no new use of that
larger theorem has been invented. The three original modules remain available
through the public re-export interface; their theorems are not needed to define
any presentation type.

Second reading of the repair by Q10: checked the new node clause by clause
against the exported original signatures, and checked its definition dependencies
against every bracketed citation. There is one real abbreviation and no copied
structure, choice, existence axiom or embedded postponed proof. Its arbitrary
scheme morphism and the generic coherence site add no assumptions to the item's
unchanged theorem. Checked zero systems, empty schemes, index zero (exponent one),
and identity reductions again: a transparent alias and re-export leave all these
cases unchanged. The original reviewer accepted all mathematical clauses; this
repair addresses the ownership of their definition interfaces only.
