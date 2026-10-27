## Worker report

Q31 states `AlgebraicGeometry.Etale.SystemCompactSupport.systemCompactSupportProjection`
in `Sheaf.Paper.SystemCompactSupportProjection`. Its proof is `sorry`; all other
new declarations are definitions, structures or instances with complete data.
There is no statement correction or dependency-record repair. The node's original
statement and proof are retained. The unused theorem dependency introduced by the
previous ownership repair has been removed. Its statement dependencies
only gain the seven new definition nodes below and the already recorded node used
for the system geometric presentation and the precise finite projection map.

The main statement asserts the existence of the geometric/tensor presentation,
its normalized evaluations, its actual strict-transition realizations, and the
canonical natural projection, with all the requested properties. Those witnesses
are conclusions, not additional hypotheses. In particular this is not a theorem
conditional on a projection isomorphism, a chosen system functor or normalized
inputs. `Support.F` is the existing exact open extension followed by total
right-derived proper image on the sequence site.

Hypotheses and conventions, one by one:

- The finite-field datum is `(k : WeilConjectures.FiniteFieldDatum.{u})`.
  The prime is `(l : ℕ) [Fact l.Prime]`, with `(hlp : l ≠ k.p)`.
- The finite extension is `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. `quotientTower l E` uses exactly
  `Padic.coefficientExtensionRing l E (n + 1)` and the recorded quotient transition.
  Thus index zero denotes the paper's first quotient, and every positive quotient
  and every composite quotient map is included. The valuation ring and uniformizer
  are the existing coefficient-extension constructions, not new choices.
- `X Y : Over (Spec (CommRingCat.of k.k))` and `f : X ⟶ Y` retain the maps to
  the same base and their commutativity. Each structure map has `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact`. The same three instances on `f.left`
  express the separated finite-type morphism. `c : Compactification f.left` is
  precisely the supplied open/proper factorization, with its recorded equality.
- `Modules W B`, `Derived W B`, `coefficients` and `transitions` are imported
  from `SystemProjection`; they are the actual vertical sequence-site modules
  and their ordinary unbounded derived category. They are not diagrams in
  levelwise derived categories. All inputs `P,M` range over those whole categories.
  The preliminary mention of pro-etale systems in the node introduces a parallel
  category; all its compact-support conclusions are expressly on etale systems.
  The existing generic semilinear definitions also apply to the pro-etale site;
  this delivery introduces no second pro-etale system category.
- Site object/morphism/coefficient universes are respectively `u+1,u,u+1` for
  these small etale sites. Finite coefficient modules have universe `u+1`.
  Every universe and variable is bound explicitly; `autoImplicit` is false.

Conclusions and canonical-map clauses, one by one:

- `d.support.F` is `d.support.openImage.J ⋙ d.support.proper.R`, via the existing
  `Support.F`. `d` is `ProjectionData c Y.hom (quotientTower l E)`.
- Exactness is `(∃ (_ : d.support.F.CommShift ℤ), d.support.F.IsTriangulated)`.
  Preservation of every small coproduct is
  `∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) d.support.F`.
  This includes the empty coproduct and uses the coefficient-size smallness
  convention of the existing Grothendieck module categories.
- `e : ProjectionEvaluation d` supplies all exact level evaluations and
  `e.support n : SupportEvaluation ...`. Its `.iso` is exactly
  `F ⋙ e_n ≅ e_n ⋙ rightDerivedLowerShriekOfCompactification ... c` in Lean's
  left-to-right functor notation, namely the mathematical `e_n F ≅ F_n e_n`.
  `SupportEvaluation` is pasted from the ordinary section-normalized proper
  comparison and the ordinary open adjunction comparison.
- The base pullback is `d.baseImage.P`. `d.pull` is its composite with `p*` and
  `j*`. This is the geometric pullback along `a_X`: `c.comm` identifies `jp`
  with `f.left`, and `f.w` identifies `f.left ≫ Y.hom` with `X.hom`.
  This notation constructs the pullback by composition, rather than postulating
  an unrelated inverse-image functor.
- `pi : d.source ⟶ d.target` is an actual natural transformation on
  `Derived s B × Derived X B`. The equation `pi.app (P, M) = d.word P M`
  specifies every component before any evaluation.
- `d.properWord` is the geometric-adjunction transpose of
  `d.properTensor.mu.hom` followed by the proper counit on the second tensor
  factor. `d.word` follows this with `R` applied to `d.openProjection.inv`.
  `ProjectionData.openProjection_transpose` fixes the open tensor map as the
  transpose of the actual open unit and the inverse tensor-pullback comparison.
  `ImageTensor.model` reuses the existing `TensorComparisonModel` on signed
  total complexes and flat-term K-flat representatives; its `pure` equation
  fixes the ordinary map on all unit-generated local pure tensors. Thus these
  are the geometric counit/open-tensor word, rather than arbitrary isomorphisms
  between the desired endpoints.
- `IsIso pi` asserts invertibility on all unbounded pairs. `e.projectionLaw pi`
  is the explicit equality of maps after applying the specified evaluations.
  On the left it evaluates `pi`, then applies compact-support evaluation,
  tensor evaluation and the composite pullback comparison. On the right it
  applies the source evaluations followed by the published coefficient-first
  `supportProjectionMap`. `pullComparison` includes the canonical
  exact-versus-left-derived comparisons and `leftDerivedUpperStarCompactificationIso`,
  so the endpoint is exactly the finite projection's pullback, without an
  arbitrary additional identification.
- The quotient functor is the existing `scalarExtension (quotientMap B h) W`.
  For every `m,n,h : n ≤ m`, the conclusion asserts
  `IsIso (compactScalarMap (quotientMap B h) c)`. That published map is the
  changed-coefficient proper counit mate followed by the canonical open tensor
  balancing map, and is a morphism in the target coefficient category. Neither
  its construction nor the new theorem assumes the quotient map flat.
- The quotient cocycle is the explicit equality of `compactScalarMap` for the
  composite ring map with `singlePath` for the two quotient maps. `singlePath`
  includes the canonical derived scalar-extension associators. Functoriality
  of `quotientTower` identifies this composite with the single quotient
  `r → n`; equality indices are included.
- `tx` and `ty` are `TransitionEvaluation` on X and Y. Their ordinary maps are
  fixed on every section by the actual intrinsic strict transition. Their
  `.derived` is explicitly its termwise quasi-isomorphism localization, and
  `.reduction` explicitly takes the extension/restriction adjoint transpose.
  The final equation states `t^(FM) = F_n(t^M) q` with the necessary canonical
  `SupportEvaluation.iso` inserted on each side. It quantifies over every
  unbounded M and all `n ≤ m`.
- Preservation of inverse/direct-image units and counits is included in the
  evaluation interfaces: `ImageEvaluation.inverse_mate`,
  `derivedInverse_termwise` and `derived_mate` fix the comparison as the mate
  of the localized ordinary comparison. The corresponding open comparison
  is its ordinary open-adjunction mate localized termwise. Mate identities
  give both unit and counit diagrams; the interfaces permit no independent
  rescaling of a derived adjunction or its evaluation map.
- No boundedness, flatness, constructibility, normalization, cartesianness, or
  invertibility of an input transition is among the hypotheses. In particular
  no passage to a constructible or cartesian full subcategory occurs.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its construction
  import: `Padic.coefficientExtensionRing`, `coefficientExtensionTransition`,
  the valuation-ring/uniformizer quotient definitions, and finiteness.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification`,
  including `.i`, `.g`, `.Z` and `.comm`.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`:
  `SheafOfModules.coefficientSystemDerivedComparison` and the strict-system
  interpretation. `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`.
- `Sheaf.Paper.SemilinearSystemModels`: `Systems`, `DS`, `transition`,
  `TensorComparisonModel`, `tensorSection`, `totalTensor`, `tensorSummand`,
  `tensorModelIso`. `Sheaf.Paper.SemilinearDerivedCalculus`: `Data`.
- `Sheaf.Paper.EtaleSystemProjectionData`: `Modules`, `Derived`, `rings`,
  `coefficients`, `transitions`, `level`, `Evaluation.E`, `Image.P`, `Image.R`,
  `Image.derivedAdjunction`, `OpenImage.J`, `OpenImage.derivedAdjunction`,
  `Support.F`, `ImageEvaluation`, `OpenEvaluation`, `SupportEvaluation.iso`,
  and `singlePath`. In particular no private geometric or scalar functor copy
  was introduced.
- `Sheaf.AlgebraicGeometry.EtaleSupportProjectionShiftUnit`:
  `supportProjectionMap`; the actual finite map is used, not an unspecified
  projection isomorphism. Its upstream imports give
  `leftDerivedUpperStarIsoMapDerivedCategory` and
  `leftDerivedUpperStarCompactificationIso`.
- `Sheaf.Paper.EtaleCompactScalarCoherence` and its public coefficient-change
  imports: `compactScalarMap`, `scalarExtension`, and the actual
  `Sheaf.derivedRestrictScalars` adjunction.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  The representative normalization here is specialized through the existing
  independent-universe `TensorComparisonModel`.
- Mathlib: ordinary `DerivedCategory`, `Localization.liftNatTrans`,
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`,
  `mapDerivedCategoryCompIso`, small etale and pro-etale sites, and the
  actual algebraic-geometric morphism-property instances.
- All recorded non-Mathlib proof-dependency modules are imported as proof
  imports (those already public in a statement dependency remain available
  there). The theorem docstring retains all seven steps of the node's argument:
  construction and exactness, coproducts, system projection, finite evaluation
  and conservativity, quotient invertibility, mate cocycle, actual transitions.

Edge cases checked before and after writing: identity compactification and
identity quotient indices; zero P or M; empty X; empty coproduct; arbitrary
cohomological degrees and unbounded complexes; and the nonflat quotient
`Z/l² → Z/l`. No clause excludes any of these. The maps for zero/empty cases
are the same canonical functorial words, and no input-transition isomorphism
is needed. Universe sizes do not identify the site object and morphism
universes. Equality of system-derived morphisms is never inferred just from
equality of their evaluations: `pi` is specified before evaluation and the
quotient maps and transitions have their actual ringed-site constructions.

Searches actually run (the node records include the service output digests):

- LeanFinder: “Unbounded derived strict semilinear coefficient systems compact
  support projection formula proper pushforward open extension”: eight hits
  on compactly supported functions, no match.
- Loogle: `PreservesCoproducts, Functor.IsTriangulated, AlgebraicGeometry.Compactification`:
  no hits, unknown `PreservesCoproducts`.
- Mathlib grep: `compactSupport|tensorProjection` in CategoryTheory: zero hits.
- LeanFinder: “Canonical tensor comparison for evaluation of strict semilinear
  module systems and for geometric inverse image characterized by local pure
  tensors and K flat total complex”: eight algebraic tensor-flatness hits,
  no match to this interface.
- Loogle: `Functor.LaxMonoidal.μ, SheafOfModules.tensorObjIsoSheafification`:
  no hits, unknown first identifier.
- Mathlib grep: `TensorEvaluation|TensorComparisonModel` in CategoryTheory:
  zero hits.
- LeanSearch: “Tensor comparison for strict semilinear coefficient systems
  evaluation and geometric compact support defined by proper counit and open
  extension”: eight hits including tensor-product extensionality and polynomial
  tensor evaluation, none giving the required constructions.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, and the item-id search:
  no existing statement of this item. The existing `EtaleSystemProjectionData`,
  `EtaleSystemCoefficientProjection`, `EtaleSystemQuotientNormalization`,
  `SemilinearSystemModels`, `SemilinearDerivedCalculus` and finite projection
  modules were inspected. Their exact operations are reused. In particular
  `etaleSystemCoefficientProjection` gives coefficient projection, but does
  not give this geometric base-object projection on strict systems.
- DAG searches inspected the native-open tensor/evaluation and open semilinear
  tensor model nodes. They concern pro-etale/integral open constructions, not
  this fixed-ring etale tensor bridge. `tools/blueprint_refs.py search` for
  “etale system tensor” and “system compact support” returned no blueprint
  node. `ancestor` gave `prop-coef-integral-exceptional-adjoint`.

Sources were read in the current `literature/blueprint/latest/` and local Stacks
sources, especially `sites-cohomology.tex` equation-projection-formula-map
(0B56), lemma-adjoint (07A6), lemma-j-shriek-and-tensor (0GL1), and
`more-etale.tex` remark-Rf-lower-shriek-change-of-rings (0GL6). The item's
historical blueprint source path is left unchanged, as required. No mathematical
statement fault or `STATEMENT-DISPUTED` was found.

The first delivery preflight required the current schema's `import_flags` field
on the six new definition records. Each now has `import_flags: []`; no import
exception or mathematical field changed.

All seven delivered files compiled separately through `scompile.py`, against
current published server sources, without errors or warnings. The larger tensor
representative expressions were split into modules to meet the unchanged
60-second per-file limit; no combined source or global build was used.

## New nodes

`def-coef-etale-support-projection-map` is the existing owner of the canonical coefficient-first source, target and map declarations.

`def-coef-etale-system-tensor-evaluation` owns
`Sheaf.Paper.EtaleSystemTensorEvaluation`. It specifies evaluation from intrinsic
constant-ring module systems to fixed `ModuleCat B_n` sheaves, preserving ordinary
pure tensors and each signed total-complex summand. Existing `Data.tensorEvaluation`
is intrinsic, while `SystemProjection.level` has the fixed-ring codomain; neither
contains this bridge. Sources are Stacks 03EK--03EL and 07A4. The actual search
results above are included in its record.

`def-coef-etale-system-derived-tensor-evaluation` owns
`Sheaf.Paper.EtaleSystemDerivedTensorEvaluation`. It adds the precise K-flat
representative localization square to the preceding data. It uses the existing
`tensorModelIso` and fixed-ring localization lax tensor map. It introduces no
second tensor. Stacks 06YU and 07A4 supply the representative construction.
The ordinary data and this derived normalization are separate modules so each
compiles within 60 seconds. The searches above found no fixed-codomain bridge.

`def-coef-etale-system-image-tensor` owns
`Sheaf.Paper.EtaleSystemImageTensor`. It specializes the existing generic
`TensorComparisonModel` to the actual etale `Image` adjunction and normalizes
its ordinary comparison by unit-generated local pure tensors. The generic
`InverseTensorPure` expects an `AlgebraicInverseImage` of set sheaves, whereas
the already recorded `SystemProjection.Image` is characterized by its fixed
module direct image and adjunction. This interface uses that exact recorded
adjunction, rather than making a second inverse image. Source: 03EL and 07A4;
searches above found the generic model, which is reused.

`def-coef-system-compact-support-data` owns
`Sheaf.Paper.SystemCompactSupportData`. It packages the actual support/base
presentations and tensor pullbacks, the adjunction-normalized open tensor
isomorphism, and the explicit proper-counit/open-inverse word, plus their
canonical evaluation data. Source: 0B56, 07A6, 0GL1. The existing support
presentation has no system tensor projection word; the finite projection
has a different domain. The searches therefore justify this additional
construction, not a duplicate support functor.

`def-coef-system-compact-support-transitions` owns
`Sheaf.Paper.SystemCompactSupportTransitions`. It transports actual strict
transitions to fixed-ring module sheaves, derives them explicitly, and defines
their actual scalar adjuncts. Source: Zheng Construction 4.1 and Stacks 07A6.
The intrinsic transition and the fixed-ring evaluation separately existed;
this exact sectionwise transport and its localization did not. Existing
transition/scalar definitions are reused, and no arbitrary level maps occur.

`def-coef-system-compact-support-evaluation` owns
`Sheaf.Paper.SystemCompactSupportEvaluation`. It defines the precise finite
projection comparison equation, including the canonical composite pullback
comparison. Source: 0B56, 0GL1, Zheng Lemma 5.16. It uses the published
`supportProjectionMap`; no new finite projection or identity axiom is introduced.
The existing finite projection statement does not contain the system-to-finite
comparison equation. The shared searches above found no such bridge.

## Repair of returned delivery

The reviewer return H2/H12 identified that `supportProjectionMap` was owned by the
statement node `lem-pur-etale-support-projection-shift-unit` while both this item and
`def-coef-system-compact-support-evaluation` used it as a definition. I added the
existing definition node `def-coef-etale-support-projection-map`, whose attached
record is `Sheaf.AlgebraicGeometry.EtaleSupportProjectionShiftUnit` and whose
`declarations` are `AlgebraicGeometry.Etale.supportProjectionSource`,
`supportProjectionTarget`, and `supportProjectionMap`. Its map is exactly the inverse
signed tensor symmetry, `projectionMapOfCompactification`, and the target signed
symmetry. Both consumers now cite this definition node in `stmt_deps`. The unused theorem
dependency is removed in the repair below. The new definition nodes
have empty proof dependencies, as required for definitions. No Lean module changed because the
canonical declarations already exist in the published module.

The ownership search reran LeanSearch, Loogle and grep. LeanSearch found only generic
adjunction/tensor hits; Loogle returned zero hits for `supportProjectionMap`; grep found
no Mathlib or WeilConjectures duplicate and found the attached declaration in
`Sheaf.AlgebraicGeometry.EtaleSupportProjectionShiftUnit.lean`. Identity and empty
objects remain covered by the same canonical functorial word.

## Second reading by Q31

I reread the returned item, the evaluation definition, the new definition record and
the attached source module. The only mismatch was the ownership of the plain map
reported by L; it is repaired by the new existing definition node. The redundant
theorem dependency is removed as described below. The item statement, hypotheses, quotient directions, evaluation law,
transition equation and all six auxiliary definitions remain unchanged. The dry run
was rerun after this repair.

## New nodes

`def-coef-etale-support-projection-map` is an existing definition node for the
coefficient-first source, target and projection map in
`Sheaf.AlgebraicGeometry.EtaleSupportProjectionShiftUnit`. It cites the owner of the
ordinary `projectionMapOfCompactification`, records the three searches above, and
contains no proof or new Lean file.

## Repair of returned head 320e29509b58

The sole return diagnostic was that `lem-pur-etale-support-projection-shift-unit`
appeared in `proof_deps` but not in the union of proof-step `uses`. I removed
that unused edge from `proof_deps`. Step 4 already proves finite-level
invertibility using `lem-etale-proper-projection-formula-finite` and
`lem-pur-etale-open-derived-tensor`, then uses conservative evaluation. Thus
the extra theorem is unnecessary for the accepted proof. Both statement consumers
still cite `def-coef-etale-support-projection-map` as owner of the actual map,
so the earlier H2/H12 ownership repair remains intact.

The initial attempted repair added a citation to step 4, but the dry-run wrapper
reported that `proof` changes were NOT delivered because that field is not
worker-editable here. That attempted proof edit was reverted. The actual repair
changes only the redundant `proof_deps` entry and this report; the accepted proof,
mathematical statement, Lean modules and signatures are unchanged from the
returned delivery. The current live base was compared with the saved packet; its
proof and proof dependency list now agree exactly with this delivery.

The second reading for this repair checked all seven steps: the set of their
`uses` is exactly `proof_deps` (17 nodes), with no missing or unused edge.
The finite projection map remains the published canonical definition, and
its invertibility still follows from the existing proper/open argument.
All seven Lean files compiled cleanly via scompile.py; the repaired packet
then passed the required dry run before delivery.
