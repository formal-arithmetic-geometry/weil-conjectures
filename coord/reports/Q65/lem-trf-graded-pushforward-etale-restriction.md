## Worker report

The module `Sheaf.TraceFormula.GradedPushforwardEtaleRestriction` states this node in two
sorry-only theorems, `AlgebraicGeometry.AlgebraicSpace.graded_pushforward_etale_restriction`
and `AlgebraicGeometry.AlgebraicSpace.graded_pushforward_etale_restriction_line_powers`.
All other declarations are real definitions or a structure specifying this node's
normalized comparison data. No object or map is selected from these theorem statements.
The natural-language statement, proof and proof dependencies are unchanged.

Sources read: Stacks `spaces-properties.tex`, lemma-pushforward-etale-base-change-modules
(Tag 03LX), including its tensor-pullback footnote; `spaces-descent.tex`,
lemma-descending-property-ample (Tag 0D3C), the section algebra and psi_d/psi paragraphs.
The former applies to arbitrary modules and arbitrary f for an etale base change.
The latter identifies the maps psi_d as the actual counits and explains their assembly.

Hypothesis and clause correspondence:

- S is the explicitly bound `S : Scheme.{u}`. The four objects are `AlgebraicSpace S`,
  and f, g, h, f' are their actual morphisms. `hg : IsEtale g.hom.hom` is the only
  etaleness hypothesis. `hp : IsPullback h.hom f'.hom f.hom g.hom` expresses X' as the
  specified fibre product without choosing a presentation. The data's field `hh`
  records the resulting etaleness of h. There are no finiteness, separatedness,
  quasi-coherence, surjectivity, or representability hypotheses on f.
- `B : ℕ → X.Modules` is the family in every nonnegative degree. The existing
  `EtaleGradedModuleAlgebra B` gives both scalar-linear homogeneous pairings, compatibility
  with every site restriction, a module unit, associativity, ordinary commutativity and
  both unit laws. This is the existing sheaf-tensor/bilinear interface, with no cochain
  signs and no replacement of module sheaves by sets of global sections.
- All module operations are the recorded `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`, and `moduleTensorSection`. For etale h and g the statement
  uses `pullback h hh` and `pullback g hg`, their restriction presentation. The normalized
  theorem `moduleTensorPullback_etale_restriction` in the imported dependency identifies
  this with tensor pullback on every local tensor, including arbitrary scalar factors.
- `restrictedAlgebra` with `restrictedProducts : IsGradedEtaleRestriction ...` makes B'_d
  exactly `(pullback h hh).obj (B d)` and fixes every product and scalar-valued unit
  to restriction of the original operations. `directAlgebra`, `directAlgebra'`,
  `directProducts` and `directProducts'` use `HasChartwiseGradedDirectImage` to specify
  the direct-image products and unit by their projections on EVERY scheme chart.
- `beta d` is the stated degree isomorphism. `sections` says that after every chart
  projection its component is the same section on the identical underlying chart;
  `moduleChartBaseChange ... hp.w` is the recorded identification of chart triangles.
  Thus the comparison is canonical, not an arbitrary isomorphism of the two modules.
- `restrictedDirectAlgebra` and `restrictedDirectProducts` are g^* of the direct-image
  algebra. `algebraHom` together with `algebraHom_degree` says exactly that beta preserves
  every homogeneous product and the degree-zero unit. Its components are all invertible
  because they are the homs of `beta d`.
- `source`, `target`, `direct`, `direct'` and their four `IsColimit` fields are the
  coproducts of B, B', f_*B and f'_*B'. This uses cofans to cover every realization of
  the canonical coproduct. `restriction_colimit` and `source_restriction_colimit` assert
  the pullback/coproduct comparisons. `total` with `total_degree` is exactly the sum of
  beta through that comparison. The homogeneous algebra homomorphism makes this an
  isomorphism of unital commutative graded algebras on these coproducts.
- `lambda` is the canonical h^*f^*/f'^*g^* comparison. `lambda_tensor` fixes it by scalar
  multiplication on arbitrary local tensors, with both coefficients a and b arbitrary.
  This agrees with the existing normalized comparison of the degree-zero dependency.
- `evaluation_colimit` and `evaluation_colimit'` specify the coproduct comparisons for
  the actual tensor pullbacks f^* and f'^*. Both evaluations in `evaluation` are the
  existing `evaluationTotal`, defined as descent of the actual adjunction counits.
  `sourceTotal` and `sourceTotal_degree` are the comparison for h^*(coproduct B).
  The field `evaluation` is precisely h^*epsilon_f = epsilon_f' after f'^*beta and
  lambda, with every source and target comparison displayed in the equation.
- `counit_tensor` and `counit_tensor'` express a tensor s with arbitrary scalar a
  mapping to a times the compatible-section chart projection. Along with `sections`
  and `lambda_tensor`, they give the same local a times s|_W formula on both paths.
  They do not only check the unit scalar or assume sections globally are pure tensors.
- The second theorem binds a line module `L` with the recorded `X.IsLineModule L`.
  It uses exactly `evaluationLinePower X L d`, the existing tensor powers transported
  from the small affine site through the actual module equivalence. `theta d` identifies
  their restriction with `evaluationLinePower X' ((pullback h R.hh).obj L) d` for EVERY d.
  `HasCanonicalEtalePowerProducts` specifies both algebras on an affine basis by the
  existing `evaluationPowerAddIso` and `evaluationSmallTmul`; it also specifies the unit
  by the unchanged regular functions and asserts that this zero-power unit is invertible.
  `gradedPowerChartIso` is the actual equivalence counit, not an arbitrary chart iso.
  `thetaHom` and its component equation preserve all these products and the unit.
  Its unit law identifies h^*O_X with O_X' in degree zero. `gradedPowerOneIso` and the
  first-power equation fix theta_1 by the usual tensor unitor. These normalizations
  characterize the iterated canonical tensor comparison. The witness R supplies the
  full algebra and evaluation comparison for the powers. The last equation explicitly
  transports the actual f' counits along theta to evaluation into the ACTUAL powers of
  the restricted line module; summing it transports R's total evaluation square.

Statement dependencies for these constructions are the landed definitions
`def-trf-etale-graded-module-algebra`,
`def-trf-etale-module-evaluation-tensor-powers`, and
`def-sfb-space-small-ringed-model`, and the new existing-declaration definition
owner `def-trf-module-chart-etale-base-change`. No conclusion of
`lem-trf-graded-evaluation-zariski-etale-comparison` is used. The degree-zero
comparison theorem remains a proof dependency; its plain chart construction is
cited through the new definition owner. Both theorem signatures are unchanged.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, `EtaleSite`,
  `etaleTopology`, `structureSheaf`, `Modules`, `pullback`, `etaleMap`, `IsLineModule`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `moduleChartScalar`, `ModuleDirectImageModel.projection` and its limit/naturality
  interface, `moduleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`, `moduleTensorSection`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`;
  these justify the cartesian algebraic-space square and derived etaleness of h.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, exactly
  `SheafOfModules`, as used by `AlgebraicSpace.Modules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal` and the independent-universe sheaf-tensor interface. The
  small-affine tensor construction is the existing one, not a new tensor definition.
- `Sheaf.TraceFormula.EtaleGradedModuleAlgebra`: `EtaleGradedModuleAlgebra`, `.Hom`,
  and its coproduct interpretation `.total`.
- `Sheaf.TraceFormula.EtaleModuleEvaluationTensorPowers`: `evaluationCounit`,
  `evaluationPullbackCofan`, `evaluationTotal`, `evaluationSmallPower`,
  `evaluationLinePower`, `evaluationPowerAddIso`, `evaluationSmallTmul`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`, exposed by the preceding
  module and explicitly publicly imported: `SmallEtaleModel`, `smallEtaleInclusion`,
  `smallModuleRestriction`, `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`:
  `moduleChartBaseChange`, now owned as a definition by
  `def-trf-module-chart-etale-base-change`; the existing theorem conclusions
  `moduleTensorPullback_etale_restriction` and `etale_module_pushforward_restriction`
  are used only by the proof plan.
- Proof imports: `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`
  (`SheafOfModules.exists_localizedSiteTensorRestriction`),
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
  (`SheafOfModules.tensor_bilinear_universal`),
  `Sheaf.AlgebraicGeometry.SpaceChartTensorRealization`
  (`space_chart_adjunction_tensor_realization`), `Mathlib.CategoryTheory.Adjunction.Limits`
  (`Adjunction.leftAdjoint_preservesColimits`), and
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
  (`PresheafOfModules.sheafification`, `sheafificationAdjunction`). All already recorded
  proof dependency modules are imported, with proof-only dependencies non-public.

Edge cases checked before writing: degree zero and the cases m=0 or n=0 are included;
all homogeneous objects may be zero; schemes and charts may be empty; etale g need not
be surjective; f may be the identity or arbitrary, with no qc or separatedness;
arbitrary scalar coefficients, their zero values and finite linear combinations are
covered by the tensor formulas and linear module maps. Infinite coproducts are sheaf
coproducts: no claim about commuting their sections with direct sums is made. The small
affine model preserves coefficient universe u without identifying the u+1 object
universe of all charts with u.

Searches for an existing statement:

- msearch leanfinder: "Etale base change of graded direct image algebra sheaves preserves
  homogeneous products unit and adjunction counit" returned 8 hits, all unrelated Proj
  and homogeneous-localization constructions. No matching theorem.
- msearch loogle: `"baseChange", "counit"` returned 0 hits.
- msearch grep: `graded.*base[Cc]hange|etale.*counit|counit.*etale` returned two matches in
  `Mathlib/RingTheory/GradedAlgebra/TensorProduct.lean`, concerning algebraic base change
  of graded modules, not this sheaf/counit statement.
- msearch leansearch: "Etale restriction preserves graded direct image algebra and tensor
  pullback evaluation counit" returned 8 hits about ordinary scheme restriction counits,
  ring etaleness and Proj sections; none states this theorem.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for this node id,
  `graded_pushforward`, and `graded.*etale.*restriction` found no existing statement.
- rg for the graded-algebra and tensor-power interfaces found the two landed nodes
  explicitly added above, so their actual definitions were reused. The earlier H2 repair
  extracted the plain helpers into their own now-landed definition module while
  preserving their data and names. Exact-name searches
  across Mathlib, WeilConjectures and Sheaf found no collision for any new declaration.

Validation: scompile.py checked this file in module mode both as its sandbox probe and
as `Sheaf.TraceFormula.GradedPushforwardEtaleRestriction`, with no errors or warnings.
The two theorem proofs are exactly `sorry`. Auto-implicit binding is disabled and every
universe and section variable is explicitly declared. No statement dispute or mathematical statement correction is required. The definition ownership and direct dependency repairs are detailed below.


## Repair of returned head 9a3e7d59a5ca

1. `GradedPushforwardEtaleRestriction.sections` and `.lambda_tensor` use the
   exact existing `AlgebraicGeometry.AlgebraicSpace.moduleChartBaseChange`.
   New definition node `def-trf-module-chart-etale-base-change` records this
   declaration with `existing: true`, its existing module, and no `lean.file`.
   The item's `stmt_deps` now names this definition node. There is no second
   definition, no renamed wrapper, and no extra statement premise from the
   degree-zero comparison theorem. The declaration's full signature and body
   were read locally and through the current server source.
2. `gradedPowerChartIso`, `gradedPowerOneIso`, and
   `HasCanonicalEtalePowerProducts` use `SmallEtaleModel`,
   `smallEtaleInclusion`, `smallModuleRestriction`, and
   `smallModuleEquivalence`. Their landed owning node
   `def-sfb-space-small-ringed-model` is added directly to `stmt_deps`.
   Its module `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel` is
   explicitly publicly imported. Its full interface and docstrings were read.

Only these dependency additions, the Lean record's note/date, and the explicit
public import change in this repair. The statement, proof, proof dependencies,
both Lean theorem signatures, and all construction bodies are unchanged.
There is no statement correction and no mathematical dispute.

## New nodes

`def-trf-module-chart-etale-base-change` gives definition ownership to the
existing chart transport used by the section and tensor formulas. For any
commutative algebraic-space square with etale horizontal arrows, it takes a
chart `(T -> X', T -> V)` to the same scheme and same map to V, with its map
to X composed with h. Commutativity supplies the triangle over Y. The node
records exactly `AlgebraicGeometry.AlgebraicSpace.moduleChartBaseChange` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`,
with `existing: true`; no module or declaration is added. Stacks 03LX and its
tensor-pullback footnote identify these unchanged charts in the localization
comparison. The construction itself only needs square commutativity, not its
being cartesian; its additional h-etale witness is already a field of the
item's comparison structure. The old theorem node remains a proof dependency.

Searches run on 2026-10-25: msearch LeanSearch query "Canonical change of scheme
charts in an etale base change square of algebraic spaces" returned eight
scheme/ring etaleness hits; msearch LeanFinder query "Algebraic space etale base
change module chart canonical functor on compatible sections" returned eight
etaleness/forgetful-functor/differentials hits. msearch Mathlib grep
`moduleChartBaseChange|ModuleChart|etaleMap` returned no hits. Exact DAG/project
searches located the sole declaration in the existing theorem module and
only theorem-node ownership/consumers, with no upstream declaration.
Blueprint search "chart base change" returned zero nodes; the ancestor tool
gave `lem-trf-local-term-locality`. Full returned search text is in the new
node's `mathlib_searches` and the sandbox `chart-owner-*.txt` logs.

Edge cases for the reused definition: the square need not be cartesian, g and h
need not be surjective, f and f' are arbitrary, and empty charts cause no extra
condition. The resulting scheme and its map a are literally the input scheme
and a; the only changed data is its structural map to X. All universes are those
of the existing declaration. The small affine model retains section universe u.

## Prior ownership repair

The eight evaluation/tensor-power definitions were extracted without duplicate
names and landed by maintenance in b9b4a88a3126dd0802813e79ee8302d7804d9a4f.
The item uses their landed definition node and module. Those companion files
are adjacent `.maintenance-b9b4a88a312.bak` files in the sandbox and are not
part of this delivery. The previous item delivery was 9a3e7d59a5c; this repair
adds the two definition dependencies requested by its independent review.

## Repair validation

scompile.py compiled the revised item in sandbox and library module mode with no
errors or warnings (58.0 s and 56.0 s). deliver2.py --no-push then compiled the
item and the existing-declaration probe and accepted the complete packet at
c4279526500. The staged node changes include the new definition-owner JSON and
both requested item stmt_deps additions. Exact logs: chart-owner-compile.log and
chart-owner-dry-run.log. The lean.statement remains verbatim; only the public
small-model import changes the Lean file.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
