## Worker report

The module `Sheaf.Paper.SignedLineScalarTensorTower` states the entire node as seven
named theorem clauses. Every proof is `by sorry`. The four accompanying definitions
only spell out this node's signed powers and its normalization equations; none has
postponed data or chooses maps from an uncharacterized existence assertion. No node
statement is corrected. A new definition node binds the four unchanged canonical
scalar-extension maps already present in the live library; no dependency module is added.

Hypotheses and objects:

- The site is `C` with `Category.{vC} C`, `J : GrothendieckTopology C`, and an explicit
  `[HasFiniteLimits C]` on every theorem, including the final object. The recorded site
  module is imported; no alternative covering or sheaf category is introduced.
- Relative smallness uses coefficient and module universe `max uC vC u`. This includes
  the two independent site sizes and is closed under the recorded slice-Hom universe
  maximum. The sheafification and locally-bijective-equivalence instances are the
  usual small-site implementations of the source's size convention. There is no
  equality between object and morphism universes. Slice locally-bijective instances
  are bound explicitly where the published dual map needs them.
- `R S T : Sheaf J CommRingCat` are R0, R1, R2. `α`, `β`, and their categorical
  composite `α ≫ β` are iota01, iota12, and iota02 respectively; no independent third
  ring map needs an additional equality assumption.
- `L`, `K`, `N` are the three module sheaves in the recorded `ringedSiteModules`.
  Each `hL`, `hK`, `hN` is exactly a family `X : I → C` with `J.CoversTop X` and
  isomorphisms of the restrictions to `unit (R.over (X i))`. On a category with a
  final object `CoversTop` is precisely coverage of that final object. These are
  actual slice-sheaf isomorphisms, not sectionwise freeness at just one object.
- `b01`, `b12`, `b02` have the displayed scalar-extension isomorphism types.
  `hb` of `signedLineComparison_tower` is exactly their exponent-one tower equation.

Clause-by-clause translation:

1. `signedLinePower` uses the existing `scalarTensorPower R L n` in nonnegative
   degree and the recorded `homObj (scalarTensorPower R L (n+1)) (unit _)` in
   degree `Int.negSucc n`. Thus zero is R, one is L, all positive powers use the
   previously fixed association, and there is no negative-zero ambiguity.
2. `SignedLineComparisonNormalized` has zero equal to `scalarExtensionUnitIso`,
   one equal to the supplied `b`, and the positive successor formula on arbitrary
   local pure tensors. This formula is exactly the recursive binary comparison;
   pure tensor generators detect its equality as a sheaf map. The negative clause
   is `scalarExtensionDualMap α ... ≫ homObjMap (B (n+1)).inv (𝟙 _)`, which is
   beta followed by precomposition with the inverse positive comparison.
3. `signedLineDual_isIso` asserts invertibility of that actual canonical beta for
   each positive exponent. The beta formula itself is the published
   `scalarExtensionDualMap_tmul` and `scalarExtensionDualMap_tmul_slice`, read in
   the imported module: on scalar-first generators it is `s*t*α(phi(x))`, equal
   to the node's `α(phi(x))*s*t` by commutativity. An `IsIso` proof turns this
   actual map into an isomorphism; there is no arbitrary substitute for beta.
4. `exists_signedLineComparison` gives all signed isomorphisms with the above
   normalization, the exact evaluation equality
   `α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x) * s * t`, and the signed
   local coordinate formula `(α.hom.app U r * s) • f m`.
5. `SignedLineBasisPowers L U e` specifies genuine bases on every object of the
   slice, degree zero 1, recursive positive basis tensors, and negative basis
   functionals evaluating to 1 on the positive basis on every slice object.
   `existsUnique_signedLineBasisPowers` supplies these for every local basis of L;
   the local coordinate clause therefore has no vacuous basis assumption.
   Compatibility at exponent one is exactly
   `b.hom.val.app U (scalarExtensionSection α L U 1 (e 1)) = f 1`.
6. `existsUnique_signedLineProduct` supplies the canonical isomorphisms μ for
   *all* `a b : ℤ`; `SignedLineProductNormalized` is precisely
   `e^a tensor e^b ↦ e^(a+b)` on every basis chart. Uniqueness characterizes
   the map given by associativity, symmetry and evaluation contractions: the
   full proof docstring checks all four sign cases by contracting opposite
   pairs, including the dual-of-power identification. This is a normalization
   of maps on the actual tensors, with no unrelated monoidal structure chosen.
7. `signedLineComparison_tensor` states the exact multiplication square as an
   equality of actual sheaf morphisms. Sigma is the published
   `scalarTensorBinaryIso α ...`, followed by tensoring the two B maps; the
   other side is `changeOfRingsHomOfUniverses α _ μ.hom ≫ B(a+b).hom`.
8. The coefficient associator for arbitrary M is the existing
   `scalarExtensionTowerIso`, now owned by
   `def-sp-canonical-scalar-extension-maps`. Its actual `hom` and `inv` are
   `scalarExtensionTowerForward` and `scalarExtensionTowerReverse`.
   Their published `_tmul` theorems give the forward scalar `t * β(s)`
   (equal to `β(s) * t` by commutativity) and the inverse with intermediate
   scalar 1. These constructions require neither local freeness nor flatness.
   No existence theorem or normalization predicate re-specifies this object.
9. `signedLineComparison_tower` assumes the supplied exponent-one equation and
   concludes `A(m).hom ≫ B02(m).hom = Eβ(B01(m).hom) ≫ B12(m).hom` for every
   signed m, where A(m) is literally the existing `scalarExtensionTowerIso`
   evaluated on `signedLinePower L m`. The exponent-one hypothesis uses
   `scalarExtensionTowerIso α β L`, since the degree-one power is L.
   Its four universe parameters are explicit; there are no A or hA binders.
10. `signedLineComparison_identity` assumes exactly the identity ring map and
    multiplication comparison at exponent one, and identifies every signed B
    with the unit comparison by its formula on every arbitrary pure section:
    `B(m)(x tensor s) = s • x`. Pure tensors determine a sheaf map, so this is
    equality with the tensor-unit map, not only equality on basis elements.

The module uses the scalar-first convention of the existing change-of-rings API.
`scalarExtensionSection α M U s x` is the node's right-scalar tensor `x tensor s`.
No assumption on flatness, characteristic, points, or nonzero coefficients occurs.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the recorded site interface; actual
  site and sheaves are Mathlib's `GrothendieckTopology` and `Sheaf`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  tensor module, publicly importing `siteSheafTensorRight`,
  `siteSheafTensorSecondMap`, `siteSheafTensorTmul`, and the existing tensor.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj` and `homObjMap` (read their full definitions and docs).
- `Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions`: `scalarTensorPower`,
  `scalarExtensionSection` and the recorded scalar comparison structures.
- `Sheaf.Paper.ScalarExtensionBinaryCoherence`: `scalarExtensionUnitIso`,
  `scalarTensorBinaryIso`, their pure-section formulas, and tensor coherence.
- `Sheaf.Paper.ScalarExtensionDualEvaluation`: `scalarExtensionDualMap` and
  `scalarExtensionDualMap_tmul`, including its full slice variant.
- `Sheaf.Paper.ScalarExtensionDualTowerCore`: `scalarExtensionTowerIso`,
  `scalarExtensionTowerForward_tmul` and `scalarExtensionTowerReverse_tmul`.
  This is the direct public import, exposing the preceding canonical definitions
  through its public imports.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`: `over`;
  its full signature and the `overFunctor`, `Hom.over`, `overMap` docs were read.
- Proof imports: `exists_localizedSiteTensorRestriction` from the corresponding
  Sheaf module; `existsUnique_hom_of_cover` and `tensor_bilinear_universal` from
  their upstream WeilConjectures modules. The binary and dual proof dependencies
  remain in proof_deps. Their canonical definitions are now a statement
  dependency through `def-sp-canonical-scalar-extension-maps`.

The item's `stmt_deps` gains the already-landed nodes
`def-sp-scalar-tensor-comparison-data` and `def-pur-localized-ringed-site`,
and the new definition node `def-sp-canonical-scalar-extension-maps`.
The two theorem nodes `lem-sp-scalar-extension-binary-coherence` and
`lem-sp-scalar-extension-dual-evaluation` are retained in proof_deps and are
absent from stmt_deps. All original statement dependencies are retained.

Searches (all run for Q48 and this exact item):

- `msearch.py leanfinder`, query "Scalar extension of signed integer tensor powers
  of invertible sheaves commutes with evaluation tensor multiplication and towers":
  eight hits, including `ModuleCat.extendScalarsComp_hom_app_one_tmul`, Picard-group
  tensor multiplication, and `LinearEquiv.lTensor_zpow`/`rTensor_zpow`. These are
  ordinary modules and powers of automorphisms, not this sheaf theorem.
- `msearch.py loogle`, query `Module.Dual.baseChange`: six hits, including
  `Module.Dual.baseChange_apply_tmul` and `Module.Dual.baseChange_baseChange`.
  They are algebraic duals of modules, not the slice internal dual and signed maps.
- `msearch.py grep`, query `signed.*[Pp]ower|[Ll]ine.*scalar|baseChange.*[Dd]ual`:
  25 hits; none states signed powers of sheaves with all tensor and tower equations.
- `msearch.py leansearch`, query "scalar extension commutes with integer tensor
  powers of line sheaves and their dual evaluation": eight hits, including
  `TensorPower.pairingDual`, tensor powers of linear automorphisms and localization.
  No exact sheaf statement.
- `rg` in Mathlib's ModuleCat, the upstream ModuleCat tree and `lean/Sheaf` for
  signed powers and the proposed names: no name clash and no exact general-site
  statement. The generic `NormalizedSignedPowers.signedPower` uses a chosen closed
  monoidal `ihom`; it does not supply the actual independent-universe sheaf tensor
  and slice `homObj` interface here. `coefficientTwistLine` and
  `signedLineTensor_equivalence` apply to the pro-etale site of a scheme, not an
  arbitrary site. Their generic ingredients (`scalarTensorPower`, `homObj`) are
  reused rather than copied. Source grep for the item id has no declaration.

Edge cases checked before and during writing: zero exponent; n=0 in `negSucc n`
means -1; positive first successor; (a,b)=(0,0), (1,-1), (-2,1), (2,-1);
identity coefficients; the composite tower; a one-object site; nonflat Z→Z/2;
the zero coefficient ring; cover members with zero sections; and a change of
basis by an arbitrary unit. The slice-basis bijectivity condition still works
over the zero ring. A cover can have empty index when the topology permits it;
no Nonempty assumption is added. Finite limits supply the final object, so an
empty category is rightly outside this node's hypotheses. No statement dispute.

All natural-language proof steps 1--10 are included in the relevant theorem
proof docstrings, with the gluing, rank-one inverse, four sign cases, balanced
associator and its inverse, scalar square, tower and identity calculations.

Validation: compilation uses only `scompile.py` against the live published build;
no local compiler, build, git mutation or edits to the shared repository were run.
The saved packet passed the required initial dry run (d0fb42e5081). The repaired
module then compiled with no errors or warnings using scompile.py (sandbox and
library checks). The repaired packet passed the fresh dry run: commit cec33beb8e5 passes preflight
and compiles; nothing pushed by that check. The new node has status split, all
required fields and an existing declaration binding; the item has an exact
primary signature and records all eleven retained declarations.

## Second reading by Q48

This is the author's second pass over the complete node and final file; the brief
forbids starting another agent and assigns independent review to the maintainer.
I compared every displayed formula with the Lean morphism directions and every
local expression with the scalar-first API. This pass caught non-inferable maxima
in the owned helpers' universe arguments; those uses now pass explicit universes.
It also caught that the finite-limit section variable could be omitted by Lean;
every theorem now binds `[HasFiniteLimits C]` explicitly. The local basis zero and
dual normalizations use explicitly typed coefficient-ring ones. I retained all
three local-line hypotheses in the tower theorem and both in the tensor theorem.
The signed normalization predicates are actual equations. On the repair pass I
removed both `SignedLineTowerAssociatorNormalized` and
`exists_signedLineTowerAssociator`, and replaced every tower occurrence of the
arbitrary A family by the existing `scalarExtensionTowerIso`. I read its full
signature, definition, forward formula and inverse formula: they have precisely
the direction and normalization required by the node. The explicit universe
arguments preserve `max uC vC u` for every signed power, including its internal
dual. The exponent-one and all-integer tower equations use that same map.
I also read all four canonical-map definitions against the new definition node:
the dual comparison remains a morphism for arbitrary M, and invertibility is
asserted only in the item's rank-one specialization. The unit and binary maps
use the coefficient module universe; the tower map also permits a larger module
universe. No mismatch of the mathematical statement remains in this reading.


## New nodes

`def-sp-canonical-scalar-extension-maps` owns the already constructed
`SheafOfModules.scalarExtensionUnitIso`, `scalarTensorBinaryIso`,
`scalarExtensionDualMap` and `scalarExtensionTowerIso`. Its `existing: true`
record names `Sheaf.Paper.ScalarExtensionDualTowerCore`, whose public imports
expose the other definitions from `ScalarExtensionBinaryCoherence` and
`ScalarExtensionDualEvaluation`; lean.note lists their actual modules. No source
module or declaration is duplicated. The node defines the unit by multiplication,
the binary map and its balanced inverse, the arbitrary-module internal-dual
morphism by evaluation on every slice, and the tower isomorphism and its inverse.
It does not assert invertibility of an arbitrary module's internal-dual map.
The source is the item's blueprint sentence, with Stacks 03EK, 04TT and 0GMX.
It builds on `def-sp-scalar-tensor-comparison-data` and `def-pur-sheaf-hom`.

New-node searches: `msearch.py leansearch` with “Canonical scalar extension maps
for module sheaves unit binary tensor internal dual and composition of ring maps”
returned eight ordinary-module hits headed by `ModuleCat.ExtendScalars.map'` and
`ModuleCat.extendScalars`. `msearch.py loogle ModuleCat.extendScalarsComp`
returned eleven ordinary-module hits, including its pure-tensor formula.
`msearch.py grep 'extendScalarsComp|baseChange.*[Dd]ual'
Algebra/Category/ModuleCat` returned six hits in Mathlib's ChangeOfRings and
Pseudofunctor modules. The actual search-log results are in mathlib_searches.
`rg` on the upstream ModuleCat and project Paper directories found the four
exact Sheaf constructions named above, and no upstream counterpart. `rg -l`
over DAG JSON files found only the four theorem nodes for binary coherence,
dual evaluation, dual local invertibility and dual tower coherence; none is a
definition node owning these maps. `blueprint_refs.py search scalarExtensionTowerIso`
returned zero blueprint nodes. The ancestor query returns
`prop-weil-twist-preserves`, used in blueprint.from with the item's via path.
The new node supplies definition ownership for existing declarations, as requested
by the return; it introduces no additional construction.

## Returned delivery repair

Return L, immutable head `67b6ac920743`, H2: canonical definitions were only
accounted for through theorem nodes. The saved packet still had precisely this
issue despite passing its initial dry run. I replaced the two added theorem
statement dependencies with `def-sp-canonical-scalar-extension-maps`, whose
existing record lists all four canonical maps. Both theorem nodes remain in
proof_deps unchanged. The live main item has no lean record and only the original
five stmt_deps; the repaired item changes only lean and adds the three required
definition dependencies. It retains its entire statement, source, proof and
proof_deps verbatim from current main.

Return L, H4: the new definition node also owns `scalarExtensionTowerIso`.
The item imports its existing module and uses this exact construction in both
its exponent-one hypothesis and its all-integer tower conclusion. The duplicate
associator-normalization definition and associator-existence theorem were removed,
and lean.declarations and lean.statement were updated to match the file.
The published forward and reverse formulas cover arbitrary M, zero rings and
non-flat coefficient maps. Signed powers in the tower still include 0, 1 and -1,
with no extra equality between site universes. The advisory overlap of
`signedLineDual_isIso` with the local-iso lemma concerns the same canonical beta;
its signed-power rank-one specialization is retained, as the return accepted its
statement and only required the two interface repairs above.
