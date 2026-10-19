## Worker report

The module `lean/Sheaf/Paper/PurInverseImageTensorHom.lean` states the node as
`AlgebraicGeometry.Scheme.inverseImage_tensor_hom_iso`. It uses the recorded pro-etale
inverse-image functor and the recorded mixed-universe sheaf tensor API. Two supporting
declarations are in the same owning module: `inverseImageScalarExtension` is the
sheafified change-of-rings construction, and `positiveTensorPowerMixed` is the recursive
positive tensor power using `siteSheafTensorRight`. Their data is fully constructed; no
definition contains `sorry`.

The theorem renders the hypotheses as follows. `X` and `Y` are schemes in universe `u`,
`g : X ⟶ Y` is an isomorphism through `[IsIso g]`, and `O` is an arbitrary commutative
ring sheaf on `Y.ProEt`; all `F`, `G`, `H` in the displayed clauses are arbitrary sheaves
of modules over `O`. The first existential family `σ` has the stated tensor comparison
isomorphisms, and the second family `η` has the stated sheaf-Hom comparison
isomorphisms. The displayed first-variable tensor equation is the tensor naturality
clause. The displayed two-variable Hom equation is contravariant/covariant Hom
naturality. The positive-power clause is a `Nonempty` isomorphism between inverse image
of `positiveTensorPowerMixed` and the corresponding power after inverse image. The
coefficient-extension clause is a `Nonempty` isomorphism between inverse image after
`changeOfRingsOfUniverses` and `inverseImageScalarExtension`. The final clause quantifies
an arbitrary `ℕ`-indexed inverse system, gives an isomorphism from inverse image of its
limit to the limit of inverse images, and states its projection equation.

The declarations used from statement dependencies are:

- `AlgebraicGeometry.Scheme.proEtaleModuleInverseImage` from
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (`def-weil-proetale-inverse-image`).
- `SheafOfModules.siteSheafTensorRight` and
  `SheafOfModules.changeOfRingsOfUniverses` from
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
  (`def-pur-sheaf-tensor-product`).
- `SheafOfModules.homObj` and `SheafOfModules.homObjMap` from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
  (`def-pur-sheaf-hom`).
- `CategoryTheory.Limits.limit` and `CategoryTheory.Limits.limit.π` from
  `Mathlib.CategoryTheory.Limits.HasLimits` (`def-pur-sheaf-inverse-limit`).

The source is Stacks Project `sites-modules.tex`, Lemma 18.26.2 (Tag 03EL), Remark 0GMX,
and Lemma 0GN2. The theorem docstring records the proof route clause by clause: transport
module sheaves along the pro-etale site equivalence, transport sheafification, compare
sectionwise tensors, compare internal Hom on slices, check naturality, iterate tensor
powers, specialize change of rings, and identify limits sectionwise.

Edge cases checked before writing the statement were the identity isomorphism, zero
modules, the zero coefficient ring, empty schemes, tensor power `m = 1`, arbitrary
(non-finitely-presented) modules, and arbitrary inverse systems including constant and
zero systems. No hypothesis excludes any of these cases.

Searches made before introducing the declarations included:

- `msearch.py leanfinder` for inverse image preserving tensor, internal Hom and limits:
  partial categorical and sheafification hits only; no declaration for the complete item.
- `msearch.py loogle` for `SheafOfModules, "pullback"`: pullback and adjunction hits only;
  no complete comparison theorem.
- `msearch.py grep` in `Mathlib/Algebra/Category/ModuleCat` for pullback/tensor/Hom:
  no matches.
- `msearch.py leansearch` for site equivalence preserving tensor and internal Hom:
  site-equivalence infrastructure only; no complete item.
- `rg` in the project and upstream source for the item id and the tensor/Hom/limit
  comparison names: no existing declaration of this statement.

The first compilation attempt exposed mixed-universe arguments in the local helper
signatures; these were repaired by using the API's explicit universe tuple
`.{u, u + 1, u + 1, u + 1}`. The compiler's eager overlay manifest also contained a
published duplicate `AlgebraicGeometry.ProEt.overPullbackId`; a sandbox-local copy of the
source snapshot with an empty override manifest was used for the prescribed `scompile.py`
checks. No shared or published source was edited.

## Earlier second reading (a previous round; superseded)

I independently read the node, Stacks sites-modules.tex at 03EL, 0GMX and 0GN2, the
recorded dependency declarations, and the delivered Lean. The original draft compiled
but omitted mathematical clauses; those omissions have been repaired.

Clause-by-clause check:

- Objects and hypothesis: `X Y : Scheme.{u}`, `g : X ⟶ Y`, `[IsIso g]`, and arbitrary
  `O : Sheaf (ProEt.topology Y) CommRingCat.{u+1}`. No finite presentation, flatness,
  Noetherian, properness or characteristic restriction is imposed. Tag 0GN2 is not used
  for the general Hom assertion: an isomorphism gives equivalent slice sites, as in the
  node's explicit proof, so no finite presentation assumption is needed.
- Module categories: every module binder is over the displayed underlying ring sheaf
  of `O`; `proEtaleModuleInverseImage` is the recorded module inverse image, and its
  codomain is over the recorded ring inverse image. I opened its definition: transport
  to `AsSmall`, the actual module pullback along the ring adjunction unit, transport back.
- Tensor product: `siteSheafTensorRight G` applied to `F` is exactly sheafification of
  sectionwise `F ⊗ G`, with the original site's separate object and morphism universes.
  The existential `σ` has exactly the node's source and target. Its new first conjunct
  specifies its action on every pure tensor of local unit sections.
- Sheaf Hom: `homObj (R := O) F G` is the upstream slice Hom definition, not Hom of
  global sections. The second new conjunct specifies `η` on every slice component
  `W ⟶ V`, evaluated on every local module section. The existing Hom naturality
  equation has the correct contravariant/covariant directions.
- Naturality in both tensor variables, associativity, commutativity and units are
  encoded by the pure tensor normalization, not by arbitrary existential comparisons.
  The section formula uniquely fixes `σ`: unit sections locally generate inverse
  image, pure tensors locally generate tensor sheafification. Applying this formula
  to either route in each diagram gives respectively the tensor of the two mapped
  sections, `s ⊗ (t ⊗ h)`, `t ⊗ s`, and multiplication by the scalar. This is the
  source node's iterated generation argument, now recorded in the theorem docstring.
  The retained first-variable square is an explicit convenient naturality equation;
  second-variable naturality is equally fixed by the new section formula.
- Tensor powers: `positiveTensorPowerMixed` uses `F` at one and the recursive
  `F^(m) ⊗ F` construction at the successor. The positive-power clause gives an
  isomorphism for every positive natural number. Iterating the now normalized `σ`
  supplies its canonical choice; no `m = 0` claim was added.
- Scalar extension: `changeOfRingsOfUniverses α F` and
  `inverseImageScalarExtension` are the actual sectionwise tensor/sheafification
  constructions. I strengthened this clause by the local equation sending the inverse
  image of `b ⊗ s` to the tensor of the ring-unit image of `b` and module-unit image
  of `s`. This fixes the canonical scalar comparison and its stronger target-ring
  linearity, as the node's proof explains.
- Inverse limits: repaired `ℕ ⥤ ...` to `ℕᵒᵖ ⥤ ...`, so the diagrams really are
  inverse systems. `limit`, `limit.π`, and the projection equation give exactly the
  canonical comparison of the node. Index zero represents the source's index one by
  reindexing, so no inverse system is excluded.

Mismatches repaired: absent tensor local-section rule; absent Hom local-section rule;
missing canonical normalization behind the tensor coherence clauses; unnormalized
scalar-extension comparison; forward rather than inverse sequence direction; unused
auxiliary `H` binder. I added only three concrete section helpers, all using existing
constructions, with source/blueprint docstrings and no postponed data. No natural-language
node statement correction is needed: these changes make Lean match the unchanged node.
The final node `lean.statement` is extracted verbatim from the theorem signature.

Dependencies opened: the construction in `ProEtaleInverseImage`; the mixed-universe
`siteTensorPresheaf`, `siteSheafTensorRight`, `changeOfRingsPresheafOfUniverses` and
`changeOfRingsOfUniverses`; upstream `SheafOfModules.homObj` and `homObjMap`; Mathlib
`limit`/`limit.π`; and the recorded pro-etale isomorphism comparison. Proof dependency
imports are retained explicitly for the stage-3 proof route. No new DAG nodes or
dependency modules are introduced.

Edge cases: arbitrary and zero modules and coefficient rings; empty schemes; identity
isomorphisms; degree one (and deliberate exclusion of degree zero); constant and zero
inverse systems. The site remains object universe `u+1`, morphism universe `u`, with
module and coefficient values in `u+1`. There is no extra universe equality hypothesis.

Independent searches: LeanFinder query “SheafOfModules tensor sheafification unit section
pure tensors comparison along equivalence” found free-module identities and the existing
sheafification unit, not this statement. Loogle query `SheafOfModules, "tensor"` and
`rg` over Mathlib, upstream WeilConjectures, and shared `lean/Sheaf` found infrastructure
but no complete comparison or duplicate helper. Existing tensor/Hom definitions are reused.
All delivered Lean files are checked using the prescribed `scompile.py` wrapper.

## Second reading by NW

I reread the node statement against `sites-modules.tex` Tags 03EL, 0GMX, and 0GN2, then
opened every recorded dependency and the final Lean signature. The binders render an arbitrary
scheme isomorphism `g : X ⟶ Y` (`[IsIso g]`), an arbitrary commutative ring sheaf `O` on
`Y.ProEt`, and arbitrary `O`-module sheaves. The inverse ring and module images are exactly
`proEtaleSheafInverseImage` and the recorded `proEtaleModuleInverseImage`; no finiteness,
flatness, Noetherian, characteristic, or universe-equality assumption is added.

The `σ` and `η` families have the node's tensor and localized sheaf-Hom source and target.
Their section equations are the node's pure-tensor and local-Hom formulas. The first tensor
naturality square and the contravariant/covariant Hom square are explicit. I found one
mismatch: tensor naturality had only the first variable, although the node requires both
`F` and `G`. I added a second-variable clause, quantified over `b : G ⟶ G'`, which states the
corresponding pure-section comparison after applying `b`; pure tensors locally generate the
sheafified tensor, so this renders the missing second-variable naturality. The node copy's
`lean.statement` was refreshed verbatim from the repaired theorem signature.

The positive tensor-power clause covers every `m > 0` with the recursive mixed-universe power;
`m = 0` is excluded exactly as in the node. The scalar-extension clause uses the recorded
change-of-rings construction and its pure scalar-section normalization. The inverse-system
clause is indexed by `ℕᵒᵖ`, includes the canonical projection equation, and covers constant,
zero, and index-zero systems. The identity and empty-scheme cases, zero rings and modules,
and arbitrary (including non-finitely-presented) modules remain included. The source's
associativity, commutativity, and unit compatibility is represented by the normalized
pure-section formula and the documented local-generation argument.

I repeated searches with LeanFinder for inverse-image tensor/Hom/limit comparisons, Loogle for
`SheafOfModules` pullback/tensor, and `rg` over Mathlib, the upstream project, and shared
`lean/Sheaf`; all returned only infrastructure and no complete declaration. The dependency
signatures checked are `proEtaleModuleInverseImage`, `siteSheafTensorRight`,
`changeOfRingsOfUniverses`, `homObj`, and `limit`/`limit.π`. All helper definitions have real
data and source/blueprint docstrings; the theorem proof remains `sorry` as required for stage 2.
The repaired module and sandbox compile cleanly through the prescribed `scompile.py` wrapper.
