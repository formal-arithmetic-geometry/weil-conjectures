## Worker report

Statement-only delivery of `lem-sfb-space-flat-direct-image-base-change` in
`Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`. The primary declaration is
`AlgebraicGeometry.AlgebraicSpace.isIso_moduleBaseChange_of_flat`.
The node's statement, statement dependencies and accepted proof split are unchanged.
The previous stage-1 refusal does not prevent this stage-2 declaration: the current
node is split, has no Lean record, and appears at stage 2 in the queue. No repair note exists.

The source was read in `spaces-cohomology.tex`, lemma-flat-base-change-cohomology
(Tag 073K), clause (1), with i = 0, and `spaces-morphisms.tex`,
lemma-flat-morphism-sites (Tag 073C). The source assumes quasi-separatedness;
the node deliberately specializes to separatedness. Neither the source nor this
statement requires finite presentation, coherence, properness or Noetherianity.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| S is a scheme | `{S : Scheme.{u}}` in the explicitly bound section context |
| X is an algebraic space over S | `{X : AlgebraicSpace S}` in that context |
| T and T' are schemes over S | `{T T' : Over S}`; these retain their structure morphisms |
| f maps X to T over S | `f : X ⟶ schemeSpace T` |
| f is quasi-compact | `hqc : IsQuasiCompactPresheafMap f.hom.hom` |
| f is separated | `hsep : IsSeparatedPresheafMap f.hom.hom` |
| g is an S-morphism of schemes | `g : T' ⟶ T` in `Over S` |
| g is flat | `[Flat g.left]`, the existing scheme predicate |
| X' is X times_T T', with h and f' its projections | `{X' : AlgebraicSpace S}`, `h`, `f'`, and `hp : IsPullback h.hom f'.hom f.hom ((Scheme.fppfTopology.over S).yoneda.map g)`; this is the sheaf fibre product used by the recorded dependency, allowing any representative of its universal property |
| M is an O_X-module on the small etale site | `M : X.Modules` |
| M is quasi-coherent | `[M.IsQuasicoherent]`, the Mathlib local-presentation predicate, with the recorded small-etale slice instances |
| The canonical ringed etale topoi and their module operations | Existing `schemeSpace`, `Modules`, `moduleTensorPullback`, `moduleDirectImage`, `moduleTensorAdjunction`, `moduleTensorSection`, and chart scalar maps; no replacement sites, coefficient universes or arbitrary functors |
| beta goes from g-star f_* M to f'_* h-star M | `(moduleBaseChange f gSpace h f' w).app M`; its functor source and target are exactly these two expressions |
| The comparison f'-star g-star to h-star f-star is canonical | `moduleTensorSquare`, obtained from the uniquely local-tensor-normalized `moduleTensorComposition` on both paths, with the equality supplied by `hp.w` |
| beta is the adjoint of the specified comparison followed by h-star epsilon_M | `moduleBaseChangeCounit` is the natural comparison followed by the whiskered counit of `moduleTensorAdjunction f`; `moduleBaseChange` applies the functor-category adjunction `((moduleTensorAdjunction f').whiskerRight X.Modules).homEquiv` to exactly that composite |
| beta_M is an isomorphism | `IsIso ((moduleBaseChange ...).app M)` |
| The comparison is natural in M | `moduleBaseChange` is a natural transformation on the entire module category, so its naturality restricts to quasi-coherent modules; no independent naturality assumption |
| No further finiteness hypotheses | The complete signature above has none |

Supporting declarations belong to this node's specified canonical comparison and map,
and are all listed in `lean.declarations`. `moduleCompositeChart` composes the actual
maps of chart schemes. Its triangle is a named theorem with a proof docstring.
`moduleTensorComposition_existsUnique` states the ordinary tensor associativity
isomorphism with its full scalar normalization: c tensor (d tensor m) maps to
c times the actual pullback of d tensor m. Uniqueness follows because these tensors
locally generate. `moduleTensorComposition` selects this uniquely characterized
object, as permitted for universal-property constructions by AGENTS.md section 5;
it does not select a bare nonempty unnormalized isomorphism. The square comparison,
counit composite and adjoint transformation then have real data. All three theorem
proofs are `by sorry`; no theorem is proved, and no definition contains a sorry.

Dependencies read and used (declaration names in namespace
`AlgebraicGeometry.AlgebraicSpace` unless otherwise specified):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `structureSheaf`, `Modules`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsQuasiCompactPresheafMap`,
  `IsSeparatedPresheafMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with
  `Flat.iff_flat_stalkMap` connecting it to the node's stalkwise definition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`; its sheaf pullback and universal property explain
  the form of `hp`. The closure declaration is publicly available for constructing
  a concrete representative.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  `etaleModuleOverHasWeakSheafify`, `etaleModuleOverWEqualsLocallyBijective`
  instances; the theorem uses their underlying `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, constructed
  from the actual representable fppf sheaf; the recorded canonical enlarged-site
  framework is imported rather than duplicated.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleChartTarget`,
  `ModuleChart`, `moduleChartScalar`, `moduleTensorSection`,
  `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction`.

All already recorded statement-dependency modules are public imports. Already stated
proof dependencies are plain imports: the etale direct-image restriction, atlas
equalizer, quasi-coherent direct image, scheme Zariski/etale equivalence,
`exists_baseChange_affine_section_equiv`, and
`exists_tensorPullback_affine_sections`. The Mathlib proof leaves are imported from
`Pullbacks`, `Flat.Basic`, `RingHom.Flat`, `Smooth.Flat`, and the public scheme-flat
module (also supplying affine-open and etale facts through their imports).
Three proof-only nodes currently have no Lean declaration and consequently no
module import: `lem-sfb-space-module-pullback-quasicoherent`,
`lem-trf-space-qc-finite-affine-atlas-refinement`, and
`lem-trf-space-separated-affine-chart-overlap`. They are not needed to type the
statement, and their proof steps remain in the complete theorem docstring and DAG.
No missing statement dependency, new independent notion or dependency repair was needed.

Edge cases checked before writing: the zero module; empty source and empty base-change
scheme; g the identity; f the identity when X is a scheme; flat non-etale morphisms;
quasi-coherent modules with infinite presentations; arbitrary characteristic and
non-Noetherian rings. In the empty cases the section/tensor/adjunction constructions
still exist. Identity squares give the ordinary unit/counit normalization, rather
than an arbitrary isomorphism. No etale or finite-presentation condition is imposed
on g. The site object universe remains u+1 while section and ring carriers remain u,
as in the recorded algebraic-space interface. No universe equality was added.

Searches performed with `msearch.py` and recorded by that tool:

- LeanFinder: `Flat base change for the direct image of a quasi coherent module on an algebraic space`.
  Eight hits, including `Flat.isStableUnderBaseChange`, `Flat.flat_appLE`, and
  `Flat.comp`; none states the algebraic-space direct-image theorem.
- Loogle: `"AlgebraicGeometry", "baseChange"`. Twelve hits concerning scheme
  morphism properties and precoverages; none is this theorem.
- Mathlib grep: `flat.*base.change|base.change.*flat` in `AlgebraicGeometry`.
  Two hits, in `Geometrically/Reduced` and `SchemeTheoreticallyDominant`;
  neither concerns module direct-image comparison for algebraic spaces.
- LeanSearch: `Flat base change for direct image of quasi coherent module sheaves on algebraic spaces`.
  Eight hits, including module flatness, ring flatness under base change and
  scheme-flatness criteria; none is the requested statement.
- Direct ripgrep in `lean/WeilConjectures` and `lean/Sheaf`: the item id has no
  matching declaration; `flat.*[Dd]irect[Ii]mage|[Dd]irect[Ii]mage.*flat` gives
  unrelated derived scheme/coefficient material. `moduleTensorPullback` in the
  algebraic-space modules occurs only in the prescribed operations and their etale
  restriction theorem. The latter requires etale g and cannot state arbitrary flat
  base change. Searches for the introduced composition/square names found no existing
  declarations; the scheme `Scheme.Modules.pullbackComp` concerns different sites
  and is not a substitute for the prescribed algebraic-space tensor pullback.

Validation: the module compiled cleanly on the server via `scompile.py` (sandbox
and library checks, 2.4 s and 2.3 s before the final explicit dependency imports).
The only initial elaboration repairs were opening the existing Functor namespace
and specifying the type of the represented scheme map when applying full-subcategory
hom extensionality. These changed no mathematical hypotheses or conclusion.
The required dry run and final delivery recompile the final file.

No statement correction or STATEMENT-DISPUTED issue.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
