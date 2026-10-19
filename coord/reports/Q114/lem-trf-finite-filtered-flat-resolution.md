## Worker report

This is a new stage-2 statement packet replacing the misrouted stage-1 packet
8c742a65578d. The supplied sandbox contained only .brief markers, not the old
report or split. I read the current main-branch node and the released stage-1
repair note. This packet keeps its statement, source, proof and proof_deps
unchanged, and does not deliver the two non-definition cylinder/comparison
nodes from the returned head. The stage-1 re-split is a separate maintenance
request; no attempt is made to route that split through stage 2 again.

The item is stated by
`SheafOfModules.FilteredFlat.finite_filtered_flat_resolution` in
`Sheaf.Algebra.Homology.FiniteFilteredFlatSheafResolution`. It has precisely
one postponed theorem proof. Its module/docstring spells out all fourteen
steps of the current base proof, including the filtered cylinder comparison
and the Koszul swap. Nothing is claimed proved at this stage.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Small ringed site, commutative coefficients, containing module universe | `{C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})`. The containing-universe/small-site condition is expressed by essential smallness at `r`; object, morphism and coefficient universes are independent. |
| Module sheaves | `Modules R` is the recorded `ringedSiteModules` abbreviation, with module universe `r`, applied to the forgetful image of `R` in ring sheaves. No replacement module category is constructed. |
| Fixed integers a ≤ b | Each clause quantifies `a b : ℤ` and assumes `a ≤ b`; the equivalence family takes this inequality as an explicit dependent argument. |
| Decreasing subcomplex filtration, whole at p ≤ a, zero at p > b | `Complexes R a b` is exactly the existing `UniformFilteredComplexes ... (some (a,b)) (CochainComplex.minus ...)`. Its endpoint equalities imply all the stated step equalities by antitonicity. |
| Bounded above M and P | The existing `CochainComplex.minus` in `Complexes` requires a degree N and `IsStrictlyLE N`; `FlatComplexes` is its full subcategory. No common cochain bound or lower bound is imposed. |
| Strict termwise epimorphism P → M | `∃ (P : FlatComplexes R a b) (f : P.obj ⟶ M), ∀ p n, Epi ((FilteredObject.restrictionSteps f.hom p).f n)`. This is epimorphic in module sheaves, not sectionwise surjectivity. |
| Filtered quasi-isomorphism | `∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom p)` uses the existing canonical map of quotient complexes. |
| Split finite sums of flat terms in the permitted grades | `IsSplitFlat` gives a finite family indexed by `Fin m`, an integer label per summand, an actual coproduct isomorphism in each degree and `IsFlatOnSite` for every summand. Every filtration step is the finite supremum of images of its permitted labelled injections. Fixed endpoint bounds force all summands outside `[a,b]` to be zero; delete them and combine summands with equal labels to obtain exactly the node's sum indexed by `[a,b]`. Splittings are independent for each n, with no differential equation. |
| All models' underlying and graded complexes K-flat | The second conjunct universally quantifies every `P : FlatComplexes R a b`, and asserts the recorded `IsKFlatIndependentCoefficients` for its underlying complex and every `filtration.gradedPiece p`. Thus this is not limited to the chosen resolution. |
| Localization of split-flat homotopy category equivalent to bounded-above finite filtered derived category | `flatHomotopyQuasiIso` is defined on filtered homotopy classes, and its formal `.Localization` is the source of each `E a b hab`. The target is the existing chain-map `UniformFilteredDerived`. The natural isomorphism after `flatHomotopyQuotient ⋙ ...Q` forces this equivalence to be induced by inclusion of the actual chain maps. It is not an arbitrary equivalence of categories. |
| Compatible with interval inclusions | The square uses the actual `widenFlatLocalization` and `widenDerived`, both localization lifts of unchanged objects and arrows. The single family `E` is normalized on chain maps for every interval. The displayed square isomorphisms are the canonical localization comparisons; that characterization also gives coherent choices for nested intervals. |
| Any finite filtered W, every grade acyclic | `W : FilteredObject (CochainComplex (Modules R) ℤ)`, `W.filtration.IsFinite`, and `∀ p, (W.filtration.gradedPiece p).Acyclic`. W has no cochain bound. Its filtration interval need not equal P's. |
| Convolution total tensor acyclic on every grade | The final conjunct asserts existence of an actual decreasing `F` on `tensorTotal ...`, `IsConvolution ... F`, and `∀ s, (F.gradedPiece s).Acyclic`. `IsConvolution` equates each step with the image of the coproduct of the actual tensor-of-inclusions over `(p,s-p)`, exactly the sum of images in the node. Existence is concluded, not assumed as a potentially vacuous input. |
| Two factors reversed | A separate existence/acyclicity clause uses `tensorTotal R W.obj P.obj.obj.obj` and `IsConvolution R W P.obj.obj F`. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  arbitrary ringed-site module sheaves, rather than scheme-only modules.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
  `SheafOfModules.IsFlatOnSite`: exactness of the canonical sheafified tensor
  functor; explicit site/ring/module universes are retained.
- `Sheaf.Algebra.Homology.KFlat`,
  `CochainComplex.IsKFlatIndependentCoefficients`, and its named canonical
  tensor-localization/zero-preservation infrastructure: the actual total-tensor
  acyclicity definition, with no forced identification of site universes.
- `Sheaf.Algebra.Homology.UniformFiniteFilteredLocalization`,
  `uniformFilteredProperty`, `UniformFilteredComplexes`,
  `uniformFilteredQuasiIso`, `UniformFilteredDerived`: the existing uniform
  finite interval and chain-map localization, used unchanged.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`,
  `CategoryTheory.DecreasingFiltration` (read through `scompile.py --source`
  because the older source checkout lacks it); its existing `FilteredObject`.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`,
  `DecreasingFiltration.complexStep` and `gradedPiece`, and the imported
  `Sheaf.CategoryTheory.FiniteFiltrationInduction` declarations
  `FilteredObject.restrictionSteps` and `FilteredObject.gradedMapSteps`.
- Mathlib `Homotopy`, `CategoryTheory.Quotient`, `Sigma.desc`, `Sigma.ι`,
  `imageSubobject`, `HomologicalComplex.mapBifunctorMap`,
  `CochainComplex.mapBifunctor`, and `Localization.Construction.lift`.

The main module additionally imports the available proof interfaces for flat
covers, bounded-above flat K-flatness, tensor closedness, dense-subcategory
localization, and the cone criterion. Unstated proof prerequisites remain in
the unchanged DAG proof; this delivery supplies their full natural-language use,
not new unrelated theorem nodes.

Sources opened: the local Varshavsky PDF at §5.2.1(b), which asserts filtered
lifts and points to Illusie V §2 (not the present resolution lemma verbatim);
Stacks sites-cohomology.tex `definition-K-flat`,
`lemma-bounded-flat-K-flat` (06YQ),
`lemma-resolution-by-direct-sums-extensions-by-zero` (077J); and the current
main-20261015 trace-triangle-compatibility Additivity proof and sk-i-additivity
unit. The node correctly identifies its finite-flag resolution as agent-formulated;
no claim is made to have obtained the wanted Illusie reference.

Edge cases read against the types: the zero ring and zero complex are allowed;
`Fin 0` allows an empty splitting of a zero term; `a=b` is a one-grade
filtration; a nonzero grade or term outside the interval is excluded by the
actual endpoint subobjects, not by an extra vanishing hypothesis; P may be
unbounded below and W unbounded in both directions; W may have a distinct
finite interval. Sites need not have points and no surjectivity on sections
is assumed. Tensor factors occur in both orders. No noetherian, projective,
finite-rank or flat-target assumptions occur. No statement dispute or item
statement correction was needed.

Searches (full outputs are retained in the new definition node):

- `msearch.py ... leansearch "finite filtered complex of sheaves of modules split flat bounded above resolution"`:
  eight generic hits (filtered colimits of complexes, tensor exactness, module
  projective resolutions and short-complex splittings), no filtered sheaf result.
- `msearch.py ... leanfinder "bounded above finite filtered complexes of sheaves have split flat resolutions and localization equivalence"`:
  eight generic sheaf Grothendieck/derived-category hits, no exact match.
- `msearch.py ... leanfinder "convolution filtration on tensor complexes of sheaves of modules"`:
  eight ordinary monoidal/total-tensor hits, no filtered sheaf model interface.
- `msearch.py ... loogle "CochainComplex.minus, FilteredObject, SheafOfModules.IsFlatOnSite"`:
  zero hits, unknown `CochainComplex.minus` in the search service; its declaration
  was instead read in the pinned source.
- `msearch.py ... grep "filtered.*flat|[Cc]onvolution|[Ss]plit[Ff]lat" Algebra/Homology`:
  zero hits. A broader CategoryTheory grep returns Day convolution/flat functors,
  which do not give a complex filtration by subobjects.
- `rg` in `WeilConjectures` for the item id: no hit. Concept search in the
  upstream and `lean/Sheaf` found the ring-module-specific
  `FiniteFilteredKFlatReplacement`, `FiniteFilteredModuleHomotopy` and
  `FilteredTensorGradedComparison`; their full signatures fix `ModuleCat R`
  and cannot express arbitrary ringed-site module sheaves. The existing general
  `UniformFiniteFilteredLocalization` is reused, rather than redefined.
- `tools/blueprint_refs.py search "split flat"`: zero blueprint matches;
  the DAG's trace-formula filtered-definition nodes were read. None supplies
  degreewise split-flat sheaf models and their bounded-above homotopy comparison.

## New nodes

`def-trf-split-flat-filtered-sheaf-models` owns
`Sheaf.Algebra.Homology.SplitFlatFilteredSheafModels`. It defines the missing
split-flat model predicate and its full subcategories, the filtered homotopy
quotient and its graded quasi-isomorphisms, canonical interval inclusions and
their localization lifts, and the concrete tensor-step arrows and convolution
characterization. These are supporting constructions of one model interface;
there is no resolution theorem hidden in the definitions. Module sheaves,
flatness, filtrations, quotient maps, totals and formal localization are existing
declarations. Its single proof obligation `widenProperty` is separately named,
postponed with `sorry`, stated in this definition node's natural statement, and
has the complete antitonicity proof in its docstring. Every other definition has
real data, with no sorry or choice from an undetermined existence theorem.
The source and all three search kinds are recorded. The analogous ring-module
notions and bounded-below filtered injective model do not supply this interface.

## Second reading by Q114

I reopened the unchanged natural statement, the new definition node and both
Lean files, and reread the elaborated clauses in order. The resolution binder
uses the full `Complexes R a b` with no good-model assumption on M; only P is
split-flat. The two maps in strictness and quasi-isomorphism are the recorded
restriction and quotient maps. The second conjunct covers all split-flat P.
The homotopy localization is genuinely on filtered homotopy classes; replacing
it with chain-map localization in the source would have missed this clause,
so the explicit quotient and normalization are retained. Interval comparisons
are concrete inclusion lifts on both sides. Both tensor-order conclusions
assert existence of the convolution filtration and acyclicity of every grade,
with no bound on W. The finite splitting is in each term and has no differential
compatibility condition. The finite-label presentation is equivalent to one
summand per permitted grade, including single-grade and zero cases.

The implementation reread found and repaired: (1) an unnecessary use of arbitrary
subobject suprema, replaced by finite `Finset.sup` for splittings and the image
of the actual coproduct arrow for convolution; (2) implicit universe inference
for flatness, replaced by explicit independent universes and `J`, `R`; (3) the
wrong namespace on `mapBifunctorMap`, changed to `HomologicalComplex`; (4) an
arrow/equivalence precedence ambiguity in the family E, replaced by an explicit
inequality binder. These changes repair expression of the same mathematics.
No item statement/proof fields and no dependent citer were edited. I did not
start another agent, as the dispatcher brief explicitly prohibits it; the
maintainer's independent reading is still required for this returned packet.

Return checklist: H1 now has two Lean files, a verbatim item lean record and both
required report sections; H2/H7 are addressed by delivering no stage-1 proof
changes or statement changes; H12 now adds only one actual definition node;
H8 has source/blueprint docstrings on every declaration and a complete proof
on each postponed theorem; H9/H10 are checked by the prescribed per-file
compiler; H11 is addressed by the explicit clause-by-clause rereading above.

Validation: scompile.py compiled both delivered modules separately with the supplied
sibling overlay, and the dry-run compilation passed after the private proof
imports were added. The first dry run found only a truncated lean.statement
record: the initial text extractor stopped at a named argument `(R := R)`.
The record now contains the full verbatim signature through the final proof
delimiter; the Lean source was already clean.
