## What changed

Proved `AlgebraicGeometry.Proj.sheafify_graded_chain` with its statement unchanged. The
proof chooses associated sheaves and chart data separately for the three graded modules,
obtains an exact chain on these fixed sheaves, and maps it through the inverse-scheme
pullback equivalence. The equivalence is constructed explicitly using Mathlib's
`pullbackComp`, `pullbackCongr`, and `pullbackId`. Monomorphisms and epimorphisms are
preserved by the equivalence. The two adjacent short complexes are mapped with
`ShortComplex.Exact.map` and recombined with `ComposableArrows.exact_of_δ₀`.

Added two smaller interfaces, one statement per module: `GradedModuleChartData` supplies
only associated sheaves and their chart data, with no chain hypotheses or exactness;
`GradedChainMapsExact` constructs exact maps on already fixed associated sheaves, with
no projective-line isomorphism, transported arrows, or existential sheaf construction.
The combination and all transport are proved in the item's module. Updated its DAG
proof to reflect this reduction. The blueprint unit route is unchanged.

All three sandbox modules compile together through lcompile.py, with no errors or
warnings. No statement, definition, target signature, universe, or public import of the
item was changed. Only the two new named theorems retain sorry.

## Proved and sorry left

Proved: `AlgebraicGeometry.Proj.sheafify_graded_chain`
(node `lem-sc-p1-sheafify-graded-chain`). Its proof contains no sorry.

Remaining sorry declarations added by this delivery:

- `AlgebraicGeometry.Proj.graded_module_chart_data_exists`, node
  `lem-sc-p1-graded-module-chart-data`, in
  `lean/Sheaf/AlgebraicGeometry/ProjectiveSpace/GradedModuleChartData.lean`.
- `AlgebraicGeometry.Proj.graded_chain_maps_exact`, node
  `lem-sc-p1-graded-chain-maps-exact`, in
  `lean/Sheaf/AlgebraicGeometry/ProjectiveSpace/GradedChainMapsExact.lean`.

Both have exactly `:= by sorry`, a source, a complete argument in words, and matching
new nodes. Edge cases checked: zero modules and the zero chain satisfy both statements;
non-finitely-generated modules require no extra hypothesis; negative module degrees are
allowed, while positive homogeneous denominators identify degree-zero fractions after
localization. The fixed sheaves need only the supplied three chart properties, since
basis uniqueness identifies them with the canonical associated sheaves.

## No longer needed

Removed the item's proof imports:

- `Sheaf.AlgebraicGeometry.TensorPullback` (node `def-pc-module-pullback`): the
  transport uses Mathlib's `Scheme.Modules.pullback` and its composition/identity
  isomorphisms, not the tensor-formula pullback or its bridge.
- `Sheaf.AlgebraicGeometry.ProjSheafificationExact` (node
  `lem-sc-p1-proj-sheafification-exact`): retained as a dependency of the new fixed-sheaf
  exact-map construction, not pruned from the overall argument.
- `Sheaf.AlgebraicGeometry.ProjTildeFunctorial` (node
  `lem-sc-p1-proj-tilde-functorial`): likewise retained under `GradedChainMapsExact`.

The graded-module sheaf existence node remains needed below both new interfaces. No
unit statement or unit step is bypassed. No other node or module is claimed globally
unreachable by this delivery.

## Where the brief, the DAG or earlier work was wrong

The existing `gradedModuleSheaf_exists` statement uses `ℕ → AddSubgroup S`, whereas
this item and `proj_sheafification_shortExact` use homogeneous `Submodule k S` grading.
Changing to underlying additive subgroups produces a different Lean Proj scheme type;
it cannot simply be passed to the target. The chart-data interface isolates the
necessary grading/Proj identification and extraction of additive chart maps, without
altering the existing declaration or its users.

`tilde_functorial` also requires injective stalk charts and a germ formula in addition
to the three chart properties available here. The fixed-sheaf map construction's proof
explicitly supplies those through basis uniqueness and canonical associated sheaves;
this is why merely applying the existing theorem does not immediately close the step.

The Stacks sources read were [01M6](https://stacks.math.columbia.edu/tag/01M6) and
[01M7](https://stacks.math.columbia.edu/tag/01M7), including clauses (2), (3), (5) and
the final functoriality/exactness paragraph. Searches through Lean Finder and Mathlib,
Sheaf and WeilConjectures source found no matching complete interface. LeanSearch
returned HTTP 500; this is recorded as unavailable, not as an absence result.

## New nodes

`lem-sc-p1-graded-module-chart-data`: existence and chart compatibility for one graded
polynomial module. It isolates the additive-subgroup versus homogeneous-submodule
interface and chart-map extraction from `gradedModuleSheaf_exists`.

`lem-sc-p1-graded-chain-maps-exact`: construction and splicing of the two short exact
sequences on fixed associated sheaves. It records the range grading, basis comparison
needed for stalk data, use of functoriality and short exactness, and categorical splicing.

No change records are needed: all existing statements and definitions are unchanged.

## Second reading by X2

1. **Visible statements unchanged: pass.** Read the complete repository and sandbox
   versions and their diff. The text from `theorem sheafify_graded_chain` through its
   signature is byte-identical, including universes, all gradedness and exactness
   hypotheses, the fixed sheaf F and its chart hypotheses, and every output clause.
   The existing docstring and public imports are unchanged; there are no definitions
   added or altered. The existing public existence-module import provides the
   degreeZeroFractions and module-sheaf vocabulary used by the signature. The only
   existing-node differences are proof, proof_deps and proof_origin. No change record
   is required.

2. **Proof and trust check: pass as a partial delivery.** All three files compiled
   locally in import order without errors or warnings. Read the choice of E, the
   fixed-sheaf chain application, both inverse-functor comparisons, and the two
   ShortComplex exactness arguments. pullbackComp has the contravariant order needed
   here; the inverse identities reduce its composites to identity pullbacks. The
   resulting equivalence supplies mono/epi preservation and the exactness transport.
   A scratch copy with explicit #print axioms for all three declarations compiled:
   each uses only propext, Classical.choice, Quot.sound and sorryAx. The last is
   expected from the two named open interfaces, so this is not an axiom-free target
   closure. The original item has no sorry; the two new theorems each have exactly
   one final `by sorry`. There are no hollow definitions or forbidden declarations.
   Removed the scratch copy before delivery.

3. **Split statements and shorter-route search: pass.** Read Stacks Definition 27.8.3
   (01M6) and Lemma 27.8.4 (01M7), clauses (2),(3),(5) and its exact-functor paragraph,
   against both new signatures and their docstrings. The single-module chart theorem
   needs no exact chain or projective-line comparison. The other theorem assumes
   fixed sheaves with chart data and concludes only a chain on Proj: it supplies
   neither their existence nor transport to the projective line. Neither restates
   the item's complete hypotheses and conclusion. Check the zero module, zero chain,
   shifted polynomial modules (including negative degrees), and the empty D_+(0)
   chart: localization at zero and sections on the empty open are both zero. Positive
   denominator powers let negative grading components contribute after multiplication;
   no finite-generation assumption is needed. For arbitrary fixed sheaves, injection
   onto the fraction subset gives chart bijections; hscalar gives linearity, and hres
   together with standardOpenProperties gives restriction compatibility. Thus basis
   uniqueness really supplies the needed canonical comparison and stalk data.
   The graded image K has an internal grading by homogeneous decomposition, and the
   two short sequences splice because the middle inclusion is mono and quotient epi.
   Read gradedModuleSheaf_exists, tilde_functorial, proj_sheafification_shortExact and
   standardOpenProperties: the grading-type and stalk-data mismatches prevent direct
   application to close either new theorem in a few minutes. Independently searched
   LeanFinder for associated Proj sheaves and exact sequences, Loogle for Proj
   isomorphisms, and Mathlib via msearch grep for graded sheaves and exact pullback;
   also searched the repository and upstream ProjectiveSpectrum sources using
   grading conversions, chart data and associated-sheaf wording. No existing complete
   interface was found. Loogle reported overload, not a mathematical absence result.
   Search calls are recorded in searches.jsonl.

4. **Top-down reduction, imports and pruning: pass after repair.** The item now proves
   choice and all pullback transport, leaving chart construction and exact maps on
   fixed sheaves below it. Existing functoriality, existence and short-exactness nodes
   remain in the new nodes' proof plans. The old proof_deps were exactly module
   pullback, short-exact sheafification, tilde functoriality and graded sheaf existence:
   the report accounts for all four. Only def-pc-module-pullback is bypassed by the
   overall argument; the other three remain needed below the interfaces. Proof-only
   imports are plain imports. Added the missing plain ProjStandardOpenProperties
   import to GradedModuleChartData to match its stated proof dependency. Read the
   sk-thm-picard-duality unit: its realized statement and step lists are empty in the
   repository and are unchanged by this delivery; no populated unit realization or
   prescribed graded-resolution step is bypassed.

5. **DAG/Lean agreement: pass after clarification.** Read all three delivered nodes.
   Their declarations and signature records agree with the Lean modules (new records
   verbatim; the unchanged item record modulo whitespace). Source, chapter, unit,
   creation records and blueprint ancestry also agree. In each node the union
   of proof-step uses equals proof_deps. The item's DAG follows the actual chart
   choice, fixed-sheaf map construction and categorical transport. The two new nodes
   carry the full natural-language arguments and recorded three-kind searches.
   Clarified the fixed-sheaf node's second proof step, and its new theorem docstring,
   to say explicitly that gradedModuleSheaf_exists and tilde_functorial use the
   additive-subgroup grading and that chart identifications transport across the
   canonical scheme comparison. This closes a gap in the written route, without
   claiming the conversion has already been formalized.

Changes by the second reader: one missing proof-dependency import; clarification of
one new theorem's proof docstring and matching DAG step; this review and independent
search/axiom checks. The original Lean proof and every theorem signature are unchanged.
