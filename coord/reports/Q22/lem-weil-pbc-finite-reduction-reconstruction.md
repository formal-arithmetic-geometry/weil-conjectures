## Worker report

The proposed delivery states `finiteReductionReconstructionCompleted` in
`Sheaf.Paper.FiniteReductionReconstructionCompleted`, and supplies the three missing
statement dependencies in separate modules. This report describes the current candidate;
compilation and the dry run are still pending. No second reading has been performed.

The ambient category is modules over the actual completed coefficient sheaf A_T, not
ordinary D(A) and not the derived category over constant A. `adicDatumRing` reuses
`adicLisseCompletedRing T d.ideal`, the limit of the finite constant quotient sheaves.
The normalized `adicDatumFiniteCoefficientIso` and its naturality theorem explicitly
identify these finite sheaves with the recorded sheafifications of continuous functions
on connected components. Specialize the finite ring to each quotient, using its discrete
topology and `d.quotientFinite`. Naturality identifies the quotient transitions, so the
limit identification also identifies the completion projections and scalar actions.
There is no identification of the original constant A sheaf with its completion.

Hypothesis and clause correspondence for the item:

- A scheme T is the explicit section variable `(T : Scheme.{t})`.
- A commutative Noetherian coefficient ring A is `{A : Type (t+1)} [CommRing A]`
  and `(d : ProEtaleAdicCoefficientDatum A)`. The latter extends the recorded
  `CompleteCoefficientDatum`: its `ideal`, `noetherian`, `finitelyGenerated`,
  `quotientTorsion`, `quotientPerfect` are precisely those hypotheses; `quotientFinite`
  adds finiteness of every positive quotient, without adding I-adic completeness or
  flatness of a quotient. Positive level a is represented by `n : ℕ`, meaning a=n+1.
- The completed coefficient sheaf and its positive quotients are `adicDatumRing`,
  `adicLisseRingSystem`, and `adicDatumProjection`. Their construction uses the existing
  genuine sheaf limit, whose operations and restrictions are sectionwise.
- The object K is `{K : adicDatumDerived T d}`. This is the standard localization of
  `completedConstantModules T (adicDatumRing T d)`, i.e. actual A_T-module sheaves.
- `M : AdicDatumModel T d K` is a K-flat representative with realization isomorphism.
  It is a computational presentation of arbitrary K, not an added restriction:
  `adicDatumModel_exists` states existence for every unbounded K. No strict functor
  choosing K-flat complex representatives is assumed.
- The ideal generators are `r`, `f : Fin r → A`, and
  `hf : Ideal.span (Set.range f) = d.ideal`. The completeness hypothesis is
  `IsCompletedIntrinsicallyDerivedComplete ... M.complex M.realization`, exactly
  invertibility of the explicit intrinsic Koszul completion map.
- `adicDatumTowerFunctor` applies ordinary quotient extension and restriction termwise
  to form a complex in the strict tower category. Its transition maps are fixed by
  `s tensor x` mapping to `q(s) tensor x`. The universal derived pair
  `adicDatumTowerDerived_exists` records derived functoriality and its K-flat computations.
  `adicDatumModelTower` is the actual evaluated strict tower on M, with all transitions.
- `L : CompletedSequentialDerivedLimit ... (adicDatumModelTower ... M)` is precisely a
  vertex, a product arrow p and a boundary forming a distinguished Roos triangle.
  It is not a choice of a derived-limit functor and does not impose a special cone model.
- `adicDatumModelRestriction` is the exact scalar-restriction comparison, including the
  degreewise identity comparison between the two presentations of the evaluated complex.
  `adicDatumModelReductionIso` is the universal derived K-flat comparison, including M's
  realization. These specify the actual quotient-coefficient target K_a.
- `completedReconstructionEvaluation` is L.p followed by its a-th product projection,
  the exact-restriction comparison, and the inverse of the K-flat comparison. Thus it
  is exactly evaluation in the required quotient coefficients.
- `completedReconstructionCounit` is the inverse hom equivalence of the normalized
  derived extension/restriction adjunction applied to that evaluation. Its target is
  `(adicDatumReduction T d n).obj K`, with its quotient action. The first conclusion is
  `IsIso` of this specified map, not an existential isomorphism.
- Functoriality is the final universally quantified square: for a derived map v and a
  map w of chosen limit vertices compatible with every evaluation, with K' likewise
  intrinsically complete, the counits commute
  with v and w after reduction. This is the naturality interpretation appropriate to a
  derived limit defined as a Roos triple, without choosing functorial vertices.
- `completedReconstructionProductComparison` is the canonical map formed from tensors
  of the product projections. Its tensor functor is extension followed by exact scalar
  restriction, so both sides lie in D(Mod(A_T)). The second conclusion says this map is
  invertible. Both product vertices in the Roos triangle are the same chosen product
  of the same family and hence use this same map; duplicating the identical IsIso
  conjunct would add no clause. No general preservation of all products is assumed.

The adjunction is not chosen from bare Nonempty data. Its ordinary unit is uniquely
specified sectionwise by `m` mapping to the sheafified `1 tensor m`, and
`adicDatumAdjunction_exists` specifies its hom-equivalence compatibility with that
ordinary adjunction, the universal derived counit and the exact restriction comparison.
The model comparison uses that same counit, transported by the homotopy/complex
localization isomorphisms. Definitions taking data from existence theorems use either
a unique section formula or a universal property fixing the canonical comparison.

Dependency declarations reused:

- `Sheaf.Paper.AdicLisseModule`: `adicLisseConstantRing`, `adicLisseRing`,
  `adicLisseConstantUnit`, `adicLisseConstantModules`, `adicLisseRingSystem`,
  `adicLisseCompletedRing`, `adicLisseForget`.
- `Sheaf.Paper.CompletedConstantFiniteComplexRealization`: `completedConstantModules`,
  `completedConstantDerived`, `completedConstantQ`, `completedConstantExtension`,
  `completedConstantTensor`, `CompletedConstantQuotientTower`, `completedConstantGenerator`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `finiteCoefficientScalarMap`, `finiteCoefficientScalarMap_locallyBijective` and the
  continuous-functions presheaf. The comparison above preserves the recorded notion.
- `Sheaf.Paper.CompleteCoefficientDatum`: `CompleteCoefficientDatum` and
  `adicQuotientPerfect`, using `DerivedCategory.IsPerfectRingComplex` from
  `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, including its specified
  additive ordinary witness, universal derived pair and K-flat counit comparisons.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlat`; `KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.KoszulComplex`: `ExteriorAlgebra.koszulComplex`; Mathlib's
  `exteriorPower.map`, `ComplexShape.embeddingDownNat`, total tensor, termwise products,
  and `CochainComplex.mappingCocone`, `mappingCocone.lift` give the intrinsic model.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle`; `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`:
  `Scheme.ProEt.countableProducts_exact`; `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`:
  `derivedCategory_countableProducts_core`; Mathlib's `Localization.lift`,
  `HomologicalComplex.complexOfFunctorsToFunctorToComplex` and exact functor localization.

Proof-only DAG dependencies without Lean records in the shared snapshot:
`lem-weil-pbc-completed-constant-sheaf-reduction`,
`lem-weil-pbc-finite-projective-tensor-products`,
`prop-weil-pbc-koszul-reconstruction`, `prop-weil-pbc-roos-triangle`.
They do not provide imports yet. The item's full four-step proof is in its docstring.

Edge cases checked before the statements were written: the empty scheme and zero modules;
the zero ring; the first positive level n=0 (a=1); the zero ideal and an empty generator
tuple r=0; the unit ideal, where a complete K is zero; nilpotent ideals; unbounded K;
nonflat finite quotients. No connectedness, boundedness, regular sequence, complete ring,
nonempty generator tuple or arbitrary chosen scalar map has been added. Site objects
remain in t+1 and morphisms in t, with coefficients/modules in t+1.

Searches for an existing exact statement or usable notions:

- msearch.py leanfinder, "Derived complete sheaves over the completed coefficient ring
  reduce modulo finite quotients and tensor commutes with products": eight ordinary
  AdicCompletion tensor hits, including `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`;
  none states the completed-sheaf derived theorem.
- msearch.py loogle, `CategoryTheory.IsDerivedLimit`: zero hits/unknown identifier in
  the remote index. The actual project source of IsDerivedLimit was read via --source.
- msearch.py grep, `Roos|derived.*completion`, CategoryTheory: zero hits.
- The earlier attempt's additional LeanFinder, Loogle, and Mathlib grep searches are
  preserved in searches.jsonl; these also found no exact completed-sheaf statement.
- rg in upstream WeilConjectures and side lean/Sheaf for the item id and the proposed
  declaration prefixes found no existing declaration. Broader searches found the
  canonical completed-coefficient APIs listed above, whose signatures/docstrings were read.
- scompile.py --source confirmed that the guessed missing AdicCoefficientDatum,
  AdicCoefficientDatumCompleted, IntrinsicCompletion, DerivedInverseLimit and
  PbcDerivedInverseLimit modules were not available on the server when checked.
- The three item's stmt_deps and their own statement dependencies were read. The
  recorded generic derived limit, tensor, K-flat, perfectness and evaluation interfaces
  are reused; no Mathlib leaf is discarded for lacking a lean record.

Sources checked: the DAG statements and proofs and Stacks 099M, 091Z, 07KC. Stacks 099M
concerns constant coefficients and supplies context, not an identification with completed
coefficients. The normalized finite coefficient comparison above supplies the representation
change actually used here. No mathematical statement correction has been made.

## Dependency modules

`def-weil-pbc-adic-coefficient-datum`: no recorded declaration existed for the node's
completed-coefficient notion. `AdicCoefficientDatumCompleted` supplies the coefficient
hypotheses, the actual completed ring and normalized finite-sheaf comparison, its scalar
map and projections, module/tower/derived categories, ordinary and derived normalized
scalar adjunctions, universal K-flat comparisons, strict derived quotient construction,
and ordinary balancing normalization with its sectionwise formula and triple-change cocycle,
and the corresponding normalization in the actual derived quotient categories. The former
constant-coefficient complete datum is reused only for the ring-theoretic hypotheses.

`def-weil-pbc-intrinsic-completion`: the available IntrinsicKoszulCompletion is over the
original constant ring and therefore unusable as this node's declaration.
`IntrinsicCompletionCompleted` extends actual Koszul complexes to A_T, with transitions
multiplying degree -1 generators by f_j and fixing degree zero. It forms tensor products,
products and the explicit mapping fiber, with its specified zero-homotopy unit.
The mapping cocone of minus (1-shift), after listing its terms as (x,y), has differential
(dx,(1-shift)x-dy), matching the node's sign. Completeness is precisely invertibility of
that unit. The descent theorem records localization through quasi-isomorphisms.

`def-weil-pbc-derived-inverse-limit`: no completed-coefficient specialized record existed.
`SequentialDerivedInverseLimitCompleted` supplies the canonical localization lift of
exact strict-tower evaluation, exact countable products and their derived products, and
the Roos-triple structure. The latter is the existing IsDerivedLimitTriangle applied to
the evaluated diagram; it selects neither an object nor a derived-limit functor.

## Validation history

Compiler infrastructure intermittently failed in the server fallback of scompile.py:
nt_compile.py -> own_directory -> symlink_to raised OSError [Errno 28], No space left
on device, while creating its artifact overlay. Both the original import-only probe
and the expanded import-only probe now pass locally. The coefficient interface subsequently
compiled on the server in 18.3 and 18.6 seconds, after narrowing inferred signatures.
A 60-second timeout was treated as an implementation fault and repaired, not as a blocker.
The finite coefficient naturality formula initially triggered an opaque-presheaf
coercion error; it was repaired by explicit ContinuousMap.toFun evaluation. The coefficient
module then passed all three local invocations (37.8, 53.0 and 46.7 seconds), and server
confirmation passed in 23.5 seconds. The next module exposed an unassigned universe in
an unused index-universe parameter of derivedCategory_countableProducts_core; that
parameter is now explicitly 0, without changing the site universes.

The subsequent wrapper attempt itself failed locally with FileNotFoundError for its
private /tmp/nt-local-compile-.../.lbuild/Sheaf directory, then server confirmation again
crashed with OSError [Errno 28] during overlay symlink creation. The first required
--no-push dry run likewise failed in that server overlay creation. No code or files in
the shared repository, live artifacts, or launcher tools were edited. Diagnostic helper
scripts in scratchpad retain the local diagnostic that scompile.py normally discards
before server confirmation; they still execute the prescribed wrappers unchanged.

The latest packet and repeated required --no-push dry run remain to be recorded below.

## Second reading by Q22

I read the node statement, its corrected source note, all three dependency node records, and the four delivered Lean files. The item introduces a scheme `T`; a commutative ring `A` with the completed Noetherian adic datum `d`; a derived object `K`; derived I-completeness via the intrinsic completion map; its strict quotient tower; a derived inverse-limit vertex `L`; and each positive quotient level. In Lean these are rendered by `(T : Scheme.{t})`, `[CommRing A]`, `d : ProEtaleAdicCoefficientDatum A`, `K : adicDatumDerived T d`, `M : AdicDatumModel T d K`, `hf`, `hcomplete`, `adicDatumModelTower T d M`, and `L : CompletedSequentialDerivedLimit T d (adicDatumModelTower T d M)`. The model is the recorded K-flat presentation of arbitrary `K`, and the tower retains all quotient transitions.

The first conclusion, evaluation followed by the derived counit, is rendered by `completedReconstructionEvaluation` and `completedReconstructionCounit`; `IsIso (completedReconstructionCounit T d M L n)` is the required finite-level isomorphism. The index `n : ℕ` denotes the positive quotient `P_(n+1)`, so it covers the node's `a ≥ 1`, including `a = 1`. The naturality clause quantifies a second complete model, a second Roos vertex, a derived map `v`, a vertex map `w`, and compatibility with every evaluation, then states the required counit square. The product clause is rendered by `completedReconstructionProductComparison`; its source and target are the two countable products in the common Roos family, and the second conjunct asserts that this canonical projection-induced comparison is an isomorphism. The same family and comparison occur at both Roos product vertices, so this is exactly the node's two-product clause rather than an added preservation assertion.

The ambient category is consistently `adicDatumDerived T d`, i.e. `D(Mod(A_T))`; quotient objects are transported back by `adicDatumReductionUnderlying`, and the counit target is the quotient-coefficient category `adicDatumReduction T d n`. No ordinary `D(A)` identification is introduced. Universes keep site objects at `t+1` and morphisms at `t`; no extra finiteness, flatness, connectedness, boundedness, regular-sequence, or nonempty-generator assumptions occur. The hypotheses `r`, `f`, and `hf` permit `r = 0`; `n = 0` is the first positive quotient; zero schemes, zero objects, zero rings, zero ideals, unit ideals, nilpotent ideals, and nonflat finite quotients are admitted by the declarations.

I searched the project and source namespaces with `rg` for the item and for `Roos`, `derived.*completion`, and reconstruction names, and checked the recorded dependency declarations. No exact existing statement or completed-coefficient reconstruction declaration was found; the three dependency modules are therefore required repairs for unusable constant-coefficient records. `msearch.py` searches recorded in the worker packet found no exact Mathlib or upstream theorem. The existing constant-coefficient completion notions are distinct and are not duplicated.

No mismatch was found in the candidate Lean statement. The only apparent differences are intentional representations mandated by the corrected node: `M` makes the K-flat representative explicit, `n : ℕ` encodes positive level `n+1`, and the single canonical product comparison represents both identical Roos product occurrences. The supplied dependency modules were read against their node statements and retain real constructions, with postponed properties as named `sorry` theorems; no hollow definition or private replacement was introduced. The item and dependency files compile under the prescribed wrapper when compiled in dependency order.

Final source/search and validation record: I independently reran LeanFinder with
“counit of derived scalar extension of a homotopy limit of reductions is invertible
for derived complete sheaves”; its eight hits concern condensed counits and generic
derived adjunctions, not this theorem. Loogle with `"PreservesLimitsOfShape", "tensor"`
returned the flat commutative-ring tensor equalizer instance, not a derived module-sheaf
product comparison. Direct searches of both upstream and side modules located ordinary
adic completion, integral-coefficient completeness, and generic Roos constructions; none
has this completed-sheaf counit statement. These calls are in `searches.jsonl`.

The shared clone omits the literature checkout, so I obtained upstream Stacks
`proetale.tex` and `more-algebra.tex` into scratchpad. I read
`section-derived-completion-noetherian` and `lemma-naive-completion` (099M), including
the preceding completed-ring comparison, and `situation-koszul` and the Koszul completion
lemmas (091Z context). The source has a general site, a Noetherian ring and an ideal;
it does not supply an identification of all constant and completed coefficient objects.
The present module correctly keeps its own completed-sheaf category. I also checked
Tag 07KC against the countable-product dependency. No stage-2 statement correction
was introduced: the earlier completeness correction belongs to the already accepted
stage-1 node, and its `split_report.source_correction` is unchanged.

The required `deliver2.py ... --no-push` completed with exit code 0 and
`OK (dry run): commit fe76b0569c passes the preflight and compiles; nothing pushed`.
It compiled the four sibling modules in the delivery, resolving the earlier individual
wrapper attempts' missing sibling object files. No Lean signature or node statement
was changed during this second reading; only this independent report and validation
record were added.
