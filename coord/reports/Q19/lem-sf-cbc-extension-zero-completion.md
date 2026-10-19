## Worker report

The delivery states `lem-sf-cbc-extension-zero-completion` in
`Sheaf.Paper.SfCbcExtensionZeroCompletion`. Its principal declaration is
`AlgebraicGeometry.Scheme.sfCbcExtensionZeroCompletion`; `lean.declarations`
records all supporting definitions and statements in the same module. This is
stage 2: mathematical theorem proofs are `sorry`, with sources and complete
proof descriptions. Definitions contain actual constructions or selection from
uniquely normalized comparisons. There is no change to the node's statement.

The earlier worker's “stale assignment” diagnosis referred to stage-1 splitting:
the shared node is split and independently reviewed, but has no Lean record.
This delivery performs its still-missing stage-2 statement work.

### Hypotheses and underlying objects

* Schemes are `{U X : Scheme.{t}}`; `j : U ⟶ X` and
  `[IsOpenImmersion j]` are the given open immersion. Neither quasi-compactness
  nor any additional separation condition is assumed.
* `{A : Type t} [CommRing A]` and `d : CompleteCoefficientDatum A` give exactly
  the ring, ideal, Noetherian, finitely generated ideal, additive-torsion quotient,
  and perfect positive quotient hypotheses. The datum's fields are
  `ideal`, `noetherian`, `finitelyGenerated`, `quotientTorsion`, and
  `quotientPerfect`. `[∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1))]` supplies the
  additional finiteness **as a set** required by the node and by its witness
  comparison. The datum alone would not supply that finiteness.
* `adicModuleRing T A` and `proEtaleDerivedCategory T A` are the recorded
  constant coefficient module sheaves and ordinary unbounded derived categories,
  using `ULift.{t+1,t} A` for coefficient size. All universes and variables are
  explicit, and `autoImplicit` is false.
* The site is the recorded `T.ProEt`, with object universe `t+1` and morphism
  universe `t`. `sfCbcModelModules`, `sfCbcModelDerived` use the existing
  `proEtaleModelTopology T` on `AsSmall.{t+1} T.ProEt`. This enlarges only the
  morphism presentation and canonically transports the same site, not the class
  of schemes or coefficients. Its coefficient map is uniquely fixed by constant
  sheafification units. This permits the published small-site completion API
  without imposing an equality between the original site universes.
* `sfCbcConstantSliceMap` is fixed by its constant-section formula;
  `sfCbcConstantModuleToSlice` is actual module pushforward along
  `cbcSliceFunctor`. `sfCbcOpenExtension` composes this with
  `SheafOfModules.localizedModuleExtension`, the actual direct-sum presheaf
  followed by module sheafification. `sfCbcDerivedExtension` is its exact
  termwise derived functor. `sfCbcTowerExtension` is actual whiskering of strict
  inverse sequences and `sfCbcDerivedTowerExtension` derives this exact functor.
* Strict towers have category `ConstantCompletion.TD (sfCbcModelRing T A)`:
  the derived category of `ℕᵒᵖ ⥤ Mod`, not the category of diagrams in a derived
  category. The index `n : ℕ` means the positive exponent `n+1`; the recorded
  coefficient objects are indexed by `⟨n+1, Nat.succ_pos n⟩`.
* `sfCbcReduction T d` is the published universal quotient presentation's tower,
  transported by `sfCbcModelDerived`. Its comparison computes the whole strict
  diagram on one flat-term K-flat representative. `sfCbcCompletion` is exactly
  that tower followed by the published total right derived strict limit and
  inverse site transport. `sfCbcCompletionUnit` transports its **specified**
  quotient-unit completion map. `sfCbcIsComplete` is the recorded local derived
  completeness predicate, rather than an image predicate or a new completion.

### Each conclusion and its Lean rendering

1. `sfCbcExtensionModel_existsUnique` states preservation of a flat-term K-flat
   representative, with the complex equal to the actual termwise extension and
   its realization equal to the exact-derived factorization followed by the
   original realization. `sfCbcExtensionModel` selects precisely that model.
   An arbitrary flat-term K-flat complex is included by taking its localization
   as `K` and the identity realization; no restriction on derived inputs is
   introduced. `sfCbcModelComplex_kflat` gives the same fact for site transport.
2. `sfCbcOrdinaryTensorComparison` is a natural isomorphism of **strict ordinary
   quotient diagrams**, fixed by every quotient-unit component.
   `sfCbcTensorComparisonNormalized` gives its exact localization formula on
   every flat-term K-flat complex, using the universal quotient counits.
   `sfCbcTensorComparison_existsUnique` and `sfCbcTensorComparison` supply the
   resulting natural isomorphism of actual **derived strict towers**
   `J ⋙ R_X ≅ R_U ⋙ J_tower`. The normalization prevents choosing an arbitrary
   natural isomorphism with those endpoints.
3. `sfCbcReducedCompletionUnit` is literally the natural transformation obtained
   by applying `R_X` to `η` on `J K`. `sfCbcReducedCompletionUnit_isIso` asserts
   invertibility, without assuming `J K` complete. `sfCbcCompletedExtension` is
   `J ⋙ C_X`. `sfCbcCompletedReductionIso` is by definition the inverse reduced
   unit followed by the tensor comparison. The principal theorem explicitly
   states `R_X(η_(J K)) ≫ q.hom = q_tens.hom` for every `K` (Lean writes
   composition in the opposite textual order from the displayed TeX formula).
4. `sfCbcFiniteTensorHom` is defined by the actual derived scalar adjunction
   from the extended quotient-unit map. `sfCbcCompletionModelIso` identifies
   the completion with the recorded Roos completion **by its unit equation**.
   `sfCbcFiniteCompletedHom` is the adjoint of the actual recorded n-th limit
   projection, followed by that tensor comparison. Its domain and target lie
   in `proEtaleDerivedCategory X (A ⧸ d.ideal ^ (n+1))`, retaining the quotient
   coefficient action. `sfCbcFiniteCompletedHom_inverse` asserts invertibility
   and explicitly identifies the inverse as the inverse tensor comparison
   followed by the reduction of the completion unit. Thus “inverse is the
   reduced unit” is read with exactly the tensor endpoint identification from
   the node; no incorrectly oriented arrow is asserted.
5. `sfCbcFiniteCompletedHom_naturality` quantifies over arbitrary derived input
   maps and arbitrary choices of the stipulated models. Scalar restriction
   commutes with extension via `sfCbcRestrictExtensionIso`, uniquely normalized
   on `sfCbcExtensionSection`, and its exact-derived version.
   `sfCbcFiniteUnderlyingHom` is the same finite comparison restricted to A.
   `sfCbcFiniteUnderlyingHom_transition` states the square for **every**
   `n ≤ m`, not only successive transitions. These are equations before
   taking any derived limit.
6. `sfCbcFiniteModelIso_existsUnique` fixes the ordinary finite evaluation
   comparison by the quotient augmentation in each degree.
   `sfCbcFiniteEvaluationIso` is its explicit localization composite using one
   model and the universal quotient counit. `sfCbcEvaluateExtensionIso` derives
   the identity between evaluation and termwise extension.
   `sfCbcCompletedReductionIso_evaluation` states that evaluation of the actual
   strict `q` is **exactly** `sfCbcFiniteUnderlyingHom`, under those prescribed
   comparisons. The finite P_n-linear morphism is therefore connected to the
   strict tower assertion, rather than merely having isomorphic endpoints.
7. The principal theorem states completeness of every `Jc K` using
   `sfCbcIsComplete`. `sfCbcCompletedExtensionPresentation` is the specified
   natural isomorphism `Jc ≅ R_U ⋙ J_tower ⋙ Rlim_X`, constructed by applying
   `Rlim` to `sfCbcTensorComparison`. It is not an assertion that ordinary `J`
   commutes with `Rlim`.
8. The witness's two components are supplied explicitly: an arbitrary
   `L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat (ULift P_n)))`
   and its specified isomorphism `α : ν_U^* L.obj ≅ adicReduction U d M n`.
   This avoids another definition of the notion of etale origin.
   `sfCbcRealizationExtensionIso` identifies fixed-coefficient and constant-module
   extension, uniquely on extension generators (its `HEq` only accounts for
   the identical underlying scheme with two equal structure maps).
   `sfCbcEtaleExtensionComparison` is the published nu/j! comparison followed
   by that normalized realization comparison, derived by exact functors.
   `sfCbcEtaleExtension_boundedBelow` supplies the bound and
   `sfCbcEtaleExtensionPlus` is the actual `j! L` as a Plus object.
   `sfCbcTransportEtaleWitnessIso` retains exactly this antecedent and forms
   `comparison ≪≫ J.mapIso α ≪≫ finiteCompletedIso.symm`. The principal theorem
   includes existence of this isomorphism for every supplied pair and every n.
   No transition maps between etale antecedents are asserted.

### Dependency declarations used

* `Sheaf.Paper.CompleteCoefficientDatum`: `CompleteCoefficientDatum`,
  `adicConstantRing`, `adicModuleRing`, `proEtaleDerivedCategory`, `AdicKFlatModel`,
  `adicLocalization`, `adicChange`, `adicRestrict`, `adicReduction`,
  `adicReductionUnderlying`, `adicTransition`, `adicTensorSection`.
* Mathlib: `Scheme.ProEt`, `ProEt.topology`, `IsOpenImmersion`, `constantSheaf`,
  `DerivedCategory`, `DerivedCategory.Plus`, `Functor.mapDerivedCategory`, its
  factorization, composition and natural-isomorphism APIs; actual strict functor
  categories and exact evaluation. The inverse sequences use the same category
  as `Functor.ofOpSequence` and the recorded diagram-site realization.
* `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`:
  `SheafOfModules.localizedModuleExtension` and its actual direct-sum/sheafification
  construction. The small pro-etale localization is the recorded
  `ProEt.weaklyEtale_localization` (imported by the owning slice module).
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleModelTopology`,
  `proEtaleModuleToModel` and its canonical ringed-site equivalence.
* `Sheaf.Paper.CompletedOpenExchangeTransport` publicly retains the owning
  `CompletedExtensionZeroComparison` declarations `cbcSliceFunctor` and
  `cbcOpenObject`. Only their coefficient-independent geometry is reused;
  its completed coefficient ring is not substituted for the constant ring A.
* `Sheaf.Paper.ConstantCompletionEquivalence`:
  `ConstantCompletion.constant`, `res`, `reductionTower`, `reductionUnit`,
  `reductionComplex`, `QuotientPresentation`, `quotientPresentation`, `rlim`,
  `completionUnit`, `IsComplete`, and their universal comparison laws.
  The strict limit is the published right derived strict limit, backed by
  `RingedStrictTowerHomotopyLimitOfUniverses`.
* `Sheaf.Paper.ProEtaleConstantReductionTower` publicly imports the generic
  completion-mate API of `Sheaf.Paper.CompletionMateComparison`; no additional
  site-universe equation is used. `CompletedPullbackAdjunction` supplies the
  completeness/reflector fact referred to in the proof descriptions.
* `Sheaf.Paper.CompletionMap`: `adicReductionComplex`,
  `adicReductionAugmentation`, `adicCompletionObject`, `adicCompletionMap`,
  `adicCompletionEvaluation` (the latter exported by the reduction module).
* `Sheaf.Paper.AdicCompletionReduction`: `adicDerivedRestrict`,
  `adicDerivedRestrictFactors`, `adicReductionDerivedUnit`,
  `adicReductionHomEquiv`, `adicReductionMap`, `adicCompletionReduction_isIso`.
* `Sheaf.Paper.RingedEtaleOriginWitness`: `etaleOriginScalars`,
  `etaleOriginRealization`, `etaleOriginComparison`. Its published fixed-ring
  realization, not an arbitrary equivalence, is used.
* `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `ProEtale.openImmersionLowerShriekComparisonUpperStarIso`, and its public
  fixed-coefficient functors/adjunctions. These are the framework's
  FiniteCoefficient imports; mixing the older non-FiniteCoefficient family
  produced a duplicate declaration, repaired by removing that import and
  using the actual geometric localization formula locally.

The added statement dependencies are all existing recorded nodes:
`def-weil-proetale-inverse-image`,
`lem-weil-pbc-constant-completion-equivalence`,
`lem-sp-completion-mate-comparison`,
`lemma-weil-pbc-adic-completion-reduction`,
`lem-cbc-completed-extension-zero-comparison`, and
`def-weil-pbc-completion-map`. Their combined statement/proof closures were
checked for a path back to this item: none. No dependency node is modified.

### Edge cases and source reading

Read the whole item, every recorded statement dependency and its declaration
signature/docstring, current blueprint `fix-lem-exchanges.proof.md` (integral
open factor), original split source, and Stacks `proetale.tex` Tags 099M/099N.
Read the canonical finite-coefficient nu/j! comparison, the exact localized
module extension, ringed slice tensor formula, and published completion-unit
and scalar-adjunction interfaces.

Checked identity open immersion, empty open immersion, zero complex, zero ring,
unit ideal, zero ideal when allowed by the torsion/perfect/finite hypotheses,
positive first quotient n=1, and equal-index transitions. No proper/nonempty
ideal, nonzero coefficient ring, lower bound on K, quasi-compactness of j,
completeness of J K, or preservation of infinite products by J is assumed.
The tensor comparison and the finite projection-adjoint maps have the same
orientation in all these cases. Only the antecedents L_n are bounded below.
The finite quotient hypothesis is used for witness transport; the earlier
strict reduction/completion statements hold with the weaker recorded datum.

### Searches and verification

Searched with the prescribed msearch.py wrapper:

* LeanFinder, “Derived adic completion of extension by zero has the same strict
  quotient diagram as levelwise extension by zero”: eight hits, the
  `IsAdicComplete.StrictMono` algebraic completion lemmas and
  `AdicCompletion.map_exact`; no derived pro-etale strict tower statement.
* Loogle, `CategoryTheory.Adjunction, CategoryTheory.NatIso`: invalid/zero-hit
  name query, replaced with valid `CategoryTheory.Adjunction`: twelve generic
  adjunction declarations, including `Adjunction`, `Adjunction.id`,
  `Equivalence.toAdjunction` and `Adjunction.mkOfHomEquiv`; none states the node.
* Mathlib grep, `extensionByZero|adicCompletion|KFlat` in CategoryTheory: no hits
  for the requested combination. Module-change, derived-functor and exact
  evaluation source signatures were subsequently opened directly.
* `rg` in upstream WeilConjectures and shared `lean/Sheaf` for extension,
  completion, K-flat and strict-tower APIs found the recorded interfaces listed
  above, but no declaration stating this result. The exact item-id search in
  upstream WeilConjectures found no previous declaration. DAG searches checked
  existing notions and the dependency closures; the item itself has no Lean
  record despite its completed stage-1 review.

All delivered Lean is checked through scompile.py, separately as the sole
module. The delivery dry run and final delivery are performed with deliver2.py.
No live source was edited, no direct Git operation or global build was run,
and no additional worker was started.

No STATEMENT-DISPUTED finding, new definition node, dependency-module repair,
or statement correction is required.

## Second reading by Q19

Independent maintainer reading of immutable delivery
`4722575a13a2d480717913a8e9a9e4b431026135`, performed on 2026-10-18.
Verdict: correct mathematical statement and constructions; report-only FIX for H11.

The original section contained only the sentence that no worker second reading had
occurred. That accurately disclosed the workflow, but did not supply the real
second reading required for this review. This section replaces that placeholder;
the complete Worker report above is preserved. No Lean or JSON change is needed.

### Hypotheses, objects and conclusions checked independently

| Node clause | Delivered Lean and finding |
| --- | --- |
| Commutative Noetherian A, finitely generated I, additive-torsion A/I, perfect A/I^n for positive n | `CompleteCoefficientDatum A`: inspected `ideal`, `noetherian`, `finitelyGenerated`, `quotientTorsion`, `quotientPerfect` in its owning module. Exact hypotheses; no assumption that A is complete. |
| Every positive quotient finite as a set | The principal theorem has `[∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1))]`. This is additional to, and not inferred from, the datum. |
| Arbitrary schemes and open immersion | `{U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]`. No quasi-compactness, properness, separation, or nonemptiness is added. |
| Small pro-etale sites and constant A-module sheaves | `adicConstantRing`, `adicModuleRing`, and `proEtaleDerivedCategory` use constant-sheafification of ULift A on `ProEt.topology`. They are ordinary unbounded derived categories of actual module sheaves. |
| Localized-site extension by zero J | `sfCbcConstantSliceMap` is uniquely determined by constant sections; `sfCbcConstantModuleToSlice` uses the concrete slice-site functor. `sfCbcOpenExtension` uses the existing direct-sum extension presheaf followed by module sheafification. `sfCbcOpenExtension_exact` supplies exactness. |
| Termwise extension on strict sequences and complexes | `sfCbcTowerExtension` is whiskering on `ℕᵒᵖ ⥤ Mod`, and `sfCbcDerivedTowerExtension` derives that exact functor. `sfCbcDerivedExtension` derives ordinary extension. |
| Actual derived strict reduction tower, computed on one flat-term K-flat representative | `sfCbcReduction` uses the existing `ConstantCompletion.quotientPresentation`, whose universal comparison and K-flat computation were inspected. `sfCbcTowerDerived` is D(Fun(Nop,Mod)), not Fun(Nop,D(Mod)). |
| Preservation of flat-term K-flat complexes | `sfCbcExtensionModel_existsUnique` fixes both the actual termwise extended complex and its realization. Its proof fields are propositions; the uniqueness assertion does not identify arbitrary resolutions. |
| Canonical tensor comparison of strict towers | `sfCbcOrdinaryTensorComparison_existsUnique` is normalized by quotient units; `sfCbcTensorComparisonNormalized` specifies its K-flat localization formula. `sfCbcTensorComparison` is the resulting natural isomorphism. |
| Completion with specified unit | `sfCbcCompletion` is reduction followed by total right derived strict limit and inverse site transport. `sfCbcCompletionUnit` transports the published quotient-unit map, including the equivalence unit. |
| Invertibility of reduction of the completion unit on J K | `sfCbcReducedCompletionUnit` is literally that whiskered map; `sfCbcReducedCompletionUnit_isIso` and the first principal conjunct assert invertibility. No completeness of J K is assumed. |
| q is inverse reduced unit followed by the tensor comparison; normalized equation | `sfCbcCompletedReductionIso` has exactly that definition. The second principal conjunct states the equation with Lean's left-to-right composition convention. |
| Finite forward map is adjoint to the limit projection and inverse is reduced unit | `sfCbcFiniteCompletedHom` uses `adicReductionHomEquiv`, the unit-preserving `sfCbcCompletionModelIso`, and `adicCompletionEvaluation`. `sfCbcFiniteCompletedHom_inverse` gives precisely the inverse formula after the tensor endpoint identification. All these finite arrows retain P_n coefficients. |
| Finite maps agree with evaluation of q | `sfCbcFiniteModelIso_existsUnique` is fixed by quotient augmentations; `sfCbcFiniteEvaluationIso` uses the universal counit. `sfCbcCompletedReductionIso_evaluation` states the full comparison square, not just existence of two unrelated isomorphisms. |
| Naturality and every quotient transition before Rlim | Naturality of the strict maps is built into natural transformations/isomorphisms. `sfCbcFiniteCompletedHom_naturality` quantifies over arbitrary input maps and models. `sfCbcFiniteUnderlyingHom_transition` covers every n ≤ m, including equality. |
| Completed output and specified limit presentation | The third principal conjunct is the existing local internal-Hom completeness predicate. `sfCbcCompletedExtensionPresentation` is Rlim of the tensor comparison; it never interchanges J with Rlim. |
| Retained bounded-below etale-origin witnesses | `sfCbcEtaleExtensionPlus` has the actual derived etale j! antecedent. `sfCbcTransportEtaleWitnessIso` composes the published nu/j! comparison, J of the supplied alpha, and the inverse finite comparison. The last principal conjunct states existence for this specific antecedent. No compatible tower of antecedents is required. |

The main theorem is read together with its recorded helper declarations, not as
an isolated conjunction. The supporting declarations explicitly supply the
preservation, transition, evaluation, inverse, and presentation clauses above.

### Dependency and source audit

Read the immutable item node and all 21 statement-dependency records and their
statements. Opened the recorded interfaces in the read-only group clone or pinned
Mathlib/upstream source, including their declaration docstrings:

- `CompleteCoefficientDatum`: the real datum, K-flat models, reductions, and transitions.
- `IsOpenImmersion`: Mathlib's open immersion of locally ringed spaces.
- `Scheme.ProEt`: weakly etale objects over a scheme with the fpqc-generated topology.
- `constantSheaf`: constant presheaf followed by sheafification.
- `ringedSiteModules`: transparent reuse of `SheafOfModules`, not another category.
- `DerivedCategory`: localization of complexes at quasi-isomorphisms.
- `localizedModuleExactIndependent`: exact extension and restriction; inspected its
  direct-sum/sheafification definition and uniquely normalized adjunction.
- `ProEt.weaklyEtale_localization`: concrete slice equivalence and constant coefficients.
- `Functor.ofOpSequence`: strict inverse sequences with the harmless positive reindexing.
- `exists_diagramSite_realization`: diagram-site realization and exact evaluation.
- `IsKFlatIndependentCoefficients`: actual acyclic-total-tensor predicate; inspected
  the same module's `IsKFlat` compatibility interface used by the datum.
- `completedPullbackAdjunction`: quotient-tower completion, reflector and unit normalization.
- `ringedStrictTowerHomotopyLimitOfUniverses`: independent site universes and actual Rlim.
- `EtaleOriginWitness` and its owning module's `etaleOriginScalars`,
  `etaleOriginRealization`, `etaleOriginComparison`: retained pair and fixed realization.
- `openImmersionLowerShriekComparison_coherence` and the actual
  `openImmersionLowerShriekComparisonUpperStarIso`: the latter is the conjugate of
  the identity restriction square, not an arbitrary chosen isomorphism.
- `proEtaleSheafInverseImage`, `proEtaleSiteModel`, `proEtaleModelTopology`, and
  `proEtaleModuleToModel`: actual site transport and sectionwise module transport.
- `ConstantCompletion`: quotient system, local completeness, strict limit,
  universal quotient presentation, and specified completion unit.
- `OrderedExchangeInterface.completionMateComparison`: recorded existing interface;
  the delivery does not substitute its generic sites for the small pro-etale site.
- `adicCompletionReduction_isIso`: reduction of completion for arbitrary input,
  with the actual projection-adjoint map and no input-completeness assumption.
- `completedOpenExchangeComparison`: only its publicly imported coefficient-independent
  `cbcSliceFunctor`/`cbcOpenObject` geometry is used here. Its quasi-compactness and
  completed coefficient ring are not smuggled into this statement.
- `adicCompletionMap`: concrete product-cone completion unit. Also inspected its
  evaluation and the derived scalar Hom equivalence in `AdicCompletionReduction`.

Inspected `RingedSliceExtensionTensor` for the extension/tensor construction.
Read `coord/pefw-upstream-framework.md`; checked the finite-coefficient open
extension and adjunction in the group's `lean/WeilConjectures/` overlay, and the
actual comparison declaration in the group's
`WeilConjectures/SixFunctors/ProEtale/Derived/LowerShriekComparison.lean`.
The older slopmaster2 framework is not used as a substitute for the side framework.

Source places read: the original
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/fix-lem-exchanges.md`,
and the later proof file under
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/`;
Stacks `proetale.tex` lines 4305ff (099M), 4336ff (099N), 5076ff (j!-comparison),
and `sites-cohomology.tex` lines 5067ff (0941). The blueprint exchange construction
motivates this agent-stated strict-diagram prerequisite; no claim is made that
one Stacks tag verbatim states the entire delivered result.

Independent searches used alternate terms including extension/completion,
K-flat preservation, and strict reductions across the group Sheaf modules,
upstream pro-etale lower-shriek modules, and Mathlib category/site sources.
The existing completed-coefficient open-exchange result has different coefficients
and a quasi-compactness hypothesis; it is not this constant-coefficient theorem.
The delivery reuses the existing categories, tensor, extension presheaf, site
transport, quotient presentation, and completion predicate. Its new helpers fix
specialized canonical transports and comparisons. No duplicate core notion found.
The Worker report retains its LeanFinder, Loogle and textual search records.

Checked dependency closure using the immutable item's dependency list and 18,859
read-only group-clone node records: no unresolved dependency ID and no path from
any statement dependency back to this item. No new DAG prerequisite, helper node,
§1(B) dependency repair, or §1(C) statement correction is needed.

### Universes, edge cases and maintainer gates

The original site has object universe t+1 and morphism universe t. The existing
AsSmall presentation enlarges Hom sizes by equivalence; it retains all objects
and the original topology. Coefficients use ULift to t+1. No equality of the
original site universes or smallness assumption on test schemes is introduced.
`autoImplicit` is false; no free bound variable/universe was found.

Checked j = identity, the empty open, the empty scheme, zero complex, zero ring,
I = unit ideal, and I = zero ideal when the stated finite/torsion hypotheses hold.
For I = unit ideal all reductions and completion are zero; for I = zero ideal
completion is the identity. The first Lean index 0 means exponent 1, not I^0.
Equal-index transitions are included. No boundedness is imposed on K; only the
etale antecedents are bounded below. No assertion of ordinary J preserving
inverse limits or ordinary J K being complete occurs.

All 83 declared names are listed, in order, in `lean.declarations`.
All 21 mathematical theorem bodies are exactly `sorry`; instance projections
and typeclass inference are only structural bookkeeping. Definitions supply
real data or choose from uniqueness/universal-property specifications.
In particular no arbitrary unnormalized map or mere existence of an unspecified
isomorphism is substituted for a canonical construction. Every declaration has
its source/blueprint docstring, and theorem docstrings carry the relevant proof
steps. No line exceeds 100 characters. The node's `lean.statement` is verbatim
the principal signature up to (excluding) `:= by`.

### Compiler evidence and findings

Reproduced the immutable sole delivered module with:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q19 lem-sf-cbc-extension-zero-completion snapshot/lean/Sheaf/Paper/SfCbcExtensionZeroCompletion.lean
```

Exit status 0. Wrapper output:

```
sandbox Sheaf/Stage2/Sandbox0.lean
(with the modules compiled into /dev/shm/nt-tmp/nt-local-compile-wdjea26f/.lbuild) [28.0 s]
library Sheaf/Paper/SfCbcExtensionZeroCompletion.lean
[29.4 s]
```

No diagnostics were reported. The installed wrapper identifies itself as the
2026-10-17 server-overlay implementation; this prescribed wrapper performed
both checks, rather than a direct SSH command or global build. Thus this is
fresh reproducibility evidence for the report's compile assertion, not a claim
to have recovered a historical compile transcript.

The immutable Lean file SHA-256 is
`0d3fffa91bfb8177f25f6f3b64a99b2e7a902399fcb621d2d5f4d35626936c01`.

Finding H11 (also the user's real-section gate): the original second-reading
section was a placeholder, not an independent clause-by-clause reading.
Corrected by this complete replacement report. No mathematical or Lean change.
The fix filename is the report override accepted by
`tools/merge_delivery.py --stage 2`: `lem-sf-cbc-extension-zero-completion.report.md`.
No merge/preflight/delivery command, Git mutation, global build, or live Lean edit
was performed; only review.md and this corrected report were written.
