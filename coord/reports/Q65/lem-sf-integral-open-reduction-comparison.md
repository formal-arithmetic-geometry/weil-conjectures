## Worker report

The delivery states `WeilConjectures.IntegralOpenReduction.integralOpenReductionComparison`
in `Sheaf.SixFunctors.IntegralOpenReductionComparison`. Its only postponed proof is this
named theorem. Its docstring follows all ten proof steps of the node. All helper definitions
have real data. The structures describe the specified constructions and their normalization;
their existence is a conclusion, never an extra hypothesis on the input.

Sources read: the complete item and its ten proof steps; every statement dependency's
statement and Lean record; their actual declaration signatures and docstrings;
Stacks `sites-cohomology.tex`, lemma-j-shriek-and-tensor (0GL1), and
`sites-modules.tex`, lemma-j-shriek-and-tensor (0E8I); current blueprint
`sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md`, especially its
sentence beginning “The maps used here are tensor reassociation, evaluation”.
The source's tensor comparison is for arbitrary unbounded complexes.

Hypotheses and objects, clause by clause:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]`
  and `[FiniteDimensional ℚ_[l] E]`.
- Its valuation ring, chosen uniformizer and positive quotients: the dependency's
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing`. No new coefficient rings are defined. The chosen
  uniformizer is the one fixed by the dependency; the ideals are powers of the
  maximal ideal, independently of its generator. Natural index n means exponent n+1,
  so n=0 includes precisely the source's first positive quotient.
- Schemes and quasi-compact open immersion: `{U X : Scheme.{t}} (j : U ⟶ X)`
  with `[IsOpenImmersion j] [QuasiCompact j]`.
- Ell invertible on both schemes: `_hlX : IsUnit (l : Γ(X, ⊤))` and the
  corresponding `_hlU`. These express exactly the source's invertibility condition.
- Small pro-etale sites: the existing `Scheme.ProEt` and `ProEt.topology` throughout.
  The site has object universe t+1 and morphism universe t; E has independent
  universe u, and sheaves/modules use max u (t+1). No universe equality is imposed.
- Completed coefficient sheaf and its restriction identification: the existing
  `completedIntegralCommRingSheafUnrestricted`; `Coefficients.finiteMap` is fixed
  by `finiteConstants` on actual constant sections. `completedMap` is fixed by
  `projections` for every quotient. `integralFunctor` and `finiteFunctor` require
  literal module pushforward along the existing `cbcSliceFunctor` and these maps.
  Thus these are presentations of j-inverse Rhat_X = Rhat_U, rather than arbitrary
  ring identifications. The `integral` and `finite` equivalences supply the canonical
  ringed-site transport, with no new ring or coefficient-category notion.
- Strict systems, R, L, u and e: `coefficientSequenceModules`,
  `coefficientSequenceDerived`, `SX.reduction`, `SU.reduction`,
  `coefficientSequenceLimit`, and the actual `SX.adjunction`/`SU.adjunction`.
  SX, SU and their full `CoefficientDerivedSystemCoherence` are supplied as
  conclusions using the recorded coefficient calculus; there is no effectivity
  or reconstruction hypothesis smuggled into this input.
- J_j: `systemExtension` is concrete coefficient transport followed by the
  existing `SemilinearSections.OpenSystems.extension`, with its normalized
  component adjunctions; `J` is its exact ordinary derived functor.
  `systemComponents` pins every component of the ring-system map, and that map is
  one natural transformation on the product site, so includes all strict transitions.
  `transportSections` pins the evaluation transport to the identical section.
- Completed-coefficient j_!: `extension` is the actual slice transport followed
  by the existing `localizedSystemExtension` (direct sums, then sheafification).
  `shriek` is its exact localized functor. `ordinaryAdjunction`, `openAdjunction`
  and `systemAdjunction` are constructed from the recorded summand-normalized
  ordinary adjunctions and the exact localization operation, not chosen derived
  adjunction structures.

Conclusions, clause by clause:

- Arbitrary derived-complete K: `complete` is exactly
  `IntegralOnSlice.IsComplete l E T none`, the dependency's global branch, hence
  the existing augmented quotient-tower Roos condition. `Comparison.r` is a
  natural isomorphism on the full subcategory of all such K. No boundedness,
  constructibility, finite-type, or Noetherian condition is added to K or the schemes.
- Specified r_j(K): `StrictModel` requires one chain isomorphism f on the actual
  system category and the equality identifying r with its localization in that
  category. The two reduction presentations use the existing
  `CoefficientReductionPresentation`, including strict transitions.
- No arbitrary lifts: `AugmentedPresentation` additionally requires one chain
  augmentation from the constant tower. On every degree, index and section it is
  exactly the actual scalar-adjunction unit followed by the inverse presentation.
  Its transpose under the existing constant-tower/total-limit adjunction must equal
  the transpose of eC/eD under the actual reduction adjunction. This fixes eC and eD
  as whole-system arrows, not just their evaluations.
- Canonical evaluation at n and strict quotient compatibility: the last equation
  in `StrictModel` is equality of component module maps in every degree with
  `tensor.ordinary n`. `TensorComparison.generators` fixes that ordinary iso by
  `1 tensor extensionSection(x) ↦ finiteExtensionSection(1 tensor x)` for every
  extension summand. Linearity fixes all coefficient multiples. All degree components
  belong to the single chain isomorphism f; all quotient transitions belong to the
  single strict system objects, so compatibility is before localization. The derived
  finite tensor evaluations follow with the dependency's `reductionEvaluation` and
  its canonical K-flat model comparisons.
- Derived completeness of j_!K: `Comparison.extensionComplete` uses exactly the
  same `complete` predicate on X.
- Invertibility of the actual unit: `Comparison.unitX` and `unitXHom` give an iso
  whose hom is literally `SX.adjunction.unit.app H.obj`; apply to
  `⟨shriek.obj K, extensionComplete K⟩`. `unitU` has the analogous actual-unit pin.
- d_j(K): `Comparison.d` is a natural iso, and `dFormula` is exactly L_X(r^-1)
  followed by u_(j_!K)^-1, in Lean's left-to-right composition order.
  `reductionD` records r after R_X(d) = the actual coherent counit.
- Corresponding completed restriction: `s` compares ordinary restriction's
  reduction with actual system restriction; `restrictionComplete` gives the
  completeness of that restriction. `pullRealization` and `pullFormula` identify
  its realization by L_U(s^-1) followed by the inverse actual unit. This is the
  quotient-completed restriction with the specified completion unit.
- Open unit and counit: `systemUnit` and `systemCounit` are equations of actual
  derived system maps. `realizedUnit` and `realizedCounit` write out their realized
  words using the actual reconstruction units, d and the restriction comparison,
  and equate them to `openAdjunction.unit` and `.counit`. There is no assertion that
  finite evaluations detect equality of arbitrary derived morphisms.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imported
  `CoefficientExtension`: the Padic coefficient constructions and positive-level finiteness.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  scheme-property convention: Mathlib `IsOpenImmersion`, `QuasiCompact`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`,
  `CoefficientReductionPresentation`, `coefficientIntegralScalarUnitSection`;
  its imported `CoefficientRingedSequenceSite`: the actual system categories,
  exact evaluation, strict scalar restriction, and total limit.
- `Sheaf.Paper.SemilinearDerivedSections` and `SemilinearDerivedCalculus`:
  `SemilinearSections.OpenSystems`, `openRestriction`, `systemRing`, and `evaluation`.
- `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction` and the
  canonical open-tensor/unit normalization used in the statement and proof plan.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`.
- `Sheaf.Paper.CompletedExtensionZeroComparison`: `cbcOpenObject`,
  `cbcSliceFunctor`, and its continuity instance; these are reused, not copied.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `localizedSystemExtension`, `localizedSystemRestriction`, `localizedSystemAdjunction`
  and their existing exactness instances.
- Additional existing definition dependency `def-trf-integral-comparison-realization-models`,
  module `Sheaf.Paper.IntegralComparisonRealizationModels`:
  `integralComparisonConstantAdjunction`. This existing adjunction fixes the whole
  strict augmentation's transpose in `AugmentedPresentation`; no parallel definition
  was created. It was added to stmt_deps as permitted for already landed notions.
  Source dependency closure was checked and has no path back to this item (853 nodes
  visited). The item's other fields, statement and ten proof steps are unchanged.
- All recorded stated proof dependency modules are imported with non-public imports,
  including effectivity, completed open exchange, Koszul reconstruction, completed
  constant reduction, K-flat resolution, ringed slice tensor and strict tower limit.

Edge cases checked before and after writing: U empty, X empty, identity open U=X,
K=0, the first quotient n=0/exponent 1, arbitrary later transitions and identity
transitions, arbitrary unbounded complexes, ell=2, unrelated sizes t and u. None is
excluded by the binders or construction. Empty direct sums give zero extension;
no nonempty or inhabitance assumption is used. The hypotheses on ell concern the
schemes, not extra torsion restrictions on the input complex.

Searches actually run:

- msearch LeanFinder: “extension by zero derived complete module sheaves strict
  coefficient reduction systems adjunction comparison”: eight hits on adic-completion
  lifts and condensed locally constant modules; no matching sheaf-system theorem.
- msearch Loogle: `SheafOfModules, Adjunction, IsIso`: zero hits, reported unknown
  identifier `Adjunction`; this is not evidence of an exhaustive typed search.
- msearch LeanSearch: “extension by zero commutes with derived reduction of complete
  coefficient sheaves”: eight unrelated zero-object/zero-map hits; no match.
- msearch grep: `extensionByZero|extension_by_zero|jShriek` in Mathlib/CategoryTheory:
  zero hits. Second grep `completed.*extension.*reduction|open.*tensor.*comparison`
  in Mathlib/AlgebraicGeometry: zero hits.
- rg in upstream WeilConjectures for the item ID and open/reduction comparison names:
  no copy of this statement. Related reduction-direct-image and nilpotent-reduction
  theorems have different objects and conclusions.
- rg in `lean/Sheaf`: located `SfCbcExtensionZeroCompletion` (constant-coefficient
  quotient towers, not these varying semilinear systems), `CompletedOpenExchangeTransport`
  (intrinsic completed exchange, not r and its actual-unit realization),
  `IntegralComparisonRealizationModels` (pullback/scalar realization), and the exact
  recorded coefficient/open dependencies. Their notions are reused where applicable.
  The namespace `WeilConjectures.IntegralOpenReduction` and its declaration names did
  not already occur. No exact existing declaration covers the entire item.

No statement correction, disputed statement, new DAG node, or dependency-record repair.

## Second reading by Q65

Independent maintainer reading of immutable delivery
`0d3abd6e3ff0ec51a97e424de7b515db3fb7d8fa`, 2026-10-18. This replaces the
worker self-reading; the reviewer did not write or previously second-read this delivery.
The original Worker report above is retained.

I read the item, all eight statement-dependency records, the complete delivered
module, and the exact imported interfaces in the read-only Q65 clone. I read
Stacks sites-cohomology.tex, lemma-j-shriek-and-tensor (0GL1), lines 4578 onward,
and sites-modules.tex, lemma-j-shriek-and-tensor (0E8I), lines 4051 onward.
Both concern arbitrary modules/derived complexes on a localized ringed site;
neither imposes boundedness. I also read the open-factor coherence context in
literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/
fix-prop-coherence.proof.md. The completion assertion uses the separately cited
completed-extension comparison, rather than attributing it to the tensor lemma.

Hypothesis and object checks:

- Prime and finite extension: l, Fact l.Prime, E, Field, Algebra and
  FiniteDimensional binders give exactly the coefficient datum. The existing
  Padic coefficient constructions supply the valuation ring, chosen uniformizer
  and quotients. The shift n to n+1 includes every positive exponent.
- Geometry: Scheme.{t}, IsOpenImmersion j and QuasiCompact j are explicit.
  IsUnit of l in both global-section rings expresses invertibility on the schemes.
  No Noetherian, constructibility, finite Tor-amplitude or boundedness assumption
  has been added. The two invertibility hypotheses are those stated in the node.
- Site and sizes: Scheme.ProEt with ProEt.topology is the actual small pro-etale
  site. The independent sizes t,u are retained, with site objects in t+1, arrows
  in t and modules in max u (t+1). No smaller-site substitute or size equality occurs.
- Coefficients.finiteConstants fixes the finite slice map on sheafification units;
  projections fixes the completed map on every quotient. integralFunctor,
  finiteFunctor and systemsFunctor fix the concrete cbcSliceFunctor pushforwards.
  systemComponents and transportSections retain the strict coefficient transitions.
- complete is IntegralOnSlice.IsComplete at none. I followed this through
  DerivedCompleteUnrestricted to IsDerivedComplete and its augmented quotient
  Roos triangle. The auxiliary finite-field existential adds no geometric assumption.
- extension and restriction reuse localizedSystemExtension/Restriction;
  ordinaryAdjunction uses the actual summand-normalized adjunction. J and P reuse
  OpenSystems and exact localization. exactDerivedAdjunction is a real localization
  construction; no arbitrary derived adjunction is substituted.

Conclusion checks:

- Comparison.r is a natural isomorphism on all complete objects with the correct
  direction R_X(j_!K) to J_j(R_U K). StrictModel gives one chain isomorphism f of
  actual systems and identifies r with its localization before evaluation.
- CoefficientReductionPresentation fixes every quotient transition and the finite
  representative identifications. AugmentedPresentation further fixes one strict
  scalar-unit augmentation and its transpose under the actual constant/limit
  adjunction. This prevents freedom to lift a family of evaluated derived maps.
- TensorComparison.generators fixes the ordinary map on every extension summand
  and scalar-unit generator. The last StrictModel equation identifies all finite
  chain components with that map. Thus the canonical tensor clause and all strict
  quotient transitions are present, without assuming evaluation is faithful.
- extensionComplete gives quotient completeness of j_!K. unitXHom identifies the
  reconstruction isomorphism with the actual SX.adjunction.unit, rather than an
  arbitrary isomorphism. unitU supplies the analogous input normalization.
- dFormula is exactly L_X(r^-1) followed by u_(j_!K)^-1. reductionD gives the actual
  counit normalization. Its orientation agrees with proof Step 7.
- restrictionComplete, s, pullRealization and pullFormula give the corresponding
  completed restriction. systemUnit/systemCounit and realizedUnit/realizedCounit
  write the two adjunction identities as equations of whole-system/realized maps.
  These are the correct mate and realization words, including their order.

I matched the main docstring to all ten node proof steps: normalized quotient
balancing; invertibility of the actual unit via effectivity and naturality;
DVR/finite-quotient Koszul identification; extension completeness; preservation
of flat-term K-flat models; the strict tensor chain comparison; d and its counit
identity; complete restriction; system unit; transposed counit and realization.
No new independent prerequisite, missing helper or universe repair was found.

Edge cases: empty U or X, identity open, zero K, the first positive quotient,
identity and composite quotient transitions, ell=2, arbitrary unbounded complexes,
and unrelated coefficient/site sizes remain allowed. The empty-open summands give
zero extension and no nonemptiness assumption appears.

One-definition checks used rg on Mathlib, upstream WeilConjectures, the upstream
name index and the side Sheaf tree. The related SfCbcExtensionZeroCompletion and
CompletedOpenExchangeTransport interfaces concern different coefficient/system
presentations and do not state this comparison. Existing coefficient, slice,
strict-system, adjunction and completeness notions are reused. The worker's three
search kinds are recorded above, including the unsuccessful typed-search query.

Mechanical checks: lean.statement equals the complete theorem signature verbatim;
all 43 explicit declaration names match lean.declarations in order. Maximum line
width is 100; autoImplicit is false; the only sorry is the main named theorem.
Definitions and instances contain concrete data or inherited instances. Module and
declaration docstrings carry sources and the blueprint id. There are no new DAG
nodes, dependency record repairs or statement corrections. The added realization
model dependency is an already recorded node, authorized by the landed-node rule.

Route-pivot check: the item's statement/proof dependencies and the eight supplied
records cite no id on origin/newtargets-dag:coord/route-pivot-dropped.txt. There is
no item repair note at that ref. The construction uses ordinary derived categories
of strict systems, K-flat representatives and total right-derived limit; no dropped
infinity/dg/model-category machinery is introduced.

Independent compilation: ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q65
lem-sf-integral-open-reduction-comparison
snapshot/lean/Sheaf/SixFunctors/IntegralOpenReductionComparison.lean`
with the immutable file's absolute context. Exit code 0, no errors or warnings:
sandbox check 53.2 seconds; library-path check 30.9 seconds. The installed wrapper
currently uses the server private side overlay, not the historical local wrapper
mode described in the brief. No timeout was raised and no global build, direct
SSH command, project edit or branch mutation was performed.

Finding H11: the original section explicitly identified itself as a worker
self-reading. This complete report replacement supplies the independent reading
required by the contract. The mathematical module and node need no changes.
