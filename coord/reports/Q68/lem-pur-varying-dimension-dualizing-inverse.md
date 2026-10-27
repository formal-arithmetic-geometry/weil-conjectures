## Worker report

The module `Sheaf.Paper.VaryingDimensionDualizingInverse` states
`lem-pur-varying-dimension-dualizing-inverse`. Its three theorem declarations have
` sorry` proofs. `DualizingInverseAssembly` is a transparent proposition packaging
the inverse objects, both evaluation isomorphisms, and their component equations;
it has real data and introduces no replacement tensor, unit, or pullback.

The node's geometric and coefficient clauses are rendered as follows.

* The fixed finite field, algebraic closure, coefficient prime distinct from the
  characteristic, finite coefficient extension, valuation ring and positive level
  are the existing `P : PurityFiniteSetting.{u}`. The extension is literally the
  datum's finite intermediate field. Every finite quotient in this module is
  `Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)`; `n : ℕ`
  therefore ranges over all positive exponents and excludes the zero quotient.
* `V B : Over (Spec (.of P.field.k))` and `g.IsOver ...` are exactly schemes and
  a morphism over the fixed algebraic closure. On each structure morphism,
  `LocallyOfFiniteType` and `QuasiCompact` express finite type. The corresponding
  instances on `g`, together with `Smooth g` and `IsSeparated g`, express the
  stated assumptions. Neither absolute structure map is required separated.
  There is no section binder or assumption of constant relative dimension.
* `smooth_dimension_clopen_partition` supplies `U : ℕ → V.left.Opens`, with
  `↑(U d) = {x | topologicalKrullDimAt (g.asFiber x) = d}`. These are exactly the
  loci defined in the node. `Set.Finite {d | (↑(U d)).Nonempty}` is finiteness of
  I, `IsClosed ↑(U d)` supplies closedness, and `Disjoint` and the `iUnion = univ`
  clauses give disjointness and coverage. The final conjunction gives pure smooth
  relative dimension d, separatedness, finite type of the restricted map and
  finite type of the component over k, including the empty loci.
* The assembly section accepts any presentation of the nonempty loci:
  `I`, `[Finite I]`, components `Vi`, inclusions `j`, an injective `dimension : I → ℕ`,
  nonemptiness, and equality of each image to its dimension locus. This is a
  reindexing of `{d | (↑(U d)).Nonempty}`, not a constant-dimension assumption.
  The preceding partition theorem supplies these data. The separate clauses
  for the component structure maps and immersion properties are its consequences,
  made explicit because the existing comparison interface requires them.
* The sites are the actual `Scheme.ProEt.topology` throughout the imported
  intrinsic coefficient categories, with object universe u+1 and morphism
  universe u. No equality of these universes is imposed. The labelled index type
  has an independent universe w, as permitted by the finite-clopen equivalence.
* `varyingDimension_finite_dualizing_inverse` uses the actual
  `clopenFiniteExceptional ... g n` applied to
  `finiteConstantCoefficientObject ... B.left n`. The first conjunct is the
  derived isomorphism from its pullback along j_i to the exceptional object of
  `j_i ≫ g`, at every positive finite level. These are derived isomorphisms,
  not merely isomorphisms of their cohomology sheaves.
* At integral and field coefficients, `varyingDimension_dualizing_inverse`
  supplies `R` and `Ri : ∀ i, ClopenExceptionalAllCoefficients ...` for a common
  compactification. `R` is the identity-component record, and the three displayed
  functor equalities ensure that each `Ri` uses the same global integral,
  rational, and algebraically closed exceptional functor as `R`. Each record
  contains its actual strict exceptional system, normalization, comparison of
  sites, finite evaluation comparisons, derived-limit realization, and
  rationalized/common-stage comparison equations. The imported
  `integralUnitComparison`, `rationalUnitComparison`, `commonStageUnitComparison`
  and `finiteUnitComparison`, evaluated on these records, are the displayed
  dualizing restrictions. In particular integral coherence is asserted on
  actual derived strict systems; it is not inferred from unrelated finite maps.
  Compactification is a presentation parameter, available by Nagata in precisely
  the stated finite-type separated setting; no exceptional admissibility datum
  is an assumption.
* The units are respectively `finiteConstantCoefficientObject`,
  `clopenIntegralUnit`, `clopenRationalUnit`, and `clopenCommonStageUnit`. The
  completed unit is the actual completed regular module in degree zero.
  Rational and common-stage units are its existing coefficient transports.
* `DualizingInverseAssembly.good omega` asserts the finite-Tor membership of the
  global dualizing object. Its existential `Q`, `good Q` and the two `Nonempty`
  isomorphisms are a two-sided inverse in the same category. At integral level
  `good` is `finiteTorConstructibleIntegral ... K.obj`; at finite level it is
  `finiteTorConstructible ... (n+1) ...`. At field stages the ambient categories
  already are Dbc = Dbctf, hence `good = ⊤` adds no hypothesis or substitute for
  constructibility.
* For arbitrary component inverses `Qi` and specified maps `ei,ei'`, the last
  part of `DualizingInverseAssembly` supplies a global inverse `Q`, both maps
  `e,e'`, and identifications `p i : j_i^* Q ≅ Qi i`. Its two final equations
  say exactly that the restriction of each global evaluation is the specified
  component evaluation under tensor/unit comparisons. They use ordinary functor
  maps on the ordered pairs `(id,p_i)` and `(p_i,id)`. Here the component omega
  is written as `j_i^* omega`; the preceding dualizing comparison identifies it
  with omega_(g_i). Conjugation by that isomorphism is a bijection between the
  node's prescribed component inverse pairs and these quantified pairs, so no
  inverse pair or specified evaluation map is excluded.
* The finite theorem's last two equivalences detect every common cohomological
  and Tor interval under restriction. The integral theorem gives the same
  equivalences with `∀ n` inside each fixed interval, so the interval is uniform
  in every positive finite reduction. These are the bound clauses of the
  imported finite-clopen equivalence, made available here also for the chosen
  inverse. Since the index set is finite, lower endpoints have a common lower
  bound and upper endpoints a common upper bound. Isomorphisms `p i` retain the
  prescribed component intervals. At rational and common stages the integral
  representative construction transports these bounds; a finite compositum
  accommodates the finitely many component coefficient fields.
* Nothing requires `Nonempty I`; component nonemptiness is quantified over I,
  so it is vacuous for I empty. The covering equation then makes V empty. The
  assembly still asserts a global inverse and both maps before quantifying over
  component inverses; consequently the empty case is not vacuous. All intervals
  can be [0,0] there. No coefficient-line basis or Tate orientation is an input
  or output.

Dependency declarations read and used:

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and
  its existing field/coefficient instances and quotient-ring construction.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `finiteIntrinsicDerivedTensor`, `constructibleIntegralPullback`,
  `constructibleIntegralTensor`, `rationalDerivedPullback`,
  `rationalDerivedTensor`, `commonStageDerivedPullback`,
  `commonStageDerivedTensor`; the latter six are used through the recorded
  clopen specializations, not redefined.
* `Sheaf.Paper.FiniteTorAmplitudeSites` and its public import
  `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructible`,
  `finiteTorConstructibleIntegral` and their full categories. The recorded
  etale declaration `finiteTorConstructibleEtale` is the alternative site
  presentation; this node uses its already-published intrinsic pro-etale form.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its imported
  completion modules: `completedIntegralCoefficientSheafUnrestricted` and
  the completed regular coefficient object, used by `clopenIntegralUnit`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated` (the separated
  clause of the recorded proper-morphism notion); properness is not assumed.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  together with `QuasiCompact` for finite type.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and
  `SmoothOfRelativeDimension`; `Scheme.Hom.asFiber` and
  `topologicalKrullDimAt` express the definition's fibre-dimension clause.
* `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
* `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System`, whose operation is the
  coefficient-compatible constructible exceptional adjoint; its published
  finite and strict-system realizations are reused through
  `clopenFiniteExceptional` and `ClopenExceptionalAllCoefficients`.
* `Sheaf.Paper.FiniteClopenDerivedDecomposition`:
  `clopenIntegralPullback`, `clopenRationalPullback`, `clopenCommonStagePullback`,
  their three tensor specializations and units,
  `finiteClopen_finite_bounds`, `finiteClopen_integral_bounds`,
  `finiteClopen_tensor_and_reduction`, `finiteClopen_coefficient_units`, and
  `finiteClopen_constructible_equivalences`.
* `Sheaf.Paper.FiniteClopenExceptionalRestriction`:
  `ClopenExceptionalAllCoefficients` and its inherited normalized strict-system
  data and coefficient-unit comparison definitions. These unchanged definitions
  are now owned by the new definition node
  `def-pur-clopen-exceptional-all-coefficients`. The exceptional restriction
  theorem remains a proof dependency only. No dependency module is repaired.

Proof imports include the recorded smooth relative-dimension local-constancy
module, `Sheaf.AlgebraicGeometry.SmoothTensorDuality`, and the Mathlib
closed-immersion/properness characterization. The other Mathlib permanence
inputs are in the public dependency closure. The proof prerequisites
`lem-pur-finite-setting-comparison-hypotheses`,
`lem-pur-shifted-line-site-inverse`, and
`lem-pur-complete-residue-line-inverse` have no recorded modules to import.
They are referenced in the postponed proof docstrings; they are not additional
statement assumptions.

Edge cases checked before and after drafting: empty source and empty family,
relative dimension zero, several distinct nonempty dimensions, nonseparated
absolute source/target structure maps, positive level one, arbitrary higher
positive finite levels, both tensor orders, arbitrary specified component maps,
uniform integral reduction index, and every common finite coefficient stage.
The dimension indexing explicitly excludes duplicate labels and empty components,
while allowing an empty index set. No statement correction or dispute was needed.

Searches for existing statements and notions:

* LeanFinder via msearch: “A smooth separated finite type morphism has tensor
  invertible dualizing complex assembled on clopen relative dimension loci”:
  eight hits about smooth relative dimension and standard smooth algebra; no
  derived dualizing inverse or prescribed finite-clopen inverse assembly.
* LeanSearch via msearch: “Finite clopen decomposition permits gluing two sided
  tensor inverses of smooth dualizing objects”: eight hits about finite unions
  of clopens, PiTensorProduct duals, and finitary extensivity of TopCat; no match.
* Loogle via msearch: `"dualizing"` and `"dualizingComplex"`: no hits.
* Mathlib grep via msearch: `dualizing|relativeDualizing`: ten unrelated text
  occurrences about dualizing constructions; no statement of this result.
  `dualizingComplex|relativeDualizing|clopen.*[Ii]nverse`: no hits.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for varying dimension and
  dualizing/inverse combinations found ordinary etale dualizing invertibility,
  the section-invariant special case, composition inverse assertions, and the
  finite-clopen decomposition/restriction interfaces. None states all four
  coefficient cases and the specified component inverse maps of this node.
* Search for the item id in `lean/WeilConjectures` found no declaration.
  Exact candidate declaration-name searches in both library roots and
  `dag/lean_names_upstream.json` found no duplicates.

The final file was compiled separately through scompile.py, both in sandbox and
library module modes. All three theorem bodies are exactly `by sorry`; there
are no additional proof terms, axioms, private/local replacement notions,
auto-bound variables, or file-local notation. Earlier probes were in module mode
and are kept outside the delivered Lean directory. The signature includes the
section hypotheses explicitly via `include` (smoothness, finite index, covering,
disjointness and the dimension-locus presentation), avoiding Lean's omission of
unused section parameters. The delivered record lists all four declarations.


## New nodes

`def-pur-clopen-exceptional-all-coefficients` owns the unchanged plain definitions
in `Sheaf.Paper.FiniteClopenExceptionalRestriction`: the finite adjoint comparison
Data/Coherence/combined structure, the single-field coefficient comparison
Data/Coherence/combined structure, the all-coefficients Data/Coherence/combined
structure, the finite-category abbreviation, and all four unit-comparison
specializations. Its `existing: true` attachment introduces no Lean declaration.
The source is the finite-clopen compactification argument, steps 4--11, extracted
from the section-invariant invertibility assertion. Data specify actual strict
systems, finite evaluations, adjunction and inverse-limit normalizations, and
coefficient-stage equations; this definition node asserts no existence theorem.
LeanSearch found eight normalization/clopen topology hits; LeanFinder found eight
profinite/clopen partition hits, neither this notion. Mathlib grep found none.
Project grep found the exact existing definitions in the module named above;
DAG and blueprint searches found only their theorem attachment and distinct
strict-system notions. Consequently they are reused, not copied.

`def-pur-clopen-coefficient-operations` owns the nine unchanged integral,
rational and common-stage pullback, tensor and unit definitions in
`Sheaf.Paper.FiniteClopenDerivedDecomposition`, also with `existing: true`.
They specialize existing derived operations and take the units to be the regular
completed module, its rational image and its finite-stage pair. This definition
asserts none of the decomposition theorem's equivalences. Its source is the
coefficient operations used in the finite-clopen inverse assembly in the same
section-invariant argument. LeanSearch returned eight ordinary integral/tensor
algebra hits; Loogle for `"clopenIntegralPullback"` and Mathlib grep returned none.
Project grep found these exact definitions in the decomposition module, with no
separate DAG definition owner. Both new nodes record the raw msearch results.

## Repair of immutable head e13b3399d63d

H2: replaced the saved packet's added statement dependency on
`lem-pur-finite-clopen-exceptional-restriction` with
`def-pur-clopen-exceptional-all-coefficients`. The theorem stays in `proof_deps`.
Added `def-pur-clopen-strict-system-comparison`, the recorded owner of
`clopenFiniteExceptional`, and the advised owner
`def-pur-clopen-coefficient-operations`. The live base has neither new definition
node; its item has no Lean record and omits the erroneous added dependency.
Only statement-dependency ownership and the Lean record date change from the
returned packet. The Lean file, statement, proof and proof dependencies remain
unchanged, preserving the review's accepted mathematical content.

Self-check: read the structures, all normalization predicates, coefficient unit
comparison bodies and the nine operation definitions against the new node texts.
Each geometric binder of the comparison package is explicit in its node: fixed
coefficients, three finite-type schemes, a separated finite-type map, its
compactification and a clopen inclusion. The record clauses cover the same strict
systems, comparisons, finite evaluations, limit realization, rational pure-tensor
normalization, common-stage coefficient actions and unit evaluations. No existence
claim or `.choose` is imported from the restriction theorem. The operation node
names the underlying operations and actual units without asserting compatibility
isomorphisms. Empty components, empty source/family, dimension zero, coefficient
level one and identity coefficient extensions are retained. No mathematical
statement correction, dispute, definition copy or dependency-module repair occurs.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
