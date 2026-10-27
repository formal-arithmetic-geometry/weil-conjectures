## Worker report

Delivery: `Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison`, namespace
`SheafOfModules.OrdinaryLineScalar`. Six sorry-only theorem clauses state this one
node. The helper structures package its normalized maps; no existence-only choice,
new tensor product, replacement module category, or replacement derived category is
introduced. No mathematical statement correction or dependency-module repair is needed.
The H2 return is repaired by the new definition-node record below.

Hypotheses and objects:

- The scheme is `X : Scheme.{t}`; the actual small pro-etale site is
  `Scheme.ProEt.topology X` on `X.ProEt`. The essentially-small instance records
  the size convention. Site objects have universe t+1, morphisms t, coefficients
  `max a (t+1)`, and derived morphisms w. No equality of site universes is imposed.
- `Modules X R` transparently abbreviates the recorded module-sheaf category.
  The `HasDerivedCategory` family selects localization categories consistently
  for all ring sheaves. `exists_presentations` supplies universal ordinary and
  unbounded derived scalar extension, its canonical tower normalization, and
  multiplication unitors. The parameters p and n in later clauses refer to this
  existing universal data, not an arbitrary extension-of-scalars functor.
- Ring maps are `α : R ⟶ S`, `β : S ⟶ T`; their composite is `α ≫ β`.
  The R/S/T binders are the node's R0/R1/R2 (Lean indices are ascending).
- The rank-one hypotheses are `L.IsFiniteLocallyFreeOfRank 1` and the analogous
  K hypothesis; this is the recorded local-isomorphism-to-the-unit condition.
  `isInvertible_iff_isFiniteLocallyFreeOfRank` and the local unit-isomorphism
  constructors in the upstream LocallyFree module justify this spelling.
- `b` is the prescribed exponent-one scalar comparison and `B` its signed
  comparisons, constrained by `SignedLineComparisonNormalized α L K b B`.
  They are input data, exactly as in the node. The tower theorem takes the
  signed tower equation `hB`, which the recorded signed-line theorem derives
  from the node's exponent-one tower condition, without any new assumption.
- `power L m` is exactly `signedLinePower L m`: zero is the tensor unit,
  positive integers are the existing tensor powers, and negative integers
  the existing slice internal sheaf Hom into the coefficient unit.
  The integer index includes every sign, without any positivity restriction.

Every conclusion clause:

- `exists_lineData` asserts the signed powers are rank-one in `LineData.rank`.
  `LineData.exact` gives exact ordinary additive right tensor, `factors` gives
  its termwise realization on ALL unbounded complexes, and `factors_normalized`
  uses the published K-flat representative identification and degree-zero total
  collapse. `twist` is the published K-flat derived tensor, not a freely chosen
  exact functor.
- `LineData.evaluation` is normalized on every local signed basis by
  `evaluation_basis`: e^m tensor e^-m goes to 1. This determines precisely
  ordinary sheaf evaluation (symmetry for negative exponents; multiplication
  for zero). `epsilon` is the derived inverse-twist isomorphism, and
  `epsilon_computed` requires its image to be the termwise ordinary evaluation
  followed by the tensor unitor. Both opposite orders occur as m varies.
- `FlatModel` is exactly independent-coefficient K-flatness AND flatness of
  each term. `LineData.flat` and `Comparison.extended_flat` assert the two
  claimed preservation statements. `single_flat` records the degree-zero
  line models needed by the published derived-tensor normalization.
- `ordinary_line_derived_scalar_comparison` supplies `Comparison`.
  Its `ordinary` natural sheaf isomorphism induces the chain isomorphism by
  `Functor.mapHomologicalComplexCompIso`. `hom_formula` is literally
  ((p tensor l) tensor s) maps to (p tensor s) tensor B(l tensor 1).
  `inv_formula` sends (p tensor s) tensor B(l tensor q) back to
  (p tensor l) tensor sq; thus it specifies reassociation after B inverse.
  These formulas use sheafification-unit pure tensors, not a claim that all
  global sections are pure tensors.
- `Comparison.derived` is a natural isomorphism of derived functors, giving
  naturality for arbitrary derived morphisms. `representative` equates its
  localized chain map with the fixed universal computation morphisms
  `compute`, and the natural all-complex line identifications. The ordinary
  comparison and the universal counits fix the localization; full faithfulness
  on flat-term K-flat representatives gives independence of P. There is no
  arbitrary resolution-comparison hypothesis.
- `Comparison.evaluation` is exactly the node's displayed evaluation square
  (Lean composes left to right): beta_-m, then T_-m(beta_m), then epsilon_j
  equals B(epsilon_i).
- `comparison_tower` is exactly the node's displayed tower square, with
  `n.derived α β` the recorded normalized associator d. It states equality
  for every derived Y and every integer m. Its ordinary normalization,
  including (p tensor s) tensor t maps to p tensor beta(s)t, is part of n.
- `UnitData.formula` normalizes scalar extension by multiplication sp.
  `UnitData.computed` fixes its derived unitor by localization.
  `comparison_identity` states beta followed by T(lambda) equals lambda_T
  for multiplication signed-line data. Those data follow from the recorded
  `signedLineComparison_identity` applied to b_ii.
- `comparison_identity_arbitrary` retains the distinct case of identical rings
  and arbitrary line isomorphism A_m. Its `hA` identifies this with the supplied
  scalar comparison. After inverse source unitor and target unitor, the
  representative equation is precisely Q of the termwise tensor map of A_m.
  This is a natural comparison on the entire derived category; the displayed
  components specify it on arbitrary complex representatives. A_m is not
  forced to be identity.
- There are no completeness, boundedness, or flatness-of-ring-map hypotheses.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, `Qh`, `quotientCompQhIso`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  the existing monoidal, symmetric, additive tensor instances.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom: `homObj`,
  through the recorded signed powers; no private dual is defined.
- Sheaf.Paper.SignedLineScalarTensorTower: `signedLinePower`,
  `SignedLineBasisPowers`, `SignedLineComparisonNormalized`,
  `signedLineComparison_tower`, `signedLineComparison_identity`.
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients:
  `site_derived_tensor_descent_independentCoefficients` (descent proof dependency).
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel:
  `DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`
  (the universal scalar-extension interface used to justify the presentations).
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization and its public
  SuccessiveDerivedQuotientData: `Presentation`, `Normalization`,
  `successive_derived_quotient_normalization`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: `IsFlatOnSite`.
- Sheaf.Algebra.Homology.LineUnboundedDerivedTensor: `LineUnbounded.Modules`,
  `tensor`, `single`, `pureTensor`, `cancellation`, `derived`, `normalization`,
  `line_unbounded_derived_tensor`. The constructions are carried by the new
  `def-pur-line-unbounded-tensor-data` in stmt_deps; the theorem remains in
  proof_deps and is not added to stmt_deps.
- The other stated proof dependencies are imported privately: localized-site
  tensor restriction, sheaf tensor closedness, ringed-topos K-flat pullback,
  and sheaf tensor bilinear universality. Localization universal property is
  a Mathlib match and is available through the derived-category imports.

Searches made (logged by msearch.py in searches.jsonl):

- LeanFinder: “Derived scalar extension commutes with signed tensor powers of
  line sheaves and dual evaluation on unbounded complexes”: eight results about
  homological-complex tensors/unitors and derived single-functor linearity;
  none states this comparison with signed powers and its coherence equations.
- Loogle: “SheafOfModules, Functor”: zero results.
- LeanSearch: “Derived tensor by a locally free rank one sheaf commutes with
  extension of scalars and evaluation”: eight results, led by
  TensorProduct.AlgebraTensorModule.distribBaseChange and ordinary scalar
  adjunction evaluation. None is the sheaf/unbounded/coherent assertion.
- Mathlib grep: “signedLine|derivedChangeOfRings”: zero matches.
  “SheafOfModules.*[Tt]ensor|[Dd]erived.*[Ii]nvertible” in
  Algebra/Category/ModuleCat: the presheaf monoidal module only.
- rg on lean/WeilConjectures and lean/Sheaf for ordinaryLine/OrdinaryLine,
  ordinary-line-derived, signedLine with derived, and candidate declaration
  names found only the signed-power machinery and unrelated ordinaryLinear
  declarations. The exact node-id grep in lean/WeilConjectures found nothing.
  Existing fixed-ring derived line tensor and ordinary scalar signed-line
  comparisons are reused rather than duplicated.

Edge cases read against the formulas: m=0 gives the coefficient unit and its
multiplication; m=1 is the supplied line comparison; m=-1 is the actual dual
comparison; general negative m is included by the same signed family. The zero
ring and empty scheme impose no nonzero or nonempty condition. Nonflat Z to Z/2
requires only K-flat source representatives, exactly as FlatModel states.
An identity coefficient map with line multiplication by a unit v retains v^m
(and v^-m in opposite degree) in comparison_identity_arbitrary. Complexes are
Z-indexed with no bounds. Site objects and morphisms have distinct universes.
No STATEMENT-DISPUTED flag and no node faults.

Validation: the final full module compiles with scompile.py, sandbox and library
modes, within 60 seconds (55.7 s and 41.7 s in the final explicit run). Only
sorry proofs are supplied. The initial expensive elaboration was repaired by
respecting reducibility in type comparison, retaining all clauses and sizes.

## Second reading by Q132

A separate rereading pass by this dispatched worker compared the written node
with every field and theorem above. No other agent was started, as the dispatch
brief prohibits that; the maintainer supplies the independent delivery review.
The rereading found and repaired the originally missing K-flat normalization of
`LineData.factors` by adding `single_flat` and `factors_normalized`. The pure
sheaf evaluation is fixed by `evaluation_basis`, and `epsilon_computed` prevents
an arbitrary equivalence counit. The tower uses the recorded associator rather
than an existential isomorphism. The identity-ring clause retains arbitrary A_m
and has its explicit termwise formula; multiplication has a separate theorem.
I checked the order of the three arrows in the evaluation equation and of all
three arrows in the tower equation against the node. The aliases retain the
existing module categories, signed powers, and derived tensors; no hypotheses
exclude negative exponents, zero rings, nonflat scalar maps, or unbounded
complexes. No mathematical statement change or dependency module was made. The H2 repair
adds the definition-node ownership record below.


## New nodes

`def-pur-line-unbounded-tensor-data` records ten existing declarations in
`Sheaf.Algebra.Homology.LineUnboundedDerivedTensor`, with `existing: true`:
`Modules`, `dual`, `tensor`, `tensorAdditive`, `single`, `pureTensor`, `cancellation`,
`collapse`, `derived`, and `normalization`, in `SheafOfModules.LineUnbounded`.
Its source is Stacks 06YU's degree-zero derived tensor construction and blueprint
main-20261015, Tate-twist local freeness proof (3), final sentence; ordinary tensor
and dual are Stacks 03EK and 0B8Q. The eight statement dependencies own the site,
modules, derived category, tensor, internal Hom, K-flatness, flatness, and published
K-flat tensor/representative comparison. The normalization signature is verbatim
from the published source. No module or definition is added or duplicated.

Fresh LeanSearch query: “Canonical tensor with a degree zero sheaf on unbounded
complexes and its K-flat derived representative normalization”: 8 hits, about
ordinary flat module tensor, zero objects, derived zero and single-complex maps;
no exact interface. Loogle “SheafOfModules, DerivedCategory.Q”: 0 hits. Mathlib
grep “representativeIso|LineUnbounded|map₂HomologicalComplexFlipObjSingleIso” in
Algebra/Homology: 0 hits. DAG grep of LineUnbounded helper names: only the theorem
node `lem-pur-line-unbounded-derived-tensor`; blueprint_refs search “line unbounded
tensor”: 0 blueprint nodes. WeilConjectures search found generic degree-zero collapse
and its uses; Sheaf search located the ten concrete helpers in the published module.
Queries and results are recorded in the new node's mathlib_searches.

## Returned-delivery repair (H2)

Compared the saved packet with current main: the base has 11 statement dependencies
and no Lean record for the item. The saved packet had added the theorem as a twelfth
statement dependency. Replaced exactly that added entry with the new definition
node; retained every base statement dependency and the theorem in proof_deps. The
mathematical statement, proof, proof_deps and complete Lean module are unchanged
from returned head fe1cdfa179d3. Initial saved-packet dry run passed at 1521faaf71f;
that mechanical pass did not resolve the independent H2 return.

Fresh second reading by Q132: the new node matches all ten live definitions.
Modules is the same ringed-site category; dual is internal Hom into its unit;
tensor is right tensor with its inherited additive instance; single is degree
zero; pureTensor uses the sheafification unit; cancellation uses reassociation,
then evaluation, then right unitor; collapse is the canonical single-factor total
collapse; derived fixes the published derived right argument; normalization fixes
c using transport along h:F=derived, inverse representative comparison, and
Q(collapse), for every flat-term K-flat K. These definitions use no theorem choice.
P need not be a line: exactness and inverse equivalence stay in the theorem node.
P=0 and the tensor unit remain valid inputs; K may be unbounded, with the stated
conditional normalization for K-flat models with flat terms. Zero rings and the
distinct t+1/t site universes remain allowed. The saved main module's evaluation,
tower, scalar formulas and arbitrary identity-ring component were re-read and
retain the previously independently reviewed meaning. No new mathematical fault.

Repair validation: explicit scompile.py passed for the retained full module in
sandbox mode (55.7 s) and library mode (41.7 s), with no unexpected diagnostics.
The field self-check confirmed only lean/stmt_deps change on the item, exact
equality between the new node references and its eight dependencies, all ten
existing helper names, the verbatim normalization signature, and no duplicate node.
