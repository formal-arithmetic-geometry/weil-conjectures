## Worker report

The module `Sheaf.Topology.NormedScalarProfiniteCechExact` states
`Profinite.normedScalarProfiniteCech_exact`, with its proof postponed by `sorry`.
It also supplies the explicit equal-image tuple subtype `Profinite.scalarCechTuples`
and coordinate deletion `Profinite.scalarCechDelete` belonging to the same statement.
Their data are actual constructions, with no postponed definition or arbitrary map.
There are no new nodes, dependency repairs, or statement changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A prime ell is `(l : ℕ) [Fact l.Prime]`.
- The finite extension E/Q_ell is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- The extending nonarchimedean norm topology is passed explicitly to both cochain
  types as `(spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace`.
  This is the spectral absolute value of the recorded coefficient extension. Its
  completeness is a consequence of these coefficient data, not an extra hypothesis.
- F is E itself: both `ContinuousMap` types have codomain `E`, with no scalar
  replacement, completion, algebraic closure, or locally constant function type.
- The size convention is expressed by explicit independent universes `u v`;
  `S T : Profinite.{v}` ranges over the chosen universe of all compact Hausdorff
  totally disconnected spaces. Both coefficient and space universes are arbitrary.
- The continuous surjection q is `(q : C(T, S)) (hq : Function.Surjective q)`.
  No set-theoretic or continuous section is assumed.
- The fibre power T_S^r is `scalarCechTuples q r`, the subtype of `Fin r → T`
  satisfying `∀ i j, q (t i) = q (t j)`. Its inferred topology is exactly the
  subspace topology of the finite product. For r ≥ 1 this pairwise equality is
  equivalent to all images equalling the first image.
- Coordinate omission is `scalarCechDelete q r j`: its ith coordinate is
  `x.val (j.succAbove i)`. The subtype witness is the original equal-image proof
  applied to the two retained coordinates. This is the ordered deletion of j.
- C_k consists of all actual continuous maps on the (k+1)-fold fibre power, as in
  the continuous-map condensed-ring dependency. The pointwise addition and zero
  are the ordinary continuous-function operations, not sheaf cohomology objects.
- Each d_k is rendered by its defining pointwise formula
  `∑ j, (-1 : E) ^ j.val * f (scalarCechDelete ... j x)`.
  Multiplication by the field element (-1)^j equals the signed addition in the
  abelian group of the field. Thus `hf` is exactly d_k f = 0, checked on every
  tuple, and the conclusion is exactly d_(k-1) g = f, checked on every tuple.
  The finite signed sum is continuous because each coordinate deletion is a
  continuous map of subspaces of finite products and E is a topological field.
  No separate hypothesis on that continuity is added.
- Every positive integer degree k is written uniquely k = n+1 with `n : ℕ`.
  Hence f has domain `scalarCechTuples q (n+2)`, its cocycle equation is on
  `(n+3)`-tuples and sums over `Fin (n+3)`, and the resulting primitive has domain
  `(n+1)`-tuples. Its boundary sums over `Fin (n+2)` and equals f on `(n+2)`-tuples.
- The empty surjection is included: `Profinite` has empty objects and neither
  the theorem nor either helper requires `Nonempty`. On positive tuple lengths
  its cochain domains are empty, so the sole empty function is a primitive.

Dependency declarations read and used:

- `def-weil-size-convention` is a metatheoretic convention with null module and
  declaration; its record expressly requires universe-polymorphic binders.
- `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingPresheafOfUniverse`,
  `Profinite.continuousMapRingSheafOfUniverse` and
  `Profinite.continuousMapRingObjOfUniverse`: sections are the universe lift of
  `C(S,T)` with pointwise operations. The theorem uses the actual `ContinuousMap`
  groups specified by the node, prior to the harmless universe lift of sections.
  This recorded module is publicly imported; no alternate condensed ring is defined.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, publicly imports the coefficient
  constructions from `Sheaf.NumberTheory.Padics.CoefficientExtension`.
  In particular `Padic.coefficientExtensionAbsoluteValue` is the spectral absolute
  value. The normed-field topology used here is precisely that of the same norm.
- Already recorded proof modules are plain imports:
  `Sheaf.Topology.FiniteQuotientFiberProduct`
  (`Topology.finite_quotient_fiber_product`), and
  `Sheaf.NumberTheory.Padics.IntegersProfiniteTower`
  (`Padic.coefficientExtension_integers_profinite_tower`).
  The DVR module is already imported through the coefficient module.
  The proof-only DAG nodes `lem-sfb-finite-valued-cech-cocycle-descent` and
  `lem-weil-valued-dvr-finite-quotients` have no Lean declaration on the read base;
  there is no module to import for either. They are not statement prerequisites,
  and the theorem's docstring records their exact roles in the future proof.

Source and edge cases:

I read Bhatt–Scholze Lemma 4.3.9 and its proof on printed p. 33, especially discrete
coefficients, profinitely split sequential limits and sequential closed colimits.
The node explicitly identifies its stronger concrete wording as the agent-expanded
Cech consequence, and its eight-step argument is preserved in the theorem docstring.
The node is not changed. The ND review and merge in the repository are a stage-1
split with no `lean` record, not an already completed stage-2 statement. This explains
why the previous stale-assignment diagnosis does not prevent the present statement.

I checked degree one (`n=0`): the cocycle uses triples and its primitive is a function
on T, with the boundary g(t1)-g(t0). There is no negative index or unintended degree-zero
vanishing claim. For the identity surjection, all fibre powers are diagonal: in odd
positive degree the next alternating sum is the identity, so a cocycle is zero; in even
positive degree the preceding alternating sum is the identity, so a primitive exists.
These parities agree with the formula. Empty spaces, disconnected profinite sets,
non-metrizable profinite sets and coefficients in an arbitrarily large type universe
are not excluded. The helper at tuple length zero is harmless and unused by the
positive-degree assertion. No false-statement concern was found.

Searches for an existing statement or notation:

- `msearch.py`, LeanSearch, query: “Every continuous cocycle of positive degree on
  the Cech nerve of a surjection of profinite sets with coefficients in a finite
  extension of the p-adic rationals is a continuous coboundary”. Eight hits describe
  abstract hom-complex coboundaries, group cohomology, and the continuous group
  cohomology complex. None states this analytic profinite-surjection exactness.
- `msearch.py`, LeanFinder, query: “Continuous Cech cocycles on a surjection of
  profinite sets with values in a finite extension of the p-adic rationals are
  continuous coboundaries”. Eight hits concerned group cohomology, Hilbert 90,
  abstract hom-complex coboundaries and continuous group cohomology. None states
  this profinite-surjection exactness result or supplies these tuple objects.
- `msearch.py`, Loogle, query `cechComplexFunctor, ContinuousMap`: zero hits;
  the service reports unknown identifier `cechComplexFunctor`.
- `msearch.py`, grep, query
  `cechComplexFunctor|Cech.*(exact|acyclic)|ContinuousMap.*(Cech|cocycle)` in
  `CategoryTheory/Sites`: two textual hits in Mathlib's sheaf-cohomology Cech file.
  I read its construction: it builds the general categorical Cech complex and
  does not assert the continuous-field exactness theorem in this item.
- `rg` over project `lean/Sheaf` and `lean/WeilConjectures` for the item id and the
  proposed declaration names found no existing declaration. Concept searches for
  profinite/Cech/fibre/cochain combinations found general site Cech constructions,
  locally constant and other coefficients, and unrelated geometric Cech material;
  none gives the required analytic exactness assertion. These are not redefined.
- The node's recorded earlier Mathlib searches also find the categorical Cech
  constructor, Nobeling locally constant exactness and continuous group cohomology;
  these have different coefficients, objects or hypotheses.

Validation: the delivered module compiled cleanly using `scompile.py` in both
sandbox and library module modes (3.0 s and 2.9 s, respectively). No local build or
interactive compiler was used. The sole postponed theorem is the item's named
theorem; both helper definitions have complete data. Dry-run and delivery results
are recorded by the prescribed delivery wrapper.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
