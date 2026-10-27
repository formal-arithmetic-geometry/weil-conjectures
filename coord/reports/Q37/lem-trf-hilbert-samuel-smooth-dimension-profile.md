## Worker report

The module `Sheaf.AlgebraicGeometry.HilbertSamuelSmoothDimensionProfile` states the
whole dimension-profile node, with main declaration
`AlgebraicGeometry.HilbertSamuel.smooth_dimension_profile`. All declarations are in
`AlgebraicGeometry.HilbertSamuel`. Definitions contain actual data; all theorem
proofs are `sorry`. The item node is unchanged except for its `lean` record. No new DAG
nodes are needed. One statement-dependency interface is repaired below,
changing only that dependency node's `lean` record. The auxiliary definitions are precisely
the head, its two sequence operators, and its numerical presentation condition
introduced in this node; they reuse the existing geometric presentation framework.

Source reading: I read ILO VIII 2.3.13, printed p.94, in the local PDF using
`pdftotext -layout`. It points to the arbitrary-smooth synchronization correction
in BMT section 6.3. I also opened the primary source
https://arxiv.org/html/0905.3580, sections 6.1--6.3 and Remark 6.2, and the PDF
https://arxiv.org/pdf/0905.3580. The local ILO source does not itself supply the
explicit normalized finite-difference formulas; those are the node's stated
normalization and its proof steps 1--6. The local-presentations source and Lean
interface qualify their finite maximal-order assertion on a minimal envelope.
The present node permits choosing a larger smooth ambient at regular points.

Hypothesis and clause correspondence:

- Reduced scheme of finite type over Q: `{X : Scheme.{u}}`,
  `p : X ⟶ Spec (.of (ULift.{u} ℚ))`, `[IsReduced X]`,
  `[LocallyOfFiniteType p]`, and `[QuasiCompact p]`. The explicit structure map
  follows the dependency's interface and makes both the extended function and
  smooth pullback unambiguous. `ULift` realizes Q in the same scheme universe;
  no site/coefficient universe is identified and no universe is left implicit.
- Raw sequence `h_x`: the existing `localFunction X x`, from
  `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`. It is the natural number
  extraction of the recorded `Module.length` of the maximal-ideal power
  quotient, then embedded into integers wherever differences are taken.
  `dimension_profile_finite` explicitly asserts finite length for every n,
  including n = 0, so no infinite length is silently interpreted as zero.
- Local component dimensions: `localComponentDimensions X x` is the set of
  `ringKrullDim ((X.presheaf.stalk x) ⧸ P)` for minimal primes P. This is the
  component-dimension set of the local spectrum, using the existing minimal
  prime/component correspondence, without choosing arbitrary components.
- Minimum `q_x`: `minimumComponentDimension X x` is `sInf` of that set followed
  by the two numeric extractions. `dimension_profile_finite` asserts that the
  set is finite and nonempty, every member is an actual natural dimension,
  and the extracted minimum equals its `sInf` in `WithBot ℕ∞`.
- Count `c_x`: `componentDimensionCount X x` is the `ncard` of the SET OF
  DIMENSIONS. Two distinct components of the same dimension contribute one,
  rather than two. Finiteness above justifies the cardinal extraction.
- Integer summation and differences: `integerSummation` sums the inclusive
  range `Finset.range (n + 1)`; `difference` has cases `0 => f 0` and
  `n + 1 => f (n + 1) - f n`. The integer codomain preserves negative entries.
  The existing natural `summation` remains the one used by H and line tests.
- Normalized ordered head: `DimensionHead = Lex (ℕ × Lex (ℕ → ℤ))` uses
  Mathlib's lexicographic product and sequence orders. `normalizedHead X x`
  is exactly `(c_x, difference^[q_x] h_x)`. `integer_operators` states the
  inverse identities and strict-order preservation and reflection of every
  iterate; its proof docstring supplies the telescoping and first-difference
  argument of node step 1.
- Smooth morphism and arbitrary `y ↦ x`: `smooth_dimension_profile` binds
  `f : Y ⟶ X`, `[Smooth f]`, and `y : Y`; x is `f y`. It imposes no
  quasi-compactness on Y or f, no constant relative dimension, and no closed
  point hypothesis. The fibre local ring is literally
  `(f.fiber (f y)).presheaf.stalk (f.asFiber y)`. It is asserted regular,
  with a finite natural dimension witness s.
- Smooth raw-function formula: `localFunction Y y =
  (summation^[s]) (localFunction X (f y))`. The same conjunction translates
  `localComponentDimensions` by s, increases its minimum by s, preserves
  `componentDimensionCount`, and equates the two `normalizedHead`s.
- Regular head and strict inequality: `regularHead = (1, (1,1,...))` with
  integer sequence entries; `normalizedHead_regular` gives equality iff
  `IsRegularLocalRing (X.presheaf.stalk x)` and gives strict inequality for
  every nonregular point. This uses the regular-local-ring part of the
  recorded regular-scheme dependency, without incorrectly requiring X
  itself to be regular.
- Fixed dimension bound D: all numerical global assertions bind `D : ℕ`
  and `hD : topologicalKrullDim X ≤ (D : WithBot ℕ∞)`. Summation iterates
  are indexed by naturals; for nonempty X an integer D bounding its
  dimension is automatically nonnegative. Empty X has no head values.
- Applying `Λ^D` to the second entry: `sumHead D` does exactly this, and
  `modifiedHead D X x := sumHead D (normalizedHead X x)`.
  `modifiedHead_eq` identifies it with `(c_x, Λ^(D-q_x) h_x)`; no initial
  entries are removed. The subtraction is natural subtraction under the
  asserted dimension bound.
- Upper semicontinuity and finite image: `modifiedHead_properties` asserts
  `(Set.range (modifiedHead D X)).Finite` and closedness of every upper
  level set `{x | a ≤ modifiedHead D X x}` for the actual lexicographic
  order. These are global finite-image and upper-semicontinuity claims,
  not just closed-point or local-finite-image variants.
- Extended H and irreducible level components: the same theorem quantifies
  over every `C : Set X` and gives an iff between C being the subtype-image
  of an irreducible component of some head level and of some `function p`
  level. `function p` is the existing `Λ^(trdeg_Q κ(x)) h_x`. The subtype
  topology states the actual level-set component assertion in both
  directions, rather than only an equality of closures or stratification
  cardinalities.
- Local presentations and SAME TEST SEQUENCES: `local_modified_presentations`
  gives an actual pointed étale neighborhood `g : S.X ⟶ X`, `g a = x`,
  over the specified rational base, in a smooth ambient `S.Z`. It returns
  the SAME `M : Marked S` with both `Presents M` for H and
  `ModifiedPresents D (modifiedHead D X x) M` for the head, and makes this
  head maximal on that neighborhood. This provides the local maximum
  hypothesis used by the subsequent removal theorem.
- `ModifiedPresentsThrough` is a depth recursion reusing `Step`,
  `Step.Admissible`, and `Step.Transforms`. At EVERY successor it requires
  existence of transforms and quantifies over EVERY transform at EVERY
  permitted test step. Thus the conclusion is not merely equality of
  starting cosupports. The retaining-head value is fixed at line tests
  because A, and hence `sumHead D A`, is smooth invariant; the existing
  geometric `Step` still sums its H level at a line test. D need not bound
  dimensions of these auxiliary line products to define `sumHead D A`.
- Marked ideal contents: the dependency's `Marked` supplies a smooth closed
  N in Z, a genuinely coherent ideal, and positive marking. `order`,
  `Marked.cosupport`, controlled blowup transformation, ordinary pullback
  at the two auxiliary operations, and ordered exceptional divisors are
  used unchanged. The existence theorem returns `FullMaximalOrder M` at
  every point, as requested by this node. At singular points use the
  dependency's full-envelope result. At a regular point choose a larger
  smooth ambient, namely the product of a smooth neighborhood with a line,
  embed that neighborhood as t = 0 and use ideal (t), marking one. This
  has order exactly one throughout cosupport. The zero ideal on a minimal
  codimension-zero regular germ itself is never asserted to have finite
  order. The full-envelope conclusion is an existential choice of ambient,
  not an extra condition on the input scheme.
- Presentation equivalence: `modified_presentation_equivalence` asserts
  that the existing all-finite-test `Equivalent M P` preserves the modified
  presentation predicate, using the same transform quantifiers.
- Smooth head-constant admissibility: `center_locallyConstant_iff` identifies
  `LocallyConstantCenter S C` with the EXACT same smooth center and
  factorization, replacing only locally constant H by locally constant
  `modifiedHead`. Thus the next theorem's dependency predicate imposes
  exactly the head-constant center condition; it does not silently demand
  a stronger kind of permissible center.
- Blowup nonincrease: `modifiedHead_nonincrease` compares every point of
  the dependency's actual `C.strictTransform S.i` to its image by the
  canonical `strictTransformToSource`. No arbitrary comparison map is
  supplied. The theorem is independent of a choice of presentation.
- No infinite strict drops from fixed initial X:
  `modifiedHead_no_infinite_drops` fixes S and D and considers values
  attained on schemes reachable from S by the reflexive transitive closure
  of the existing genuine `BlowupTransition`. It excludes an infinite
  strictly decreasing sequence of such values, including subsequences
  separated by unchanged values in an infinite history. Zero blowups are
  included. It makes no false well-foundedness claim about all integer
  sequences or heads from unrelated initial schemes. The dependency
  interface repair supplies the corresponding precise descending-chain
  statement for H.
- Resolving a presentation removes that head:
  `modified_presentation_empty_maximum` quantifies over an arbitrary finite
  history with initial marked presentation, actual admissible blowup
  steps and controlled transforms, ending with empty cosupport. It gives
  strict inequality for every final point. Maximality holds on the local
  neighborhoods supplied by `local_modified_presentations`; covering a
  constant stratum by such neighborhoods gives the stated removal claim.
- Ordered exceptional histories:
  `modified_presentation_history_comparison` uses the existing
  `CommonComparison S T x y e earlierS earlierT`, retaining the ordered
  previous-center ideals via its canonical cartesian comparisons. It
  returns equivalent marked pullbacks that still present the modified
  level. The finite-test and empty-maximum statements use `Step`, whose
  boundary is an ordered list, with both auxiliary operation types and
  their exact existing boundary transformations. Previous centers are
  history data rather than additions to the new test boundary.
- Finite disjoint unions: no theorem assumes connectedness, irreducibility,
  equidimensionality, or nonemptiness. Every finite disjoint union of the
  input finite-type rational schemes again satisfies the hypotheses with
  one common D. Local rings at its summand points are unchanged; the
  smooth theorem in particular applies to its open summand inclusions.
  The history theorem allows operations on different summands in any
  order and the global theorem asserts finite image on the whole union.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`,
  sectionwise reduced with the existing equivalence to stalkwise reduced.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  no substitution of formal smoothness of a local ring.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`
  and its public ring and stalk regularity imports. Regular points use
  `IsRegularLocalRing` from `Mathlib.RingTheory.RegularLocalRing.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact`; both finite-type clauses are kept.
- `Mathlib.RingTheory.Length`: `Module.length`; the actual raw-function
  declaration was read in `HilbertSamuelInvariant.lean`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, including its
  `WithBot ℕ∞` codomain, not an a priori natural dimension.
- `Sheaf.AlgebraicGeometry.HilbertSamuelReachableLevels` publicly imports
  `Sheaf.AlgebraicGeometry.HilbertSamuelLocalPresentations` and adds
  `function_no_infinite_reachable_drops`. I read every
  recorded declaration, its full signature and proof docstring. The
  numerical, local-presentation, full-maximal-order, history-comparison,
  and empty-maximum interfaces are reused. Its dependency modules
  `HilbertSamuelInvariant.lean` and `HilbertSamuelPresentation.lean` were
  read in full: `localFunction`, `summation`, `function`, `Embedded`,
  `Marked`, `Step`, `Presents`, `Equivalent`, `CommonComparison`,
  `LocallyConstantCenter`, `BlowupTransition`, and their transforms are
  the shared definitions, not private copies.

The available proof-dependency modules are imported non-publicly, including
`Algebra.smooth_local_tangent_cone_extension`, the regular-local generators
and graded-polynomial theorems, both dimension/transcendence-degree theorems,
the regular-local domain theorem, Mathlib length additivity (already public
through the numerical dependency), Krull intersection, minimal-prime/component
correspondence, and Noetherian component finiteness. The DAG's
`lem-trf-hilbert-samuel-equality-component-rigidity` has no recorded Lean
module in the read tree, so no fictional import is made for it; its use in
the eventual proof is explicitly retained in the relevant proof docstring.
All source signatures needed to state this node are available.

Edge cases checked before writing and again against the final signatures:

1. Empty scheme and empty finite union: statements quantified over points
   are vacuous; the image is empty and no attained-value sequence exists.
2. A field stalk: q = 0, c = 1, h = constant one, so the head is exactly
   `regularHead`. No positive-dimensional or singular-point hypothesis
   excludes this case.
3. Several components of the same dimension: c remains one. For the nodal
   ring Q[x,y]/(xy) at the origin, q = 1, h(n) = 2n+1 and the difference
   sequence is (1,2,2,...), strictly above the regular head. This also checks
   that c does not count the two minimal primes.
4. A plane and a transverse line, Q[x,y,z]/(xy,xz) at the origin: local
   dimension set {1,2}, q = 1, c = 2. Its h(n) is binomial(n+2,2)+n.
   Both the higher-dimensional component and the smaller one are retained.
5. Smooth line product at a closed fibre point: s = 1, h is summed once,
   the dimension set is translated once, and the normalized head is fixed.
   At the generic point of that line fibre, s = 0 despite relative dimension
   one: h and the dimension profile are unchanged, while residue-field
   transcendence degree increases. `f.asFiber y` records precisely this
   distinction.
6. Summation/difference at index zero: inclusive summation and `difference 0`
   are inverse without dropping any initial entries; q = D and D = 0 are
   both allowed. Arbitrary negative integer entries remain valid.
7. A regular codimension-zero germ: the zero ideal has infinite order.
   Its maximal-order presentation in the theorem uses a nonminimal
   ambient with one extra normal coordinate and ideal (t), marking one.
   In a blowup chart meeting the strict transform its controlled transform
   is (t/e); in a chart missing the strict transform the cosupport is
   empty. This treats regular points without claiming finite order of zero.
   I also read the existing DAG node
   `lem-trf-marked-ideal-transverse-suspension`, whose r >= 1 clause
   explicitly supplies this test-equivalence argument, including I = 0.
8. Non-quasi-compact smooth source and varying relative dimension: there is
   no extra source quasi-compactness or relative-dimension binder. The
   fibre-local dimension is computed separately at every y.
9. Ordered history of length zero and zero blowups: `Fin (n+1)` and
   `Fin.last n` retain the starting stage when n = 0. The empty-maximum
   theorem then simply says an already empty maximum cosupport has no
   points at that level.

Searches actually run:

- `msearch.py ... leanfinder` with query
  `Hilbert Samuel function finite differences smooth invariant local component dimensions resolution marked ideal`:
  eight hits on smooth local algebra and dimension inequalities, none on
  the normalized dimension head or its statement.
- `msearch.py ... loogle` with query `Module.length, ringKrullDim, List.Lex`:
  zero hits.
- `msearch.py ... leansearch` with query
  `Hilbert Samuel smooth invariant normalized finite differences dimension irreducible components`:
  eight smooth-algebra hits, none on this head.
- `msearch.py ... grep` with query
  `HilbertSamuel|hilbertSamuel|hilbert.s amuel|dimensionProfile`, subdirectory
  `RingTheory`: zero hits. The broad repository rg searches separately
  found the already landed HilbertSamuel numerical and presentation modules
  and the growth-polynomial module; those were reused where applicable.
- `rg -n 'HilbertSamuel|hilbertSamuel|hilbert.s amuel|dimensionProfile|normalizedHead'`
  in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing declaration of this node;
  the existing raw function and presentation declarations are listed above.
- Exact node-id rg in `lean/WeilConjectures`: no hits.
- Searches of the proposed declaration names and relevant lexicographic
  APIs found Mathlib's `Pi.Lex`, `Lex.linearOrder`, and product Lex
  instances. These are reused in `DimensionHead`, not redefined.

There is no statement correction and no unresolved STATEMENT-DISPUTED flag.
The node's maximal-order existential is retained also at regular points by
allowing a nonminimal smooth ambient. No finite maximal-order claim is made
for a regular zero ideal itself.

Validation: the first complete module compiled cleanly using the prescribed
server `scompile.py`. After adding the explicit ordered-history comparison, local maximum
guarantee, and maximal-order choice of ambient at regular points, the final
file was recompiled using the same wrapper. The dry run also checks the
module on the server and runs the maintainer preflight before delivery. The metadata signature is taken verbatim from the source. All
variables and the universe u are explicitly bound with `autoImplicit false`.
Both node copies change only `lean`. The complete two-module packet is
compiled in dependency order with `scompile.py`, and then checked by the
required `deliver2.py --no-push` dry run.


## Dependency modules

`lem-trf-hilbert-samuel-local-presentations` is repaired by
`Sheaf.AlgebraicGeometry.HilbertSamuelReachableLevels`. Its original
`function_no_infinite_drops` excluded strict decrease at every consecutive
single-blowup stage. That statement alone does not rule out an infinite
strictly decreasing subsequence whose intervening blowups leave a value
unchanged. The item's proof step 14 passes to such a subsequence after
stabilizing the count and minimum dimension, so the recorded interface was
too weak for the node's actual descending-chain clause.

The new main declaration
`AlgebraicGeometry.HilbertSamuel.function_no_infinite_reachable_drops`
uses `Relation.ReflTransGen BlowupTransition S T`: every chosen H value is
attained on an actual scheme after a finite admissible history from the same
initial S. It asserts that these values have no infinite strict descending
chain. Thus one may pass to subsequences, histories of arbitrary finite
length, or zero blowups. The source is the dependency node's proof steps 3
and 9: the diagram descending-chain condition holds for all possible values
in a fixed ambient variable bound, and blowup charts preserve that bound.
The new proof docstring gives that argument step by step. All its numerical
hypotheses are the original reduced, finite-type rational-scheme hypotheses;
there is no stronger condition on centers or arbitrary transition map.

This module publicly imports the original `HilbertSamuelLocalPresentations`
module, so it preserves every original definition and theorem, including
`local_presentations`, both existing presentation-comparison declarations,
the singular-point qualification, and the original consecutive-stage theorem.
There are no duplicate declarations and no weakening or replacement of the
geometric framework. The dependency record lists all its previously recorded
declarations plus the new descending-chain theorem and explains the repair
in `lean.note`. Its statement, proof, dependency fields, and all other fields
are unchanged. The item imports the newly recorded module directly.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
