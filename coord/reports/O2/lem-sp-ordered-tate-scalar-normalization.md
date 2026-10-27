## Worker report

The item is stated in `Sheaf.Paper.OrderedTateScalarNormalization` as
`AlgebraicGeometry.Etale.ordered_tate_scalar_normalization`, with proof `sorry`.
The module constructs the canonical direct comparison before stating its equality
with the published ordered affine comparison. All data are actual composites of
published maps. The ordinary Tate balancing map is selected from the published
unique-existence theorem, which fixes it on every generator, tensor power, and unit;
no arbitrary isomorphism is selected from mere existence.
The natural-language statement and accepted proof split are unchanged.

Source read: main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, especially its final canonical
isomorphism and iterated projective-line integration. The seven proof steps of
this DAG item are reproduced in the theorem docstring (the successor calculation
and final induction are described separately there).

Hypothesis and clause correspondence:

* The prime ell is `(ell : ℕ) [Fact ell.Prime]`; positive characteristic is
  `(p : ℕ) (_hp : 0 < p) (k : Type u) [Field k] [CharP k p]`;
  `_hEll : p ≠ ell` is precisely the excluded characteristic.
* The separated finite-type k-base is `(S : Scheme.{u})` with `S.Over (Spec (.of k))`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure map.
  Finite type is locally finite type plus quasi-compactness. All coordinate and
  projective stages and all maps are the existing canonical k-base constructions;
  no arbitrary auxiliary scheme or morphism is quantified over.
* The two finite commutative rings and the unital map are
  `(A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]`
  and `(φ : A →+* B)`. The annihilation hypotheses are exactly
  `hA : ((ell ^ n : ℕ) : A) = 0` and the analogous `hB`.
  Positivity of N is supplied by `pow_pos (Fact.out : ell.Prime).pos n`.
* The ordinary small-etale categories are `Etale.DerivedCategoryModule A S`, the
  published derived categories of `Sheaf S.smallEtaleTopology (ModuleCat A)`.
  The coefficient universe is u+1, as in the six-functor convention; finite rings
  in smaller universes can be lifted without changing their category.
* `K : DerivedCategoryModule A S` with
  `_hK : ProEtale.AdjunctionTransfer.etaleProperty A S K` is exactly bounded
  constructible cohomology intersected with the published finite-Tor predicate.
  Reading that predicate shows the interval is chosen before quantifying over
  every degree-zero module sheaf, as the node requires. It is not a condition
  restricted to constructible or finite module sheaves.
* `scalarExtension φ T` is the already published ordinary derived extension of
  coefficients; it has no flatness premise. `Scheme.finiteEtaleTateSheaf A N T hA d`
  is the recorded finite etale Tate power (unit at zero, ordered tensor powers
  at nonnegative degrees). The degree-zero derived object uses the existing
  `DerivedCategory.singleFunctor`.
* `affineTraceTower S d` and `affineTraceProjection S d` are exactly X_d and p_d,
  with literal identity at zero and the affine-line recursion at a successor.
  `affineTraceRight A N hA S d` is the ordered G-calligraphic tower, built from
  `affineTraceLineRight`, hence from the published standard chart and projective
  projection and their shifted Tate line.
* The h_r and a_r comparisons and their paste are precisely
  `ProEtale.reductionEtaleLineScalarIso`, whose definition first uses inverse
  `scalarPullbackIso` for the chart, then pulls back
  `reductionEtaleP1ScalarIso`. The latter uses the scalar tensorator,
  inverse `scalarPullbackIso` for q_r, and the generator-normalized shifted Tate
  comparison. `ProEtale.reductionEtaleAffineScalarIso` is A_d: its zero is
  `Iso.refl`; its successor is the line comparison followed by W_B of its
  preceding comparison. The definitions, not the downstream exceptional
  coefficient theorem, are used.
* `orderedAffineRight A N hA S d` renders G_d. At positive dimension its displayed
  formula is exactly p_d pullback, tensor with the single d-th Tate sheaf, then
  shift by `2 * (d : ℤ)`; at zero it is `𝟭 _`, implementing the stipulated unit,
  identity-pullback and zero-shift normalization.
* `orderedAffineRightIso` is I_d, exposing the actual existing ordered recursive
  normal form used by the trace construction. Its successor uses pullback
  composition, Tate pullback, ordered products, associativity and even shift
  addition. Its zero branch is `Iso.refl _`.
* `orderedTateProductIso` exposes the same degree-zero derived Tate multiplication.
  `orderedTateScalarIso` builds the coefficient map for an unshifted Tate power
  from the published scalar/single adjunct and the unique ordinary balancing
  family in `finite_tate_scalar_source_normalization`. Its uniqueness fixes the
  generator formula, tensor powers, and scalar unit at zero. The existing flatness
  proof makes the actual adjunct invertible. Root factors are never permuted.
* `orderedAffineDirectScalarIso` is a_d. For a positive dimension it first
  extracts the total even shift with `scalarShiftIso`, splits scalar extension
  across the direct tensor with `ExceptionalCoefficients.tensorIso`, applies
  the direct scalar/p_d pullback comparison and the just constructed Tate-power
  comparison, then retains the one accumulated shift. This construction does
  not mention A_d or I_d; the desired equation is not made definitional by
  conjugating A_d with I_d. Its zero case is `Iso.refl _`.
* Lean's `f ≫ g` means g after f. The left side is exactly A_d(K) followed by
  I_(d,B,T K); the right side is T(I_(d,A,K)) followed by a_(d,K). Both are actual
  morphisms in the ambient ordinary etale derived category, not assertions of
  existence of an isomorphism or equality of object isomorphism classes.
* The conclusion starts `∃ hS : IsUnit ...`, because the existing comparison APIs
  accept that proof. This is a proof forced by the field/characteristic and
  k-structure hypotheses: ell is nonzero in k, its power is a unit, and the
  structure morphism transports the unit to Γ(S, top). It adds no assumption or
  choice of data; proof irrelevance makes all maps independent of its witness.
  It covers empty S as well, whose global ring is the zero ring.

Dependency declarations read and used:

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the
  standing finite-type/separated k-setting, rendered explicitly by binders.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and its ambient homology convention.
* `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`:
  `AlgebraicGeometry.ProEtale.AdjunctionTransfer.etaleProperty`; its full definition
  was checked against bounded constructibility and the degree-zero Tor test.
* `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: the universal derived
  scalar-extension/cochain-model declarations, retained as the general input.
  The actual site scalar functor and its representative normalization are the
  already published `Etale.scalarExtension` and `ExceptionalCoefficients.tensorIso`
  / `unitIso`, publicly provided by the existing coefficient-map modules.
* `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `Scheme.finite_etale_torsion_twist_line` (flatness of the actual finite Tate lines).
* `Sheaf.AlgebraicGeometry.AffineTraceTower`:
  `affineTraceTower`, `affineTraceProjection`, `affineTraceInvertible`, and the
  projective/base-change invertibility constructions.
* `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  general canonical representative-normalized tensor comparison input.
* `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`:
  `Etale.exists_affineSpaceTopTrace`; its existing live record is preserved.
  The new definition node exposes the exact recursive construction used in its proof.
* `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.finiteEtaleTwistPullbackData` and its root-normalized fields `c` and `p`.
  Their positive recursion, pullback-composition, associativity, zero and unit
  laws were read, not just their signatures.

All stated proof dependencies are imported, including KFlatResolutionIndependentCoefficients,
KFlatRingedToposPullback, KFlatTotalTensorModel, TensorBilinearUniversal,
RingedDerivedMonoidalComparisons, CochainPullbackTensorCoherence,
Mathlib.Algebra.Homology.BifunctorShift (the node's Mathlib match), and
CochainPullbackTensorShift. The direct comparison also reuses the published
FiniteSmoothPurity.scalarShiftIso and ReductionExceptional's real canonical
root and ordered scalar maps, with no copy of those notions.

Edge cases checked by reading the constructions and their defining formulas:
d=0 gives identity for I, A, and a; d=1 uses one ordered root and shift two;
d=2 appends the second root and accumulates shift four, without exchanging
factors. Arbitrary n includes n=0 (N=1 forces zero coefficient rings). Zero A or B
and the empty scheme are retained. Nonflat maps, for example Z/ell² → Z/ell,
are retained because no flatness is assumed on the scalar extension. Even shifts
have the same signed tensor comparison on both paths. No primitive root, scalar
orientation, bounded resolution of B, or arbitrary normal-form witness is chosen.

Searches actually run via msearch.py for this item:

* LeanFinder: "Ordered Tate right comparisons in an affine coordinate tower agree
  with canonical derived scalar extension"; eight unrelated Galois/elliptic/base
  extension hits, no match.
* Loogle: `CategoryTheory.MonoidalCategory.associator_naturality`; one match, the
  generic associator naturality lemma, which does not state this specified
  ordinary-etale geometric map comparison.
* grep: `orderedTate|affineTraceRight.*calar|scalar.*ormalForm`; one unrelated
  Mathlib PID Smith-normal-form hit, no match.
* LeanSearch: "Canonical derived scalar extension commutes with ordered Tate
  powers and affine pullback normal forms"; eight ordinary algebra extension
  hits, no match.
* rg of lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `orderedTate|orderedAffine(Right|Direct)|affineTraceRight.*calar|scalar.*ormalForm`:
  the existing ReductionExceptional and ChartCounitScalarTransport define the
  iterated comparison but do not compare it with the specified direct normal
  form; EtaleProEtaleScalarCounitTransposes treats a different site/counit map.
* grep by this exact node id in lean/WeilConjectures: no hits. Earlier logged
  searches in searches.jsonl reach the same no-exact-match result. No search
  service failure is recorded as a mathematical no-match.

The landed node `lem-pur-finite-tate-scalar-source-normalization` is added to
stmt_deps and its module is publicly imported. Its full statement, signature,
normalization predicates, scalar/single map and source proof were read. It supplies
the already existing canonical scalar map and fixes it uniquely, including its
zero and tensor normalizations. This replaces redundant recursive reconstruction
of the same map and reduces kernel checking cost. That scalar map introduces no additional definition node; the ordered affine
normal form itself is owned by the new node described below.
There is no statement dispute or source correction.

## New nodes

`def-sp-ordered-affine-right-normal-form` owns `orderedAffineRight`,
`orderedAffineRightIso`, and `orderedTateProductIso` in
`Sheaf.Paper.OrderedAffineTraceNormalForm`. It uses exactly
`def-amb-affine-trace-tower`, `lem-asd-finite-etale-twist-line`, and
`lem-asd-etale-finite-twist-pullback` as statement dependencies. The item cites it.
The source is the Charts paragraph of the current blueprint's
sk-lem-sp-reduction-exceptional proof, specifically its ordered
p_d pullback, d-th Tate power and accumulated shift. The node specifies the
construction used in that comparison, rather than a new assertion about the trace.

The Lean binders give a finite commutative A, positive N annihilating A, an
arbitrary scheme S and invertibility on S. `orderedAffineRight` implements G_d,
with literal identity at zero. `orderedAffineRightIso` implements I_d using
`towerENormalForm` for positive d and literal identity at zero.
`orderedTateProductIso` is the existing `singleProductGeneral` specialized to the
flat finite Tate sheaves and canonical `twistSheafProduct`. Its binders allow
every d >= 0 and every scheme T on which N is invertible. All three definitions
have real construction bodies. Their signatures and bodies are unchanged from
the reviewed packet; their blueprint ownership tags now name this definition node.

Fresh searches are recorded verbatim in the node and searches.jsonl:
LeanSearch for "Ordered affine coordinate tower right adjoint normal form as
pullback tensor Tate power and even shift" returned eight generic shift,
adjunction and algebraic scalar results; LeanFinder for "Canonical ordered
normal form of iterated affine-line Tate pullback functors and degree-zero Tate
multiplication" returned eight affine-scheme constructions; neither states this
specified normal form. Mathlib grep for
`orderedAffineRight|orderedTateProductIso|towerENormalForm|singleProductGeneral`
returned no hits. Project rg found only the generic private `towerENormalForm`
and `singleProductGeneral`, which this module reuses through `import all`, and
existing users of the iterated scalar map. No DAG node owns this specified
construction. Blueprint search "ordered affine" returned three different purity
statements (zero-section purity, orientation charts, affine composition); "Tate
right" returned zero. None is the same definition, hence `same_as: []`.
The blueprint ancestor command returned `det-sp-reduction-exceptional`.
Edge cases are the same zero dimension, zero ring, N=1 and empty schemes checked
above; there is no field, Noetherian, or constructibility restriction on this node.

## Repair of returned head ddc80fd8d2ce

H13 / repeated F1: restored the complete sandbox copy of
`lem-amb-affine-space-top-trace.json` byte-identical to the live repository.
Its module remains `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`, primary theorem
`AlgebraicGeometry.Etale.exists_affineSpaceTopTrace`, recorded by Q24. The delivery
therefore makes no change to that node or its existing consumers. The new
normal-form definition node owns the three helper declarations instead. No
trace theorem is appended to that new node's declarations. No dependency module
repair is requested or delivered. The item retains its accepted statement,
proof, proof dependencies, and theorem signature. Its statement dependencies
add the new node and retain the genuine finite Tate scalar source normalization
node accepted by the maintainer.

The advisory about `det-sp-reduction-exceptional` concerns the owner of the
already published A_d construction. This packet uses its existing definition
`reductionEtaleAffineScalarIso`, not the downstream exceptional isomorphism
theorem; it does not rebind or duplicate that owner.

## Second reading by O2

This repair's self-check re-read the two modules and their node signatures.
The item still quantifies over prime ell, positive characteristic p != ell,
a field k, arbitrary finite coefficient rings with a unital map, all n >= 0,
a separated finite-type k-base, all d >= 0, and bounded constructible finite-Tor
K. The witness hS is derived from these hypotheses, not a new assumption.
The conclusion remains the equality of the specified A_d followed by I_B,
and scalar extension of I_A followed by the independent direct comparison a_d.
The new definition node's three composites match their Lean bodies clause by
clause as detailed above. The defect found was exclusively the old trace record
owning a different notion; the restored record and new owner correct it.
The independent mathematical reading remains the maintainer's review, as this
worker was instructed not to start other agents.

## Validation

scompile.py compiled both final modules separately in dependency order against
the live server library, with no errors or non-sorry warnings. The new definition
module library compile took 29.0 seconds and the item library compile took 49.1 seconds.
The delivery wrapper additionally checks the same packet and server preflight. Every variable and universe is explicitly bound;
autoImplicit and relaxedAutoImplicit are disabled for the item. All delivered Lean
lines are at most 100 characters. The only newly postponed theorem is the item's
named theorem with its complete source proof docstring.

The revised preflight required `import_flags` on the new definition node; the
empty list is supplied. Its advisory about the finite Tate scalar source theorem
is the genuine theorem dependency explicitly accepted in the maintainer return.
