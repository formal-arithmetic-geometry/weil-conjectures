## Worker report

Item: lem-sfb-bicosimplicial-shuffle-totalization. N7, stage 2, 2026-10-21 UTC.
Module: Sheaf.Algebra.Homology.BicosimplicialShuffleTotalization.
Main declaration: AlgebraicTopology.BicosimplicialShuffle.exists_shuffle.

This is the stage-2 statement of the reviewed stage-1 split. The NY report and
ledger entry concern the natural-language split only; the live node has no Lean
record. They do not supply this stage-2 theorem and were not changed. The sandbox
was otherwise empty. No stage-1 proof, statement, dependency, source or review
field is changed. The one node change is its lean record.

The theorem has one postponed proof. All twelve helper definitions have real
data and belong to the same canonical shuffle and its totalizations, explicitly
introduced in this node. They are listed in lean.declarations; no independent
missing notion or new DAG node is needed. There is no choice from an unproved
existence theorem and no data-valued sorry.

Clause-by-clause reading:

- The arbitrary abelian category is {C : Type u} [Category.{v} C] [Abelian C].
  Object and morphism universes remain independent. HasDerivedCategory.{w} C
  chooses the morphism-size convention of the recorded ordinary derived-category
  dependency; it makes no extra mathematical hypothesis on C.
- Δ is Mathlib's SimplexCategory, whose objects are the nonempty finite ordinals
  and morphisms are monotone maps. X has the literal type
  SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ. Both cosimplicial
  structures and all internal chain-map identities are encoded by this functor.
- diagonalBicomplex is the alternating-coface complex of the diagonal restriction
  of X. Its total diagonalTotal is D(X): the summands are X^(n,n,r), n+r=m,
  and the existing total differential is δ_diag + (-1)^n d_r.
- tripleComplex applies alternatingCofaceMapComplex first in the second
  cosimplicial direction, then in the first. Its value is a complex of complexes
  of internal complexes. cosimplicialTotal totals the first two directions in
  CochainComplex C ℕ, and successiveTotal totals their sum with the internal
  direction. Thus T has terms X^(a,b,r), a+b+r=m, and differential
  δ₁ + (-1)^a δ₂ + (-1)^(a+b) d_r. All these are Mathlib total constructions,
  with the published hasTotal_up_nat instance: no infinite sum in C is assumed.
- diagonalInclusion and successiveInclusion are the canonical total coprojections.
  The latter uses the inner coprojection, evaluated at r, then the outer one.
  They make the theorem's component equation independent of arbitrary choices
  of coordinates or an unspecified derived comparison map.
- shuffleSurjection n μ is the actual monotone map whose value on i is the
  cardinality of μ.filter (j.val < i.val). Its target is the ordinal μ.card.
  Replacing μ by its complement gives exactly the other surjection. The Fin
  bound follows from card_filter_le, and the monotonicity field is the monotone
  inclusion of these filters. These are construction fields, not extra theorems.
- shuffleSign n μ is (-1) to the number of inversions (i,j) in μ × μᶜ with j<i.
  This equals the sign of the permutation whose list is increasing μ followed
  by increasing μᶜ: neither list has inversions internally. shuffleTerm composes
  the actual X-map on these two surjections with the specified target inclusion,
  with this sign. card_add_card_compl identifies the target total degree with n+r.
- The first conjunct of exists_shuffle fixes S on every source summand to the
  sum of shuffleTerm over all μ : Finset (Fin n). Each subset represents exactly
  one ordered partition (μ,μᶜ); grouping this finite sum by μ.card=a gives exactly
  S_(a,b) in the node. Equality into the coproduct specifies every target component,
  including zero components when the internal degree changes. Coproduct universality
  uniquely determines every degree map, so this is the prescribed canonical S,
  not a free comparison map supplied as a hypothesis.
- The next conjunct says diagonalMap f ≫ S Y = S X ≫ successiveMap f for every
  strict natural chain map f:X→Y. Those maps use only the existing alternating
  coface functor and total.map; this is precisely naturality of the cochain map.
- For every X the third conjunct supplies e : HomotopyEquiv D(X) T(X) with
  e.hom = S X. The homotopy inverse is therefore an inverse of this specified
  shuffle, not merely of another map between the same complexes.
- The fourth conjunct supplies an isomorphism of the two entire derived objects,
  whose hom is Q.map of S extended by zero from ℕ to ℤ, and its naturality
  equation for every f. This is the ordinary DerivedCategory C of the dependency,
  not only a collection of cohomology-object isomorphisms. Extension by zero
  is exactly the interpretation of a nonnegative complex as an integer complex.
- The last conjunct quantifies over every nonnegative M and chain map
  i : M ⟶ X.obj (⦋0⦌,⦋0⦌). The two hypotheses are i followed by the difference
  of the two first-direction cofaces and then the two second-direction cofaces,
  respectively, equal to zero as chain maps. This is δ₁i=δ₂i=0 in Lean's
  left-to-right composition convention.
- It supplies chain maps jD,jT with degree-m values i.f m followed by the
  canonical summand inclusion at cosimplicial degree zero. This is exactly
  support in degree zero, with no condition on the internal degree. Finally
  jD ≫ S X = jT is strict equality of chain maps, as in the node.

Dependencies read and used:

- def-sp-abelian: CategoryTheory.Abelian, Mathlib.CategoryTheory.Abelian.Basic;
  its full class extends preadditivity and normal mono/epi structure and includes
  finite products, kernels and cokernels. The ordinary total API uses its finite
  coproducts, including in the abelian category of internal complexes.
- def-weil-abstract-derived-category: HasDerivedCategory, DerivedCategory,
  DerivedCategory.Q in Mathlib.Algebra.Homology.DerivedCategory.Basic. The size
  parameter w is explicitly bound, and Q is the existing localization functor.
- def-sp-double-complex-total: WeilConjectures.CategoryTheory.DoubleComplexTotal
  is publicly imported. Its recorded primitive constructions are Mathlib's
  HomologicalComplex₂, total and ιTotal, reused directly. The same node's signed
  finite-diagonal construction for ℕ is provided by the already published
  WeilConjectures.Mathlib.Algebra.Homology.TotalComplex (hasTotal_up_nat), importing
  WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns (TensorSigns (up ℕ)).
  No sign instance or duplicate total construction was added.
- The published statement proof dependencies are imported without public:
  Mathlib.CategoryTheory.Abelian.Injective.Resolution (InjectiveResolution.desc
  and desc_commutes_zero) and Sheaf.Algebra.Homology.AugmentedResolutionLiftHomotopy
  (ModuleCat.augmented_lift_homotopy). I read their complete signatures and
  docstrings. The combinatorial child lem-sfb-simplex-lattice-shuffle-boundary
  has neither a Lean record nor a Mathlib match yet; it is proof-only, and
  therefore has no module to import. Its use is retained in the proof docstring.

The main docstring contains every step of the reviewed nine-step proof: free
representables and enough projectives, the two projective resolutions, the cone
and tensor contractions, the combinatorial signed boundary identity, lift in
the opposite category and uniqueness up to homotopy, contravariant evaluation
by finite matrices, compatibility with the internal differential including the
homotopy signs, derived localization and naturality, and strict augmentation.

Edge cases checked before finalizing:

- n=0 has exactly μ=∅, complement ∅, zero inversions and sign 1. Both counting
  maps are the identity of [0]; thus the component formula gives the required
  strict augmentation identity. The total degree zero formulas are typed.
- μ=∅ or μ=Fin n gives a=0 or b=0; the corresponding counting surjection
  is constant, with no nonemptiness premise on either subset. In particular
  the a=0 and b=0 summands have not been lost.
- The definitions do not assume nonconstant or normalized diagrams. Constant
  diagrams and a constant first or second direction use the same unnormalized
  alternating-coface construction, retaining all repeated vertices.
- The zero functor and zero internal complexes are admitted. Finite coproducts
  and all indicated zero maps exist in every abelian C.
- Internal degree r=0 and arbitrary r are both covered. Totals are indexed by ℕ,
  hence only finitely many indices contribute in each degree; integer negative
  degrees in the derived objects are supplied by actual extension by zero.

Searches actually run with the prescribed msearch.py wrapper:

- leanfinder: “The shuffle map from the diagonal of a bicosimplicial cochain
  complex to its double totalization is a natural chain homotopy equivalence
  preserving augmentations”. Eight hits: extra-degeneracy and one-variable
  Dold–Kan homotopy equivalences, not the requested bicosimplicial shuffle.
- loogle: '"CosimplicialObject", "total"': zero hits.
- grep: 'bicosimplicial|Eilenberg.Zilber|Alexander.Whitney|shuffle' in
  Algebra/Homology: zero hits.
- leansearch: “Finite totalization of a first quadrant cochain bicomplex indexed
  by natural numbers with signs minus one to the horizontal degree”: returned
  AlternatingCofaceMapComplex.obj, total, total_d and existing total-shape APIs.
  Their actual source was opened and reused.
- loogle: ComplexShape.TensorSigns: returned the sign structure and its induced
  total-shape instance. Mathlib grep for 'TensorSigns.*up ℕ|HasTotal.*up ℕ' had
  no hits, but direct rg of the project's WeilConjectures found the already
  published sign and finite-total instances; those were opened and reused.
- Direct rg for bicosimplicial, Bicosimplicial, shuffle and Shuffle in
  lean/WeilConjectures and lean/Sheaf, plus the exact blueprint id in both:
  no pre-existing declaration of this theorem. Direct DAG and blueprint search
  for nonnegative totals found general total-complex nodes, not this shuffle.
  blueprint_refs ancestor returns None, as recorded in the reviewed split.

No statement dispute or mathematical correction is needed. No new nodes,
statement_change or dependency-record repair is included. The sole expected
sorry is AlgebraicTopology.BicosimplicialShuffle.exists_shuffle.

## Validation

The prescribed scompile.py compiled the final module separately as a sandbox
module and as Sheaf.Algebra.Homology.BicosimplicialShuffleTotalization, without
errors or warnings (2.6 and 2.5 seconds). Explicit universes and autoImplicit=false
are in the module. All lines have at most 100 characters. Diagnostic #checks
were not retained. Delivery preflight follows below.

## Self-review by N7

I reopened the node and final signature and checked all clauses above against
the actual definitions. Initial elaboration repairs qualified Functor.curry,
Functor.whiskerLeft/Right and the Simplicial notation scope; explicit source and
target types were added to the degree-zero coface pairs to resolve product-category
metavariables. Unused lambda names were changed to underscore names. These changes
affect only elaboration, not the objects or statement. No separate agent was
started, as explicitly required by this worker brief; the maintainer supplies
the independent review.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
