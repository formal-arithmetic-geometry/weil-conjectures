## Worker report

Item: lem-sfb-cyclic-row-derived-comparison. Module:
`Sheaf.CategoryTheory.CyclicRowDerivedComparison`. This is stage 2: each new theorem
and the quasi-isomorphism instance have `sorry` proofs, with the complete argument
in their source/blueprint docstrings. Definitions have actual data.

The source read is the current `literature/blueprint/latest/` direct-image proof,
paragraph (3), together with this node's accepted eight-step agent extraction.
The latest snapshot is main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8.
The blueprint paragraph motivates the extracted task; it does not itself state
this relative calculation. Its recorded combined external reference remains
WANTED; I have not invented a citation. I also read Stacks `derived.tex`, labels
lemma-subcategory-right-resolution (05T6), lemma-injective-acyclic (05TH),
lemma-enough-injectives-right-derived (05TI), and `homology.tex`,
lemma-double-complex-gives-resolution (0133), including its row variant.
No repair note for this item is present.

Hypothesis and clause correspondence:

1. Arbitrary commutative condensed R is `A : CondensedBar.Ring.{u}`, the existing
   `CommMon` of abelian sheaves on `coherentTopology Profinite.{u}`. `A.toMon` is
   the recorded `Profinite.CondensedRing` and its commutativity is the existing
   `ringComm` instance. This includes rings without a topological presentation.
   Modules are the existing internal `Mod` through `CondensedBar.Modules A`.
   There is one explicit universe `u`; coefficients have universe u+1 and the
   internal/action categories have object universe u+2. Group parameter sets
   have universe u. The lattice bridge explicitly transports its larger derived
   Hom universe, rather than identifying universe levels.
2. G and H have explicit group, topology and topological-group binders, with
   `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace` for profiniteness. H is
   bound only in declarations using restriction. The cyclic group is the existing
   `Z.{u} = Multiplicative (ULift ℤ)` with discrete topology and generator +1;
   `v : Z.{u} →ₜ* H` is the continuous homomorphism in the node. No surjectivity
   or density assumption on v is made.
3. All actions are the existing `CondensedBar.Equivariant` abbreviation of
   `Profinite.CondensedAction.ActionModule`, acting on continuous P-valued
   sections after every profinite base change. `invariants A G J`, `derived`,
   `unit`, `forgetResidual`, `CondensedBar.forgetAction`, `productMap`, `inflate`,
   `beta` and `forgetDerived` are the recorded normalized constructions, not
   private replacements. These respectively render Gamma, RGamma, alpha, U_J,
   U_0, id_G times v, V, beta and delta.
4. The cyclic complex is an existing `TotalModel A G`. Its `coordinates`,
   `differential`, `maps` and `augmentation_coordinates` say exactly
   N^n plus N^(n-1), (dx,(T-1)x-dy), diagonal maps and (inclusion,0).
   The signed-total theorem already supplies existence and descent; quantifying
   over a coordinate model and its localization comparison does not assume a
   new comparison with derived invariants.
5. `cyclicRow_injective_module` is precisely the quasi-isomorphism of the row
   for `[Injective I]`, with `single ... I` the module in degree zero.
   `cyclicRow_injective_complex` covers every `I : CochainComplex.Plus ...`
   with `[∀ n, Injective (I.obj.X n)]`, with no nonnegative-only restriction.
6. `RowNormalized ... θ` is the displayed equation theta alpha = Qb on EVERY
   P in the bounded-below complex category. Its two extra arrows are the
   existing `plusQιIso` and the total's localization isomorphism e. They only
   reconcile the standard Q and Qh presentations. Composition is written in
   Lean's left-to-right categorical order.
7. `cyclicRow_derived_comparison` asserts `∃! θ, RowNormalized ... θ` separately
   from `∀ θ, RowNormalized ... θ → IsIso θ ∧ NatTrans.CommShift θ ℤ`.
   Thus uniqueness is among all normalized transformations, not merely among
   invertible ones or ones fixing H-zero. F and e range over the actual
   localization of K; their existence with the required signed shifts is
   `exists_signed_cyclicTotal`. `_hK` and `_he` impose exactly those canonical
   signed comparisons, not a resolution or any injectivity of the input P.
8. `cyclicRow_hasComparison` supplies the existing `HasComparison` predicate,
   so subsequent clauses use its existing `lambda`, the inverse theta. The
   normalization is on all complexes, so on a module it is exactly the
   actual invariant inclusion, not an unspecified degree-zero isomorphism.
9. `cyclicRow_resolution_formula` quantifies over ANY quasi-isomorphism
   a:N→I to ANY bounded-below termwise injective I, without requiring a mono.
   It reads lambda_N = Q(Ka) Q(b_I)^(-1) alpha_I RG(Qa)^(-1), the node's exact
   four arrows in composition order. The augmentation inverse is available
   from the preceding quasi-isomorphism instance. Equality to the same existing
   lambda_N for every a expresses independence of all resolutions.
10. `cyclicRow_resolution_naturality` is the naturality square for every chain
    map of bounded-below complexes. It therefore includes specified diagrams
    of resolutions and their cones; the formula applies at every vertex.
    `cyclicRow_shift_boundary` gives `CommShift` and the last-arrow square
    for every degree-one arrow, hence the actual cone boundary -p. The signed
    shift and cone structures are those already specified by the total node.
11. `cyclicRow_forgotten_normalization` identifies the forgotten augmentation
    with the SCALAR unit on every complex. Its inverse `forgetInvariants`
    identifies the actual fixed-submodule domains. `forgottenLambda` includes
    all exact-functor localization comparisons; it is not an arbitrary map.
12. `cyclicRow_forgetting` gives a UNIQUE NATURAL isomorphism k of the two
    forgotten total functors, with BOTH coordinate projections specified.
    Its equation identifies the forgotten lambda with the scalar lambda
    computed using a trivial residual group, on every bounded-below input.
    Inverting the equation gives the theta equality. `scalarizationIso` is the
    identity-underlying add/forget comparison; `forgetDerived` is normalized
    by computation units. `NatTrans.CommShift k.hom ℤ` retains signed shifts
    and boundaries. The two shift instances are actual `CommShift.ofComp`
    transports through the existing fully faithful inclusion; no theorem or
    shift structure is postulated to define them. A further instance caches the
    existing canonical topological-group structure of the lifted discrete
    integers; its data are obtained by `inferInstanceAs`, not by a postponed proof.
13. `rowForgetIso` selects that unique coordinate-preserving identification;
    its data are determined uniquely, so this is not a hollow choice.
    `rowRestrictionMap` defines c on a bounded-below complex by beta followed
    by the exact restriction localization comparison followed by lambda inverse.
    `cyclicRow_restriction_forgetting` equates its forgotten value to scalar
    group restriction followed by `forgottenLambda` inverse, which the preceding
    theorem identifies with scalar lambda through the canonical row coordinates.
    All exact-functor localization factors are explicit. No inverse of beta and
    no injectivity of V(I) is assumed.
14. `Profinite.DiscreteLattice.cyclicRow_lattice_witness` simultaneously chooses
    the lattice family K and comparison family at ALL rings and ranks, retains
    exactly the full coefficient-square and rank-zero clauses of the recorded
    lattice existential witness, and adds its rank-one equality with the
    forgotten lambda. Thus the chosen rank-one comparison really is a witness
    to that theorem, including coefficient naturality. `DiscreteBridge` fixes
    the action equivalence by the positive generator and invariant inclusion;
    `DiscreteDerivedBridge` fixes its derived comparison by computation units
    on every complex. `lowerDerived` and `lowerQ` keep the two localization
    universes distinct. The chain comparison fixes degrees zero and one by
    `zeroCoordinate`, `oneCoordinate` and the empty/singleton subset projections.

Dependency declarations read and used (including full definitions/docstrings):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `ModObj`, `Mod`, `Mod.Hom`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Modules`, `ActionModule`,
  `inflate`, `Invariants`, `ProductInvariants` and their inclusion/transpose fields.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `Q` and its quasi-isomorphism inversion instance.
- `Sheaf.CategoryTheory.ProductActionExactForgetting`: `Datum`, `ExactForgetting`,
  `exists_datum`; used in the proof plan for exact conservative/injective forgetting.
- `Sheaf.CategoryTheory.RelativeRestrictionMateForgetting`: `beta_mate`,
  `beta_forget_natTrans`, `beta_boundary`, `forgetDerived_boundary`.
- `Sheaf.CategoryTheory.CyclicTotalTriangulated`: `HasSignedTotalShift`,
  `IsTotalDescent`, `exists_signed_cyclicTotal`, `cyclicTotal_cone`,
  `cyclicTotal_lowerBound`, `cyclicTotal_transpose`.
- `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution`: `KoszulModel`,
  `Comparison`, `CoefficientComparison`, `derivedUnit`, `invariantUnit`,
  `discrete_lattice_koszul_resolution` and the action/invariant/restriction definitions.
- The Mathlib match of `lem-weil-pbc-right-derived-plus-injective` is used:
  `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
  `Functor.rightDerivedFunctorPlus`, `rightDerivedFunctorPlusUnit` and
  the `IsRightDerivedFunctor`/left Kan extension property in
  `Mathlib.CategoryTheory.Functor.Derived.RightDerived`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`/`.Resolution`:
  `Injective`, `InjectiveResolution`.
- Existing owning definition modules `RelativeDerivedInvariants`,
  `RelativeCyclicTotal`, `RelativeInvariantForgetting`, `RelativeLatticeBridge`:
  the recorded invariants, units, TotalModel, HasComparison, lambda, plusQ,
  plusQιIso, descent, single, forgetDerived, forgottenLambda, scalarizationIso,
  DiscreteBridge, DiscreteDerivedBridge, lowerDerived, lowerQ and coordinate maps.
  Their four landed owning nodes are added to stmt_deps; their Lean records need
  no repair. There are no new definition nodes or dependency modules.
- Proof imports include the existing first-quadrant total comparison,
  bounded-below injective resolution, specified-resolution/cone naturality,
  ordinary scalar restriction and condensed derived restriction calculus.

Edge cases checked before writing: G=1 gives the scalar construction; H=1 and
v=0 are permitted and give T-1=0 after restriction. No claim that T-1 is
surjective on an arbitrary module occurs: the row quasi-isomorphism is asserted
only on injectives. Negative lower bounds are retained in `CochainComplex.Plus`.
Zero complexes and the zero ring are included without a nontriviality assumption.
The rank-zero identity and every scalar map, including nonflat scalar maps, remain
in the lattice witness. The empty and singleton subset projections are the correct
rank-one coordinates, and the second total summand has the negative vertical
sign. The source uses -p as its cone boundary. No statement correction or
STATEMENT-DISPUTED flag is required.

Searches actually run via `msearch.py Q16 lem-sfb-cyclic-row-derived-comparison`:

- leanfinder: `Infinite cyclic invariants derived comparison row augmentation
  normalized on all bounded below complexes`. Eight hits concerned generic
  augmentations, extensions and Moore complexes; none was this statement.
- loogle: `CategoryTheory.RelativeCyclic, rightDerivedFunctorPlus`. Zero hits;
  unknown project identifier CategoryTheory.RelativeCyclic.
- grep: `cyclic.*(comparison|invariant)|rowAugmentation` in CategoryTheory.
  Zero Mathlib hits.
- leansearch: `Derived invariants of an infinite cyclic group are the two term
  complex with differential generator minus identity`. Eight hits included
  groupCohomology.d₀₁_ker_eq_invariants and finite-cyclic group resolutions.
  These concern ordinary representations/finite cyclic groups, not internal
  condensed modules with residual action and normalized derived arrows.
- rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id and cyclic row/comparison names found no existing full item.
  It found the recorded TotalModel/HasComparison and forgetting/lattice bridges,
  which are reused. The downstream `RelativeCyclicRestrictionModel.forgetLambda`
  and `.latticeCompatibility` give some related clauses, but not the injective
  row, unique all-complex theta or resolution formula; that downstream theorem
  is deliberately not imported as a prerequisite of its own proof. The new
  forgetting statement is a natural shift-compatible functor isomorphism,
  and the new lattice statement retains the simultaneous full witness.
  A further search found `LatticeKoszulInjectiveNormalization`, whose statement
  was read: it works in the abstract lattice action category with its finite
  total and does not state this residual condensed-action comparison.

## Second reading by Q16

This is the author's separate rereading, not a claim of an independent worker;
the dispatcher forbids spawning agents, and the maintainer reviews independently.
I reopened the node and checked each clause against the declarations above.
The normalization quantifies over all P and its uniqueness does not use H-zero.
The resolution formula has the correct order of the four arrows and allows every
quasi-isomorphism. The original draft omitted a canonical shift instance for the
composite of bounded-below forgetting functors; I supplied it by the existing
full-inclusion transport rather than adding a shift hypothesis. The scalar square
includes exact-localization and scalarization maps. The lattice statement retains
its coefficient square and rank-zero clauses instead of merely choosing an
individual module isomorphism. No definition was chosen from a non-unique existence
claim. No source statement, accepted proof plan, or target statement was changed.
