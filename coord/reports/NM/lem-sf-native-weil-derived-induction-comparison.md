## Worker report

The module `Sheaf.Paper.NativeWeilDerivedInductionComparison` states
`AlgebraicGeometry.NativeWeilInduction.nativeWeil_derived_induction_comparison`.
Its proof is `sorry`; every helper has actual data. The node's statement, dependencies,
proof and all other fields are unchanged. There are no new or repaired dependency nodes.

The statement uses the actual native framework, the ordinary unbounded derived free
adjunction, and the native bounded-constructible localizing hull. It constructs beta and
the first Frobenius exchange by the standard localization and right-derivation APIs,
then asserts the normalization, coherent integer exchanges, and the specified transpose
kappa with its summand formula and invertibility on the localizing hull.

Hypotheses and introductory objects, clause by clause:

- The finite field is `(k₀ : Type u) [Field k₀] [Finite k₀]`. The native framework's
  geometric fibre uses its chosen `AlgebraicClosure k₀`; all sites, coefficients and
  Frobenius maps are exactly those of the recorded framework. The prime and characteristic
  restriction are `(l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`.
- `X` and `Y` are `Scheme.{u}` with their `Over (Spec (.of k₀))` instances. The map is
  `(f : X ⟶ Y) [f.IsOver (Spec (.of k₀))]`, with `IsSeparated f`, `QuasiCompact f`,
  and `LocallyOfFiniteType f`. The three conditions on the target structure map are
  `LocallyOfFiniteType`, `QuasiCompact`, `QuasiSeparated`. Those on the source are
  `LocallyOfFiniteType` and `QuasiCompact`. There is no absolute separatedness hypothesis.
- `(c : Compactification f)` supplies the fixed native compactification: its middle
  scheme is `c.Z`, its open immersion is `c.i`, its proper map is `c.g`, and its
  composition is `f`. The exact same `c` occurs in the ordinary and Weil operations.
  The existing `Compactification.over` supplies the canonical middle structure map
  through `c.g`; the module makes this already-defined instance available globally.
- For T equal to X, Y, or c.Z, `ProEtale.AdicSheaf l
  (T ↘ Spec (.of k₀)).geometricFiber` is the actual internal module heart over the locally
  finite continuous coefficient sheaf. `WeilSheaf.frobeniusPullback k₀ l T` is the actual
  geometric Frobenius pullback, and `ProEtaleWeilSheaf k₀ l T` is its `IsoAlgebra` heart.
  No coefficient sheaf or constructibility predicate is copied.
- `ProEtale.DerivedCategory.boundedAdicConstructible` supplies C_T: bounded ordinary
  derived objects with native constructible cohomology. I read the full definitions in
  `Adic/Constructible.lean`: `IsAdicLisseSheaf` quantifies over each cover member before
  choosing its finite rank, `IsAdicStratifiedLisseSheaf` requires constructible locally
  closed disjoint covering strata, and `IsAdicConstructibleSheaf` makes this local.
  In particular no single rank across a cover is imposed.
- L_T is `ProEtale.nativeAdicConstructibleLocalizingHull`, the existing abbreviation for
  `ObjectProperty.localizingClosure` of that bounded-constructible predicate. This is
  full, replete, triangulated and closed under small coproducts. The explicit scheme
  universe is u; heart and derived Hom groups, all small indexing sets and the sums in
  the statement use u+1. The generic comparison helpers have explicitly bound u, v, w.
- `forget` is the native `IsoAlgebra.forget` localized by `mapDerivedCategory`;
  `induction` is the recorded `IsoAlgebra.Free.functor` localized the same way.
  Units and counits are specifically `IsoAlgebra.freeWeilDerivedAdjunction`, never an
  arbitrary adjunction witness. `HeartProperties` includes `IsColimit` for the canonical
  integer cocone into U_T I_T A, rendering the asserted underlying direct-sum formula.
- `ordinaryImage` abbreviates the actual termwise native adic open extension along the
  geometric fibre of `c.i`, followed by the actual native adic right-derived proper
  image along that of `c.g`. F_W is the existing
  `ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c`, with the same native coefficient
  maps and Frobenius lifts. Its definition is exactly the analogous Weil composite.

Conclusions and normalizations, clause by clause:

- The first three conjuncts are `HeartProperties` at X, Y and c.Z. Its Grothendieck
  assertions concern the actual ordinary and Weil hearts, whose abelian instances are
  already supplied by the framework. Finite limits and finite colimits give exactness
  of heart forgetting. Its derived functor is triangulated (derived exactness), reflects
  isomorphisms (conservativity), and preserves every `Discrete J` coproduct for
  `J : Type (u+1)`. The heart forgetful functor preserves K-injective complexes.
- The remaining fields of `HeartProperties` state P_T(C_T) is contained in C_T and
  P_T(L_T) is contained in L_T. They use the derived native Frobenius, not a replacement
  endofunctor. The final field supplies the specified free coproduct cocone for every A.
- The next two conjuncts are `.IsTriangulated` for the actual F and F_W.
- `comparison` is beta as a natural isomorphism `F_W ⋙ U_Y ≅ U_X ⋙ F` in Lean's
  left-to-right functor composition order. Its domain is the entire ordinary derived
  Weil category. It is explicitly assembled from `properComparison`, `openComparison`,
  whiskering and associators; it is not an existential arbitrary isomorphism.
- `properComparison` uses `rightDerivedFunctorMapOfNatIsoCompForgetIso` for the actual
  native proper lift. `ProperNormalization` is its equation with the actual proper
  right-derived units and exact forgetting factors on every K-injective Weil complex.
  This equation identifies both evaluations through the same complex p_* U_Z J: the
  intermediate sheaf functors agree definitionally on objects and arrows. The comparison
  is a natural isomorphism, so this equation also respects derived morphisms.
- `openComparison` uses `exactForgetComparison` for the actual native open lift.
  `OpenNormalization` specializes `exactForgetNormalization` to this very same lift:
  its equation compares the two exact localization factorizations, with the termwise
  underlying complexes literally identical. The generic predicate avoids expensive
  elaboration of repeated concrete sheaf-category expressions; it changes no equation.
- `exchange` is c_1, derived directly from the native proper and open Frobenius exchange
  isomorphisms. `rightExchange` uses exact Frobenius equivalences and their canonical
  derived comparison factors. No arbitrary Frobenius exchange is supplied as a hypothesis.
- The existential family `cN n A` gives c_n for every integer n and ordinary derived A.
  The first field is naturality on every derived arrow, expressed using the recorded
  `IsoAlgebra.Free.objMap`. The second is c_0 = identity. The third is the successor
  recurrence using `Free.objSucc` and the native `exchange` on P_X^n A. This pins down
  all positive and negative iterates: at n=-1 the invertible factors determine c_-1
  from c_0, and descending induction determines all remaining negative terms. Thus the
  existential is not an unconstrained comparison; it is the coherent iterate system
  of the specified c_1 with the chosen inverse and coherence of `Free.obj`.
- The next existential is a natural transformation κ : `F ⋙ I_Y ⟶ I_X ⋙ F_W`, with
  its component fixed by the explicit transpose formula: I_Y applied to F(eta_X)
  followed by beta inverse, then the actual derived free counit at F_W I_X A.
- For every A satisfying L_X, `IsIso (κ.app A)` is asserted. The following equality for
  every `n : ℤ` is exactly inclusion_n followed by U_Y(κ_A) followed by beta_{I_X A}
  equal to c_{n,A} followed by F(inclusion_n). The directions match the node in Lean's
  composition order.
- `inclusion` is constructed from the actual derived free unit and the n-th iterate of
  the localized free structure, using existing `Free.hom`, including the negative
  recursion. Its cocone is asserted colimiting above; hence it really is the n-th
  coprojection under the canonical UI direct-sum identification. `structureIso` is the
  localization of the existing structure natural isomorphism. Forming the individual
  `IsoAlgebra.mk` needed by `Free.hom` supplies an underlying structure to each derived
  Weil object; it asserts no equivalence with fixed pairs in the derived category.

Dependency declarations read and used:

- `def-sf-native-weil-derived-framework`: `WeilConjectures.WeilSheaf.LowerShriek`,
  `ProEtaleWeilSheaf.rightDerivedLowerShriek`, and the modules it publicly imports:
  `WeilSheaf.Category` (`ProEtaleWeilSheaf`, `WeilSheaf.frobeniusPullback`),
  `WeilSheaf.LowerStar` (`ProEtaleWeilSheaf.lowerStar`), and `WeilSheaf.OpenImmersion`
  (`ProEtaleWeilSheaf.extensionByZero`). I read their full signatures and docstrings.
  I also read `Adic.Module`, `Adic.Constructible`, `Adic.ConstantSheaf`, `Adic.Truncation`
  and the native `Adic.GeometricFrobenius` exchange definitions used in these signatures.
- `lem-sf-free-derived-weil-resolution`: `Sheaf.CategoryTheory.FreeDerivedWeilResolution`,
  `CategoryTheory.Endofunctor.IsoAlgebra.freeWeilDerivedAdjunction`, its exact-free
  instance, and its heart and derived property assertions. The module was read in full.
  Its canonical adjunction and the original `IsoAlgebra.Free` construction are reused.
- `def-weil-triangulated-subcategory`: Mathlib's recorded
  `CategoryTheory.ObjectProperty.IsTriangulated` in `Triangulated.Subcategory`, with
  upstream `ObjectProperty.localizingClosure` for its replete localizing hull.
- `def-weil-size-convention`: the record explicitly says this is a metatheoretic
  convention with no definiendum. Explicit universes render it; there is no invented
  Lean definition or additional size equality hypothesis.

The stated proof dependencies that have modules are imported, publicly only when their
objects occur in the statement. In particular `NativeAdicCompactSupportSums` supplies the
existing native hull abbreviation and the coproduct theorem for proof step 8. The main
proof docstring includes all eight DAG proof steps, including the chain-map structure
calculation, arbitrary derived-arrow naturality, and the final coproduct/conservativity
argument. Generic exact-functor localization and normalized comparison APIs already
provided by the published library are used without restating dependency nodes.

Edge cases checked before and after writing:

- Empty schemes and zero objects introduce no nonempty or positive-rank assumption;
  the native constructibility definition permits rank zero and empty strata.
- There is no boundedness assumption on A except membership in L_X for the invertibility
  and summand conclusions. K-injective normalization quantifies over unbounded complexes.
- The index n is an integer throughout; the n=-1 successor equation runs from the chosen
  inverse to c_0, so negative powers are not discarded. The zeroth equation is identity.
- The identity compactification and identity Frobenius still use the actual unit,
  counit, native exchanges and the free structure. A nontrivial Weil automorphism is
  not erased when the underlying Frobenius functor is identity.
- Only f is separated; no step of the formal statement assumes X or Y absolutely
  separated. The compactification middle has its canonical map through the proper factor.
- Coproduct preservation is required of U on the whole ordinary derived category,
  but κ invertibility is required only on L_X. There is no assertion that F preserves
  every ambient coproduct.

Searches for an existing full statement:

- `msearch.py`, LeanFinder: "Free induction comparison with compactly supported pushforward
  of native Weil sheaves on ordinary unbounded derived categories". Eight hits concerned
  condensed free functors, sheaf free modules and derived t-structure facts; no match.
- `msearch.py`, Loogle: "IsoAlgebra.Free, rightDerivedFunctorMapOfNatIsoCompForgetIso".
  No hits; unknown identifier `IsoAlgebra.Free` in the Mathlib service. Direct project
  inspection located the existing free and proper-forgetting constructions listed above.
- `msearch.py`, grep in CategoryTheory: "inductionComparison|freeWeil|CompForgetIso".
  Three Mathlib hits were unrelated over/under and monoidal opposite comparisons.
- `msearch.py`, LeanSearch: "Derived induction commutes with Frobenius equivariant compact
  support". Eight hits concerned Witt-vector Frobenius, analytic compact support,
  Frobenius field equivalences and their iterates; no match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for native induction/comparison,
  `freeWeil`, `derivedInduction`, `inductionComparison`, and exact new declaration names,
  plus the node id in upstream sources. No existing theorem states this node.
  The searches found the generic free-resolution module, the native operations and
  comparison APIs, and the native compact-support sums module, all reused here.
- Searched `dag/lean_names_upstream.json` and both source trees for the chosen full
  namespace and primary declaration: no clash. Nearby native open exactness and native
  closed duality comparisons do not assert the derived induction comparison.

Validation: `scompile.py NM lem-sf-native-weil-derived-induction-comparison` compiled the
sandbox and its actual library module separately in 6.6 and 6.7 seconds. No errors or
warnings remained. `autoImplicit` is false, every universe and section variable is bound,
and all lines fit the 100-character convention. Earlier failures were repaired by
supplying the canonical middle base structure, explicit exact integer-coproduct instances,
and a generic presentation of the exact normalization equation. No source files or
launcher tools were edited. Delivery preflight and its final compilation follow below.

No statement dispute or correction was needed.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
