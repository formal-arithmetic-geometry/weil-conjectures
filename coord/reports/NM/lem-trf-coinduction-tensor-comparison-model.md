## Worker report

Module `Sheaf.Algebra.Homology.CoinductionTensorComparisonModel` states
`ModuleCat.coinduction_tensor_comparison_model`. Its proof is `sorry`; all five helper
abbreviations/predicates have real data. The node's statement, dependencies and proof plan
are unchanged. No new nodes or dependency repairs are needed.

Hypotheses and clauses, matched individually:

- A commutative ring homomorphism is the section binder `f : R →+* B`, with
  `[CommRing R] [CommRing B]`. The independently bound derived morphism universes
  `wR`, `wB` are retained. The ordinary categories are `DerivedCategory (ModuleCat.{u} R)`
  and `DerivedCategory (ModuleCat.{u} B)`. Any two ring/module universes can be placed
  in a common maximum universe; the chosen common carrier universe imposes no algebraic
  assumption. All universes and variables are explicitly bound; autoImplicit is false.
- Restriction, coinduction, its action, and its evaluation-at-one counit are exactly
  `restrictScalars f`, `derivedCoinduction f`, `coinductionComplexFunctor f`,
  `derivedCoinductionAdjunction f` and `coinductionEvaluation f I` from the recorded
  coinduction dependency. In particular the chain Hom carrier is the published
  `CoextendScalars.equiv`, not a separate choice of an adjoint or a Hom object.
- `R[0]` is the cochain tensor unit. `J`, `[J.IsKInjective]`, `η` and `[QuasiIso η]`
  are ANY K-injective unit resolution. The first conjunct constructs its isomorphism
  `d : C_B(Q 1) ≅ Q V`, with its hom explicitly `C_B(Q η)` followed by the published
  K-injective model comparison. Thus `V` represents precisely `D_B`.
- `coinductionTensorSource f J` abbreviates the fixed-second-factor tensor functor of
  `exists_derivedTensor_second_factor_functor f`, applied to `V`. Its computation map
  is abbreviated by `coinductionTensorSourceComparison`. Choice is made only from the
  existing universal left-derived-functor statement, which determines the functor up
  to its unique compatible isomorphism. No arbitrary map or mere Nonempty is chosen.
- The second conjunct asserts the computation comparison is invertible for EVERY
  K-flat `F`; the K-flat predicate is the dependency's actual
  `(HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat`.
- The existential `σ : coinductionTensorSource f J ⟶ derivedCoinduction f` is a natural
  transformation. `CoinductionTensorCounitNormalized f J η σ` specifies its adjunct
  on every K-flat model: `s.hom = Q.map ((ρ_ F).inv ≫ F ◁ η)`, and restriction of
  `σ` followed by the actual counit equals the tensor computation map, the exact
  scalar-restriction factorization, `Q.map e`, and `s.inv`. The formula predicate for
  `e` says `x ⊗ h ↦ x ⊗ h(1)`; with the extension scalar it says `h ⊗ (b ⊗ x)`
  maps to `x ⊗ h(b)`. Consequently this is exactly tensoring the counit and then
  identifying `K ⊗ R[0]` with `K`, expressed through the specified representatives.
  Uniqueness of normalized `τ` asserts the canonical adjunct, not an arbitrary map.
- Naturality for EVERY derived morphism `u : K ⟶ K'` is the third conjunct after
  `σ`: `σ.app K ≫ C_B.map u = L.map u ≫ σ.app K'`. It does not require a chain
  representative for `u`.
- ANY K-flat representative is quantified as `F`, `hF`, `c : Q.obj F ≅ K`. ANY
  K-injective resolution of `F ⊗ J` is `I`, `[I.IsKInjective]`, `q`, `[QuasiIso q]`.
  `a : K ≅ Q.obj I` has `c.hom ≫ a.hom = Q.map ((ρ_ F).inv ≫ F ◁ η ≫ q)`.
  Thus the precise identification of `I` with `K` is included.
- The existential `t` has the type of a `B`-linear CHAIN map from the actual mixed
  total tensor of `F,V` to the actual coinduced Hom complex of `I`. Its predicate
  `coinductionTensorChainFormula` specifies on every summand `p+r=n`, every `x,h`,
  and every `b,b'` the equation
  `t(h ⊗ (b ⊗ x))(b') = q(ι(x ⊗ h(b' * b)))`.
  Setting `b=1` gives precisely `t(x ⊗ h)(b') = q(x ⊗ h(b'))`. Including arbitrary
  `b` fixes the extension presentation on all generators; it adds no restriction
  beyond balancing and the prescribed coextension action. The chain-map type includes
  the differential equation with the total sign `(-1)^p`.
- The representative localization equation identifies `σ.app K`, transported through
  `a` and the published coinduction comparison, with `L.map c.inv`, the published
  tensor computation comparison and `Q.map t`. Hence both its source and target models
  and the localized comparison itself are identified, rather than just isomorphic
  as unrelated objects.
- The next existential `e` satisfies the generator formula and the CHAIN-MAP equation
  `U(t) ≫ coinductionEvaluation f I = e ≫ q`. This includes exactly the counit composite
  `x ⊗ h ↦ q(x ⊗ h(1))`. The same formula, using `CoextendScalars.equiv` into the
  ordinary R-linear Hom carrier, also specifies the usual underlying Hom/tensor
  evaluation after scalar restriction. No second evaluation map or extra sign is used.
- Independence of `F,c,I,q` is expressed by the universal model equation for the SAME
  `σ`; uniqueness makes the localized maps agree under these identifications.
  For ANY other unit resolution `J',η'` and any normalized `σ'`, the last conjunct
  supplies a chain comparison `k` commuting with the unit maps AFTER LOCALIZATION
  (K-injectivity represents the inverse-resolution derived comparison). For EVERY
  such `k`, the existing second-factor tensor comparison is invertible and carries
  `σ'` to `σ`. This covers arbitrary choices of `J`, including resolutions without
  a strictly commuting comparison. The dependency's functorial comparisons compose,
  and uniqueness removes any dependence on the representative `k`.
- No perfectness, flatness, Noetherian condition or boundedness is present. In
  particular no `IsIso σ`, `IsIso (σ.app K)` or `QuasiIso t` is asserted.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, with their full size binders.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`: all the construction/model/
  counit declarations listed above, and `derivedCoinductionAdjunction_spec`. Its
  degreewise ordinary Hom construction already supplies the B[0] specialization;
  no duplicate general Hom-complex construction is necessary.
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`:
  `DerivedCategory.exists_derivedTensor_second_factor_functor`; read its complete
  signature and proof, including functoriality in the second factor and the
  invertible K-flat computation maps.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat` (reexported by the tensor dependency).
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, and its public generic
  `derivedInternalHomOfUniverses` comparison framework, imported as recorded.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex` and
  `homComplexFunctor`, imported as recorded; its general product formula reduces
  to degreewise Hom for B[0], already implemented by the coinduction dependency.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `HomologicalComplex.ιMapBifunctor` and `ιTensorObj` expose every direct-sum summand.
  `ModuleCat.mixedTensor`, from `WeilConjectures.Algebra.Homology.MixedTotalTensor`,
  supplies the B-action and is totalized in the order (F,V).
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, used directly for both resolutions.

Sources read: Stacks dualizing.tex, section Trivial duality for a ring map,
labels lemma-right-adjoint (0A70), lemma-RHom-ext (0A71), including their proofs.
The current blueprint proof of lem-trf-local-term-locality was read at
literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/.
The node is the technical algebraic input split below that blueprint, not a unit statement.

Edge cases checked mathematically before writing: identity ring map (comparison is
ordinary tensor/Hom evaluation), zero input, zero coefficient ring, the nonflat map
Z → Z/2, unbounded F and J, and arbitrary derived morphisms. The mixed extension
presentation retains b'b (commutativity permits bb' but no change of action is made).
Only B is in degree zero; neither F nor J nor I is restricted. Direct sums keep each
input finitely supported, even though the general Hom construction uses products.
The comparison need not be invertible for an arbitrary algebra. K-injective comparison
maps need only commute with the unit resolutions after localization; that case is
included explicitly, avoiding an accidental strict-comparison restriction.

Searches for duplicates:

- msearch.py leanfinder: “Unbounded derived coinduction tensor comparison represented
  by f tensor h maps to b maps to q f tensor h b”. Eight hits, headed by Rep.Tor_map
  and ordinary representation tensor/induction maps; none is this chain model.
- msearch.py loogle: “ModuleCat.restrictCoextendScalarsAdj,
  CategoryTheory.Adjunction.counit”. No hits.
- msearch.py grep: “coextendScalars|restrictCoextendScalarsAdj”, subdirectory
  Algebra/Category/ModuleCat. Seven hits; the ChangeOfRings source defines ordinary
  coextension and evaluation, not the derived comparison model.
- msearch.py leansearch: “unbounded derived coinduction tensor comparison canonical
  evaluation counit chain model”. Eight general adjunction/derived-counit hits;
  none has the arbitrary unbounded chain formula and representative clauses.
- rg over WeilConjectures and Sheaf for coinduction/Coinduction/mixedTensor and
  tensor-comparison names; also the exact node id in WeilConjectures. Read the full
  DerivedCoinductionAdjunction, DerivedTensorSecondFactorFunctor, MixedTotalTensor,
  MixedTensorRestrictionComparison, and PerfectAlgebraCoinductionTensor candidates.
  The last assumes perfectness and asserts invertibility, so is not this item.
  Existing tensor-source and computation abbreviations in ChangeOfRingsTensor are
  owned by an unrelated quotient-ring theorem; this delivery names its own fixed
  coinduced specialization of the same universal functor, not a new tensor notion.
- Exact proposed declaration-name searches over Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json found no collision after renaming the normalization
  predicate to `ModuleCat.CoinductionTensorCounitNormalized`: the shorter initial
  name was already used for an unrelated Tor-independent exchange predicate.

Validation: scompile.py compiled the final single file against the live published
library in both sandbox and library contexts (16.0 s and 10.4 s), cleanly. The only
postponed theorem is the main node theorem. No STATEMENT-DISPUTED or node fault.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
