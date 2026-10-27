## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleProperOpenExchangeCube` states
`AlgebraicGeometry.Etale.etaleProperOpenExchangeCube`, with proof `sorry`.
It asserts the existence of the normalized sheaf comparison family `θ` and the
normalized unbounded derived natural-isomorphism family `Γ`, including all the
pasting, identity and cube equations. The two public abbreviations name their
function types only; they do not construct different categories, functors or maps.
They belong to this comparison theorem and are recorded in `lean.declarations`.
There is no new independent notion, dependency repair or statement correction.
Only the item's `lean` record changes.

Sources read: Stacks `more-etale.tex`, the statement and proof of
`lemma-shriek-proper-and-open` (0F7B, especially case (b)), the vertical and
horizontal composition lemmas (0F7C and 0F7D), `remark-going-around` (0F7E), and
`lemma-shriek-proper-and-open-base-change` (0F7F). These explicitly allow a
non-Cartesian original square. The latest blueprint's
`sec-six-functors-basics/sk-prop-sf-cbc/prop-asd-smooth-base-change.proof.md`,
coherences (i) and (iii), and its `_section.md` were also read. The support
normalization is exactly the first paragraph of 0F7B's proof; the extra Cartesian
mate normalization is the recorded `etaleProperOpenTensorSquare` interface.

### Every hypothesis and clause

| Node text | Lean rendering |
| --- | --- |
| A finite commutative ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]`; no nonzero or characteristic restriction. |
| Ordinary unbounded small-etale module derived categories | `DerivedCategoryModule A U`, the existing abbreviation for `DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))`; the family types use these same derived categories through the existing functors. |
| Exact inverse image P, total derived direct image R, termwise open extension J | The existing `D((v)^*[ModuleCat A])`, `R((v)_*[ModuleCat A])`, and `D((j)_!open[ModuleCat A])`. The displayed `. {u + 1}` universes in the file follow the recorded six-functor coefficient convention. No new versions of these operations are defined. |
| Arbitrary schemes U,V,W,Z and commutativity pk=ir | `{U V W Z : Scheme.{u}}` and `CommSq k r p i`; its equation is `k ≫ p = r ≫ i`. |
| p and r proper; i and k open | `[IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]` in both family types and the quantified clauses. No Cartesian condition occurs here. |
| Canonical natural isomorphism J_i R_r to R_p J_k | `Γ : ProperOpenDerivedComparisonFamily A`; its value is the natural isomorphism `R(r_*) ⋙ D(i_!) ≅ D(k_!) ⋙ R(p_*)`. Lean functors compose in application order, so this is the stated orientation. |
| Canonical sheaf proper-support identification theta | `θ : ProperOpenSheafComparisonFamily A`, and the first conjunct, equating the two composites into `(r ≫ i)_*`. The two maps into that common direct image use `openImmersionLowerShriekToLowerStar` and the canonical `lowerStarComp`; on the right `sq.w.symm` supplies exactly the common composite. This pins theta to the identity on the underlying sections, rather than an arbitrary natural isomorphism. By the proper/open support specializations of `properSupportSheafComposition`, these are precisely the two proper-support subsheaves of the node. |
| Every K-injective representative I and every K-injective resolution k_!I -> H | Second conjunct: `I`, `H`, `[I.IsKInjective]`, `[H.IsKInjective]`, `ρ : (k_!.mapHomologicalComplex (.up ℤ)).obj I ⟶ H`, `[QuasiIso ρ]`. It does not require degreewise injectivity. |
| The representative is i_!r_*I -> p_*k_!I -> p_*H | The right side of that conjunct is `DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (θ ...).hom (.up ℤ)).app I ≫ p_*.mapHomologicalComplex.map ρ)`, followed by the canonical resolution identifications. On the left, `i_!.mapDerivedCategoryFactors.inv` and `D(i_!).map (r_*.rightDerivedFunctorObjQIso I).inv` identify the source with J_i R_r(QI). On the right, `p_*.rightDerivedFunctorObjQIso H` and `R(p_*).map (inv (Q.map ρ) ≫ k_!.mapDerivedCategoryFactors.inv.app I)` identify the target with R_p J_k(QI). Thus this is equality of the specified component with the localized chain map, not just existence of isomorphic values. |
| For Cartesian Q the specified unit--open-base-change--counit map | Third conjunct: for `sq : IsPullback r k i p`, `(Γ ... sq.toCommSq.flip).hom = openImmersionLowerShriekLowerStarExchange (ModuleCat A) sq`. The existing declaration's component formula is exactly the unit for p, the inverse open-base-change comparison, and the counit for r. The flip only changes the orientation of the commutativity proof. |
| Vertical pasting | Fourth conjunct with `s₁.vert_comp s₂`, at every `M`. It first applies J_i2 to the inverse `rightDerivedLowerStarComp r₁ r₂`, then Γ_Q2 at R_r1 M, then R_p2 of Γ_Q1, then `rightDerivedLowerStarComp p₁ p₂`. This is precisely the requested equation with both canonical direct-image compositors inserted. Componentwise equality for every derived object is equality of the natural transformations. |
| Horizontal pasting | Fifth conjunct with `s₁.horiz_comp s₂`, at every `M`. It inserts `mapDerivedCategoryOpenImmersionLowerShriekComp i j`, applies J_j to Γ_Q1, applies Γ_Q2 at J_k M, and contracts with the inverse top open compositor. The order is Γ_Q2 J_k after J_j Γ_Q1. |
| Identity proper edges | Sixth conjunct: `Γ j (𝟙 U) (𝟙 V) j s`, equal to J_j of the source `rightDerivedLowerStarIdIso` followed by the inverse target identity comparison, at every M. |
| Identity open edges | Seventh conjunct: `Γ (𝟙 U) r r (𝟙 W) s`, equal to the bottom `mapDerivedCategoryOpenImmersionLowerShriekId` followed by R_r of the inverse top identity comparison. |
| Arbitrary b and base-changing every vertex | Final conjunct quantifies over `b`, `a`, `c`, `d` and all eight schemes, with the four side faces `sk`, `si`, `sp`, `sr` Cartesian. These are arbitrary models of the four base changes, equivalent to choosing the node's pullbacks and transporting through their unique projection-compatible isomorphisms. They include the canonical chosen pullbacks and every b. The hypotheses proper/open on the primed edges follow from those side faces, so introduce no additional geometric restriction. `s₁` is the induced commutative square, with no Cartesian hypothesis. |
| beta_i and beta_k are inverses of the fixed open-unit mates | The `.inv` of `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso` at `si` and `sk`. The recorded `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate` identifies exactly these termwise comparisons with the open-unit-normalized mates; there is no choice of an isomorphism here. |
| The two specified unbounded exchanges | `exactDerivedBaseChangeMap (ModuleCat A) sp.toCommSq` and the analogous expression for `sr`, exactly the declaration of `def-kun-unbounded-exchange`. |
| Cube equality of natural transformations | Final conjunct is a natural-transformation equality. Left: whisker Γ_Q by P_b, then whisker Ex_p by J_k, then whisker beta_k by R_p1. Right: whisker beta_i by R_r, then Ex_r by J_i1, then Γ_Q1 by P_d. Explicit `Functor.associator` hom/inv terms give common source `(R_r ⋙ J_i) ⋙ P_b` and target `P_d ⋙ (J_k1 ⋙ R_p1)`. Neither Ex_p nor Ex_r is inverted or cancelled. |
| No qc opens, Noetherianity, boundedness, constructibility, Tor amplitude or original Cartesian assumption | None of these classes or predicates occurs in the family binders or theorem. The only original Cartesian assumption appears inside the dedicated normalization clause. |

The theorem states existence with normalization of the whole family, so the same Γ
is used in the representative, pasting and cube clauses. It does not replace a
canonical map by a universally quantified arbitrary map or by a stronger assumption.
The support inclusion equation determines theta, and the formula on every
K-injective representative determines Gamma. No data are selected from a bare
`Nonempty` or unspecified existence theorem.

### Statement dependencies and declarations read

- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`; `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`, `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory`, `DerivedCategory.Plus`, `DerivedCategory.Bounded`, `DerivedCategory.homologyFunctor`, `CategoryTheory.Sheaf.IsTorsion`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; `CategoryTheory.Limits.pullback`, `CategoryTheory.Limits.pullback.fst`, `CategoryTheory.Limits.pullback.snd`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`; `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`; `AlgebraicGeometry.IsProper`, `AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.UniversallyClosed`.
- `def-kun-unbounded-exchange`: `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`; `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`, `AlgebraicGeometry.Etale.exactDerivedSquareUpperStarIso`.
- `lem-weil-pbc-extension-by-zero-exact`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`; `AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek`.
- `prop-weil-pbc-inverse-image-modules-exact`: `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`; `AlgebraicGeometry.etaleInverseImageModulesExact`.
- `lem-sf-etale-proper-open-tensor-square`: `Sheaf.AlgebraicGeometry.EtaleProperOpenTensorSquare`; `AlgebraicGeometry.Etale.etaleProperOpenTensorSquare`.
- `lem-asd-open-base-change-unit-mate`: `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange`; `AlgebraicGeometry.Etale.unit_map_derivedOpenImmersionLowerShriekBaseChangeIso`, `AlgebraicGeometry.Etale.derivedOpenImmersionSquareMap_app`, `AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate`.
- `def-pur-kinjective-complex`: `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean`; `CochainComplex.IsKInjective`.
- `lem-weil-pbc-kinjective-total-derived`: `Sheaf.CategoryTheory.KInjectiveTotalDerived`; `CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`; `CategoryTheory.ringedToposDerivedPushforwardComposition`.
- `lem-cbc-extension-zero-composition`: `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`; `AlgebraicGeometry.Etale.openImmersionLowerShriekComp_coherence`, `AlgebraicGeometry.Etale.openImmersionLowerShriekComp`.

The declarations' signatures and docstrings were read in the corresponding sources.
The generic ringed-topos composition theorem is imported as recorded; the concrete
compositor in the equations is the already published constant-coefficient
`rightDerivedLowerStarComp` in
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`, not a duplicate definition.
The exact open compositor and both identity comparisons are the existing declarations
in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`.
The sheaf inclusion used for the support normalization is the existing declaration
in `WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison`.
The K-injective comparison is the existing `Functor.rightDerivedFunctorObjQIso` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`.
All recorded proof-dependency modules are imported, with plain imports when they
are not also statement dependencies. The declaration docstring carries the full
ten-step proof plan, including the local finite-CD argument and the simultaneous
resolution homotopy that proves the cube.

### Edge cases checked before and after writing

- The zero coefficient ring is allowed. All sheaves and derived objects are zero;
  all equations remain well typed. No `[Nontrivial A]` was introduced.
- Empty schemes and the empty open are allowed. Extension by zero is zero on the
  empty open, and proper pushforward of its zero complex is zero. No nonempty
  hypothesis was introduced.
- Identity proper and identity open edges are covered by explicit unit laws,
  including when both types of edges are identities.
- A genuinely non-Cartesian square is permitted, for example an empty top-left
  scheme over nonempty identity proper right edge with bottom identity open.
  Its comparison concerns zero functors; no original pullback assumption is needed.
- Arbitrary, unbounded complexes and arbitrary K-injective resolutions are allowed;
  no degreewise-injective restriction, boundedness or finite-amplitude hypothesis
  was introduced. Degreewise injectivity is used only in the proof plan before
  the homotopy-invariance reduction.
- A non-quasi-compact open is allowed; the finite-CD proof is local on the target.
  There is no uniform global fibre-dimension bound in the statement.
- The final cube allows identity b and every arbitrary b. Four side pullbacks,
  rather than a Cartesian original square, are exactly what its maps require.
- Every universe is explicitly bound, with scheme universe u and coefficient
  module universe u+1, as in the dependency's existing six-functor encoding.

### Searches for existing statements

The required msearch wrappers were run for this item:

- LeanFinder: `Unbounded derived proper direct image extension by zero non Cartesian square interchange and base change cube`.
  Eight hits, principally `Functor.mapDerivedCategoryFactors(h)`, single-functor
  comparisons and sheaf pushforward composition. None is this normalized proper/open
  theorem or cube.
- Loogle: `NatIso, Functor.rightDerivedFunctor` returned no hits because `NatIso` is
  not a Loogle identifier. A successful follow-up for
  `CategoryTheory.Functor.mapDerivedCategoryCompIso` returned that declaration and
  its factorization/single-functor compatibility lemmas, seven hits; these provide
  the existing exact-functor infrastructure, not the requested theorem.
- LeanSearch: `proper direct image commutes with extension by zero on sheaves`.
  Eight hits: topological/sheaf pushforward comparisons, generic exact functors and
  `Scheme.Modules.pushforwardComp`/`SheafOfModules.pushforwardComp`; no etale
  unbounded proper/open cube.
- Mathlib grep via msearch: `proper.*open|open.*proper` in `AlgebraicGeometry`.
  Twenty-five returned hits on scheme geometry, open-map cancellation and
  morphism-property stability; no derived proper/open interchange theorem.
- Source and project `rg -n` searches for `proper.*[Oo]pen|[Oo]pen.*[Pp]roper|exchange_pfBaseChange_cube|properOpen`
  in `lean/WeilConjectures/SixFunctors` and `lean/Sheaf`, followed by narrower
  proper/open-cube searches. They located the bounded-below
  `properOpenInterchangeCoherence`, the Cartesian
  `openImmersionLowerShriekLowerStarExchange`, the abstract Cartesian
  `CompactSupportFormalism.exchange_pfBaseChange_cube`, and pro-etale finite-CD
  analogues. Their signatures were read: none supplies this normalized ordinary
  unbounded etale family on arbitrary non-Cartesian original squares with all
  the stated coherences. The existing maps and compositors they expose are reused.
- `grep -rn 'lem-pur-etale-proper-open-exchange-cube' lean/WeilConjectures` and the
  corresponding project rg search found no existing declaration attached to the node.

### Validation

The module was compiled through `scompile.py` in both sandbox mode and at its
actual library module path, each under the normal 60-second per-file limit.
Both passed without warnings. The first probe exposed only a parsing issue in
an abbreviation's Pi-type conclusion; parentheses were added around each
natural-isomorphism type. No hypothesis or clause changed during that repair.
There is one postponed theorem, `etaleProperOpenExchangeCube`, matching the item;
the two abbreviations contain real function types. No proof was supplied in stage 2.

No `STATEMENT-DISPUTED` issue or source/node fault was found. The example module
`CompactObject.lean` is currently withdrawn and contains no declarations; its node
and the current stage-2 module-mode/public-section rules were read.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
