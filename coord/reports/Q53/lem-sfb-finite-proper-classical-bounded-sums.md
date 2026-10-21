## Worker report

The module `Sheaf.SixFunctors.FiniteProperClassicalBoundedSums` states all clauses of
`lem-sfb-finite-proper-classical-bounded-sums` in six component theorems. Every proof
is `by sorry`. There are no new definitions, new nodes, dependency repairs, or statement
corrections. The primary declaration is
`AlgebraicGeometry.ProEtale.finiteProperClassical_bounded_sum_factorization`.

Sources read: the complete item (all nine proof steps), every statement dependency's
statement and Lean record, the recorded declaration signatures and docstrings, and
blueprint main-20261015 `sec-six-functors-basics/sk-prop-ctf-finite-proper/`
`sk-prop-ctf-finite-proper-localizing.proof.md`, especially Transfer. Also read Stacks
`injectives.tex`, `lemma-derived-products` (07D9), and `etale-cohomology.tex`,
`lemma-proper-mod-n-direct-sums` (0F0D). The latter is deliberately not substituted for
the explicit hypothesis on E: this item assumes the finite-ring etale coproduct theorem.
There is no repair note for this item.

### Categories, coefficients, and universes

`A : Type (u + 1)` with `[CommRing A] [Finite A] [TopologicalSpace A]
[DiscreteTopology A]` renders exactly finite discrete commutative coefficients.
`X Y T : Scheme.{u}` and `I : Type (u + 1)` put site objects, coefficients and the
whole small family in the common universe of the established comparison API. Site
morphisms retain universe u. No equation between the site object and morphism
universes is imposed.

Ordinary constant-ring module sheaves use the established fixed-ring presentation
`Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)` and
`Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)`; D is `DerivedCategory` of these
abelian categories. The etale abbreviation is the recorded
`Etale.DerivedCategoryModule A T`. On the pro-etale side the recorded
`finiteCoefficientRealization T A` is the canonical exact equivalence to
`FiniteCoefficientModules T A`, the continuous-function coefficient presentation of
`def-weil-pbc-proetale-modules`. The statement uses that very functor and the recorded
`IsClassicalModuleComplex`, rather than defining a second classical predicate.
In particular, the condition on L is
`IsClassicalModuleComplex ((finiteCoefficientRealization T A).mapDerivedCategory.obj L)`.
The realization changes the presentation of the scalar action; its underlying module
sheaf is the sheafification of the same fixed-scalar sheaf, hence has its original
underlying sheaf and continuity maps. This does not restrict the allowed classical
objects. Its exactness identifies cohomology and standard degree bounds in the two
presentations.

The total functors are exactly
`E = (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor` and
`G = (ProEtale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor`, the ordinary
unbounded K-injective direct images in this presentation, and
`F_T = (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory`.
No arbitrary functor, coefficient identification, or comparison map is a hypothesis.
The existing `CategoryTheory.derived_hasCoproducts` theorem is registered as an
instance so the standard notation `∐`, `Sigma.ι`, and `sigmaComparison` uses its
ambient derived coproduct construction. No new coproduct construction is introduced.

### Hypothesis-by-hypothesis and clause-by-clause correspondence

- Finite commutative discrete A: the five coefficient binders above occur in every
  component theorem.
- Proper f: `(f : X ⟶ Y) [IsProper f]` in the factorization theorem. The preceding
  structural clauses are stated for arbitrary T, so apply to X and Y; equivalently
  each scheme occurs by taking its proper identity morphism. Those clauses need no
  hypothesis about a particular f.
- Classical cohomology, without boundedness, for the closure assertions:
  `_hL` uses the exact recorded predicate after realization, in every degree.
- Every small ambient coproduct is classical:
  `finiteProperClassical_coproduct_closure` concludes that predicate for `∐ L`.
- Both good truncations are classical:
  `finiteProperClassical_truncation_closure` concludes the two predicates for
  `(DerivedCategory.TStructure.t.truncLE n).obj L` and `.truncGE n`.
- Natural cohomology and good-truncation coproduct comparisons:
  `finiteProperClassical_coproduct_cohomology_truncations` asserts
  `PreservesColimitsOfShape (Discrete I)` for every homology functor and both
  truncation functors. This is preservation of the specified cofans, so the
  isomorphisms are the canonical, natural `sigmaComparison` maps. Its last two
  conjuncts explicitly give compatibility with `truncLEι` and `truncGEπ`. The LE
  equation is sum(truncLE L) -> truncLE(sum L) -> sum L equals the sum of the
  component inclusions. The GE equation is sum L -> sum(truncGE L) -> truncGE(sum L)
  equals the canonical quotient of sum L.
- Exact termwise nu* preserves all small sums:
  `finiteProperClassical_comparison_preservesCoproducts`, universally quantified
  over I, asserts precisely preservation by `F_T`.
- E preserves all small sums: `_hE : ∀ J : Type (u + 1),
  PreservesColimitsOfShape (Discrete J) E`, an implication hypothesis of the
  factorization theorem, not an extra theorem asserting this premise.
- Any integers a <= b: `(a b : ℤ) (_hab : a ≤ b)`; all lower/upper bound hypotheses
  are `(L s).IsGE a` and `(L s).IsLE b`, the standard t-structure predicates.
- Existence of etale origins in exactly [a,b]:
  `finiteProperClassical_bounded_origins` returns a family
  `B : I → Etale.DerivedCategoryModule A X`, its two bounds for every s, and
  `Nonempty (∀ s, F_X.obj (B s) ≅ L s)`. Nonempty only states existence of these
  isomorphisms; it defines no data by choice from a postponed theorem.
- Every allowed origin choice: the factorization theorem universally binds B, its
  interval condition `_hB`, and the actual family `i : ∀ s, F_X.obj (B s) ≅ L s`.
  It is not restricted to origins chosen by the previous theorem.
- The canonical theta_B and theta_sum: existential isomorphisms `theta` and `Theta`
  have forward maps equal to `unboundedDirectImageComparisonMap A f (B s)` and
  `unboundedDirectImageComparisonMap A f (∐ B)`. This existing map is the derived
  adjunction mate of the specified pullback comparison. The module
  `UnboundedDirectImageBoundedBelow` was read: it identifies its bounded-below
  restriction with the D+ canonical comparison via derived compatibility
  isomorphisms. Thus these equations select the node's theta, not a bare unspecified
  isomorphism. The existence of these isomorphisms also asserts their invertibility.
- The canonical t: the existential `t : F_X.obj (∐ B) ≅ ∐ L` satisfies
  `F_X.map (Sigma.ι B s) ≫ t.hom = (i s).hom ≫ Sigma.ι L s` for every s.
  F_X preserves the cofan, so these equations uniquely specify t. This existential
  presentation of the uniquely characterized isomorphism is equivalent to the
  node's instruction to define t; it introduces no extra choice-dependent claim.
- alpha_Y is exactly `sigmaComparison F_Y (fun s ↦ E.obj (B s))`, in the direction
  sum F_Y(E B_s) -> F_Y(sum E B_s). Inverse-image preservation makes it invertible.
- sigma^E_B is exactly `sigmaComparison E B`.
- The specified factorization is the main equality in the last theorem. Lean `≫`
  runs left to right. Its first factor is `Sigma.desc` of
  `(G.mapIso (i s)).inv ≫ (theta s).inv ≫ Sigma.ι ... s`, exactly the sum of
  theta_s inverse after G(i_s) inverse. Its remaining factors in order are alpha_Y,
  F_Y(sigma^E_B), Theta.hom and G(t.hom). Reversing to ordinary right-to-left
  notation gives precisely the displayed formula in the node.
- Actual sigma_L is invertible: the following `IsIso (sigmaComparison G L)` conjunct.
- Its s-th coprojection gives G(iota'_s): the final explicit `Sigma.ι ... s ≫
  sigmaComparison G L = G.map (Sigma.ι L s)` conjunct. This clause is required by
  the node even though it is also the defining property of the canonical comparison.
- Empty families: no index type has `[Nonempty I]`; sums and the defining equations
  remain present for the empty type. The comparison at sum B then is at zero.
- No unbounded etale/classical equivalence: the only origin theorem explicitly
  requires the common finite bounds [a,b]. Arbitrary unbounded inputs appear only
  in the closure and cohomology/truncation clauses.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  the recorded `IsSeparated` diagonal and `UniversallyClosed` base-change definitions
  were also read. Finite type and separated proof modules are imported.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientModules`, `finiteCoefficientRealization`,
  `finiteCoefficientRealization_exact`, its additive/finite-limit/finite-colimit
  instances, and `finiteCoefficientRealization_isEquivalence_ring`.
- `Sheaf.SixFunctors.ClassicalDefinition`: `IsClassicalModuleSheaf` and
  `IsClassicalModuleComplex`, with cohomology in the recorded module category.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison` and its module specialization; the actual fixed-ring
  functor `comparisonUpperStar` is its established coefficient presentation.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, `DerivedCategory`, and `DerivedCategory.homologyFunctor`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its universal unit/ObjIso;
  on these Grothendieck categories the existing `Functor.rightDerivedFunctor` is
  the total K-injective version, used by both E and G.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: its documented reuse of
  standard good truncations and their maps. The unrelated telescope predicate is
  not substituted for truncation. `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
  supplies `TStructure.t`, `DerivedCategory.IsGE`, `IsLE`, `isGE_iff`, `isLE_iff`;
  `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT` supplies `truncLEι`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`: `directImageComparison`.
  `Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap` supplies
  `unboundedDirectImagePullbackIso`, `unboundedDirectImageComparisonMap` and its
  naturality identity. These are existing constructions, not new helpers.
- Proof imports: `AlgebraicGeometry.ProEtale.classicalDerivedEquivalence` from
  `Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`,
  `AlgebraicGeometry.ProEtale.proEtaleClassicalSheavesModules` from
  `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`, and
  `AlgebraicGeometry.ProEtale.boundedBelowComparison` from
  `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`; also
  `SheafOfModules.isGrothendieckAbelianOfUniverses`,
  `DerivedCategory.isColimit_mapCocone_grothendieckSum`, and
  `Functor.mapDerivedCategoryHomologyFunctorIso` / `isGE_mapDerivedCategory_obj`.
  All stated proof-dependency modules are imported.

### Edge cases and searches

Checked the empty index family, zero complexes, the zero coefficient ring, empty
schemes, a=b (including degree zero), arbitrary negative endpoints, and arbitrary
unbounded classical complexes in the closure clauses. There is no Nontrivial,
nonempty, characteristic, constructibility, fibre-dimension, finite-type-over-field,
or uniform cohomological-dimension hypothesis. Properness is the sole geometric
hypothesis in the transfer. For an empty family every coprojection equation is
vacuous but the canonical map remains the unique map from zero, not an omitted case.
The file binds universe u and every variable explicitly with autoImplicit false.

Executed searches using msearch.py:

- `leanfinder`: “Classical proetale complexes closed under coproducts and good
  truncations with bounded etale origins and canonical pushforward coproduct
  comparison factorization”. Eight hits, mostly scheme/etale infrastructure;
  no matching theorem.
- `loogle`: `CategoryTheory.Limits.sigmaComparison, DerivedCategory`. Zero hits.
- `grep`, Mathlib/CategoryTheory:
  `sigmaComparison|[Cc]lassical.*[Cc]oproduct|[Cc]oproduct.*[Cc]lassical`.
  Twelve hits, including the generic canonical coproduct comparison and preservation
  criteria. Read `Shapes/Products.lean` and `Preserves/Shapes/Products.lean`;
  these supply the comparison used here, not the theorem of this node.
- `leansearch`: “Coproducts of classical proetale complexes are classical and proper
  derived pushforward preserves coproducts of uniformly bounded classical complexes”.
  Eight hits on scheme coproducts and additive finite-coproduct preservation;
  none states the present assertions.

Direct rg searches in `lean/WeilConjectures`, `lean/Sheaf` and the upstream name
index for the item id, classical coproduct/bounded-sum words, and the new declaration
prefix found no exact statement or name collision. Existing
`FiniteProperClassicalCoproducts.lean` states only preservation, assumes an additional
universal fibre-dimension bound, and has no closure/origin/factorization clauses; it
is not this node. Reused its ordinary finite-coefficient infrastructure only.
`UnboundedDirectImageComparisonMap.lean` gives exactly the canonical map needed for
the factorization. No new definition or duplicate construction was necessary.

Validation: scompile.py compiled both its sandbox view and the actual library module
without diagnostics after correcting two parentheses in the truncation preservation
signature. The final wrapper dry run and delivery results are recorded below.

Delivery dry run: `deliver2.py Q53 lem-sfb-finite-proper-classical-bounded-sums
--no-push` returned `OK`: commit `9d686cf7a4e` passed the server preflight and compiled.
Only the module, this node's lean record, and this report are included.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
