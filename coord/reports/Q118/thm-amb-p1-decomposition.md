## Worker report

The module `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` states the current
ordinary-small-etale finite-coefficient projective-line decomposition, with its
specified ordered components and arbitrary-base compatibility. The sole theorem
has proof `sorry`; all helper definitions contain actual data. No other DAG node
is stated, repaired, or rebound.

The previous attempt's blocker is obsolete: the current statement dependency list
no longer names `def-coefficient-twists-detailed`. The Q52 stage-1 repair supplies
ordinary finite etale twists and the actual scalar Kummer interface. I read that
repair, the current main-20261015 node statement and proof, and the older master
statement. The latter explicitly says ordinary derived categories. The withdrawn
pro-etale coefficient-twist binding is neither imported nor restored here.

Hypotheses and clauses are rendered as follows:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Integer N at least one | `(N : ℕ) (hN : 0 < N)` |
| Finite commutative coefficient ring | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| NA=0 | `(hA : (N : A) = 0)`; equivalent to annihilating every A-element |
| Noetherian scheme S | `(S : Scheme.{u}) [IsNoetherian S]`; Mathlib Noetherian.lean identifies this with a finite affine cover by Noetherian spectra |
| N invertible on S | `hS : IsUnit (N : Γ(S, ⊤))`; local inverses glue uniquely, so this is the stated local-ring condition |
| P=P1_S and its projection q | `ProjectiveLine S` and `ProjectiveLine S ↘ S`; the recorded base-change projective-space construction |
| Ordinary small etale unbounded module derived category | `DerivedCategoryModule A T`, through the recorded `ordinaryFinitePullback`, `ordinaryFinitePushforward`, and `ordinaryFiniteTensor` abbreviations |
| Positive twist mu_N tensor A | `ordinaryFiniteLine A N hA T`, the existing `finiteEtaleTateLine` placed in degree zero |
| Negative twist as sheaf Hom | `Scheme.finiteEtaleTateSheaf A N T hA (-1)`, definitionally internal Hom of the positive line into the constant unit |
| K=A_S(-1)[-2] | `p1DecompositionTwist A N hA S (-1) (-2)` |
| O(1) transition e0=t^-1 e1 | `ordinaryFiniteP1ChernSpec` refers to the actual Picard class of `ProjectiveSpace.twist (ULift (Fin 2)) S 1`, with exactly that transition |
| Actual Kummer scalar-extended Chern morphism c | The existential `c` satisfies `ordinaryFiniteP1ChernSpec`; this requires its abelian-cohomology realization to equal the prescribed Kummer boundary followed by the scalar root map z↦1 tensor z. It does not substitute an arbitrary class or add a Chern-class hypothesis |
| h is the specified adjoint | `p1DecompositionChernAdjoint`: inverse tensor unit, tensor with c, normalized negative-twist pullback, evaluation, then `derivedUpperStarLowerStarAdjunction.homEquiv` |
| Evaluation | `p1DecompositionEvaluation`: cancel shifts -2 and 2, symmetry, the canonical flat degree-zero tensor comparison, and the actual `ihom.ev`. The proof of flatness is extracted from the recorded normalized product isomorphism; no flatness hypothesis on A is added |
| Unit component 1 | `p1DecompositionUnit`, the adjoint of the canonical constant-object pullback comparison |
| Ordered map (1,h) is an isomorphism | `IsIso (p1DecompositionMap ... c)`, with that map defined by `biprod.desc` of the two specified components |
| Every base-change morphism | `∀ (S' : Scheme.{u}) (g : S' ⟶ S)` with no Noetherian or nonemptiness assumption on S' |
| Same construction over S' | `c'` has the identical Kummer specification; `p1DecompositionMap ... S' ... c'` is an isomorphism |
| Proper exchange identifies the pullback with that map | The final equation composes pullback of `(1,h)` with `ordinaryFiniteP1Exchange` and the constant-object comparison, and equates it with `p1DecompositionSourceMap` followed by `(1,h')` |
| Canonical source comparison | `p1DecompositionSourceMap` is built from the images of the two biproduct projections, constant transport, and normalized signed-twist transport |

The compact `P1DecompositionTwistTransport` record retains the roots inclusion,
pure-tensor, tensor-power, zero-exponent, negative evaluation and inverse-product
equations from `Scheme.etaleFiniteTwistPullback`. Its constructor projects that
theorem into this constrained record before selecting its uniquely normalized data.
The sheaf pullback and product helpers access that record; they do not repeatedly
reduce the much larger full theorem type. In particular the product at (1,-1) used here is the prescribed
internal-Hom evaluation. These are determined canonical comparisons, not a
selection from a bare existence or Nonempty assertion. The Chern specifications
likewise determine the module-derived morphisms through the ordinary Ext/cohomology
realization; the existential formulation exposes this characterization explicitly.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveLine`,
  `ProjectiveSpace.map`, `ProjectiveSpace.isPullback_map`, projection and properness.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `DerivedCategoryModule`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `upperStar`, `lowerStar`,
  and `upperStarLowerStarAdjunction`; their upstream derived adjunction and shifts.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`, its symmetry,
  `derivedTensorShiftIso`, `singleFunctorObjTensorIso`, and `derivedTensorSingleUnitIso`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `Scheme.finite_etale_torsion_twist_line` (positive-line flatness in the proof route).
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `Scheme.kummerSequence_shortExact`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `exactDerivedBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `Scheme.etaleFiniteTwistPullback`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`: `Scheme.finiteEtaleTateSheaf`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`: `ordinaryFiniteP1ChernSpec`,
  `ordinaryFiniteP1KummerClass`, `ordinaryFiniteClass`, constant unit and positive line.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`: `ordinaryFinitePullback`,
  `ordinaryFinitePushforward`, `ordinaryFiniteTensor`, `ordinaryFiniteUnitPullback`,
  `ordinaryFiniteP1Exchange`. Its already-landed node
  `def-asd-ordinary-finite-p1-arrows` is added to stmt_deps; no node is restated.

All stated proof-dependency modules are imported through this interface or directly:
`OrdinaryFiniteP1Adjunction`, `ProperProjectionFormula`, `ProperUnboundedBaseChange`,
`OrdinarySupportedCartierKummer`, projective-space properness, Noetherianity, the
finite twist theorem and exact exchange. The theorem docstring gives both complete
DAG proof steps, including the component adjunction calculation and the arbitrary
base-change Cartier/unit comparison.

Edge cases checked mathematically before writing: N=1 forces A=0, which is
admitted; A=0, empty S and empty S' give the zero categories/maps; disconnected
or nonreduced Noetherian S is admitted. A=Z/2 and N=4 tests non-flat coefficients:
no A-flatness over Z/N is assumed. A=Z/6 on a Z[1/6]-scheme and product coefficient
rings are retained. S' may be non-Noetherian and nonreduced. The infinity equation
is a polynomial variable, so Cartier pullback remains valid over all those rings.
Identity base change and the geometric-field case retain the normalized unit and
degree-two Kummer component. The scheme universe u and coefficient universe u+1
are exactly those of the recorded six-functor encoding, with no additional equality.

Searches actually made with msearch.py:

- LeanFinder: “projective line etale derived direct image decomposes as A plus
  inverse Tate twist shifted by minus two, compatible with arbitrary base change”:
  eight hits on etale morphism stability, etale algebras and Kaehler base change;
  no decomposition statement.
- Loogle: `AlgebraicGeometry.Proj, CategoryTheory.IsIso`: zero hits.
- Mathlib grep: `projective.bundle|firstChern|chernClass|TateTwist`, restricted to
  AlgebraicGeometry: zero hits.
- Earlier diagnosis searches: LeanFinder “coefficient Tate twist finite etale
  sheaf A(1) projective line decomposition” returned projective-spectrum charts
  and affine-space definitions; Loogle names `coefficientTateTwists,
  rationalComplexTwist, algebraicClosureComplexTwist` rejected an unknown name,
  recorded as unavailable rather than absence. Grep for those names found no
  Mathlib/upstream declaration; the shared CoefficientTwistsDetailed source is
  explicitly withdrawn and is not this ordinary finite-coefficient notion.
- `rg` by the item id in the upstream WeilConjectures source found no exact
  statement. Projective-space and derived/base-change searches found chart,
  projective-line exchange and abstract Tate interfaces. Shared-side searches
  found the existing normalized twisted adjunction theorem, which includes
  only Noetherian-to-Noetherian base-change compatibility and therefore does not
  state this theorem's arbitrary-base clause. It is used as the proof input.

No statement correction, new node, dependency repair, STATEMENT-DISPUTED claim,
axiom, private notion, local notation or local instance is introduced.

Validation uses only scompile.py and the required deliver2.py --no-push wrapper.
The initial import typo was corrected from the node record. A timeout was repaired
by projecting the large finite-twist existential into the compact normalized record;
that record and extraction compile cleanly in isolation. The evaluation is factored
into typed degree-zero tensor, degree-zero evaluation and shift-cancellation
definitions to avoid repeating their kernel conversions; this entire prefix
compiles cleanly in 30.4 seconds (sandbox) and 29.0 seconds (library). The actual shift instance
is made explicit inside the derived pullback construction, without a file-local
instance or any change of functor. The exponent-pullback helper is the existing
ring-homomorphism unit map with the natural-number cast transport; its scoped
defProp linter exception reflects that it is a proof-term construction, with no
postponed mathematical lemma.
The independent second reading is left to the next worker.

The complete module passed the prescribed local-overlay scompile.py check cleanly:
52.6 seconds for the sandbox check and 44.1 seconds for the library-path check,
both within the unchanged 60-second limit. The subsequent change only expands
the proof docstring with the node's two explicit counit/triangle equations and
the divisor-unit exchange equation. The mandatory delivery dry run recompiles
that final source and runs server preflight.

## Second reading by Q118

I am the independent second reader; I did not write the worker's statement. I read
both the sandbox node and module, the current shared node, all statement-dependency
records, their declaration signatures and the relevant construction bodies. There
is no repair note for this item, no new node, no dependency module, and no stage-2
`statement_change`. The shared node's already-reviewed Q52 stage-1 revision is the
statement being formalized; this delivery does not change its mathematical fields.

Source check: I opened the master `sec-smooth-purity/sk-prop-sf-cbc/`
`thm-amb-p1-decomposition.md`, the main-20261015 statement, and both proof steps in
the node. The master explicitly specifies ordinary derived categories and arbitrary
change of base; its general-A proof uses scalar extension. I also opened Stacks
`etale-cohomology.tex`, the Kummer section (03PK), `lemma-kummer-sequence` (03PL,
lines 2841 onward), and `lemma-proper-base-change-mod-n` (0F0C, lines 18887 onward).
The former assumes invertibility of N, not a field, reducedness or Noetherianity;
the latter allows arbitrary g and unbounded complexes, with no Noetherian S'. The
node's finite torsion-ring extension is the recorded proper-base-change dependency.
03Q1 is the stalk-pullback lemma, used by the normalized twist dependency. These
sources introduce no additional standing hypothesis missing from the Lean.

My independent inventory, with the Lean rendering and verdict for each item:

| Object, hypothesis or conclusion in the node | Lean rendering and verdict |
| --- | --- |
| Integer N at least 1 | `(N : ℕ) (hN : 0 < N)`: exact. N=0 is intentionally excluded. |
| A finite commutative ring, annihilated by N | `(A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)`: exact, including the zero ring. N times every element vanishes iff N times 1 does. |
| S Noetherian in the finite-affine-cover sense | `(S : Scheme.{u}) [IsNoetherian S]`: exact; I checked Mathlib `IsNoetherian`, its locally-Noetherian/compact fields and its finite-affine-cover equivalence. |
| N invertible on S | `hS : IsUnit (N : Γ(S, ⊤))`: exact. Stalkwise inverses glue uniquely; conversely a global inverse restricts to every stalk. |
| P=P1_S and q | `ProjectiveLine S` and `ProjectiveLine S ↘ S`: exact. Upstream `ProjectiveLine` is projective space on `ULift (Fin 2)`, and `ProjectiveSpace.isPullback_map` supplies the actual Cartesian square. |
| Ordinary small-etale unbounded module-derived categories | `DerivedCategoryModule A T`, used by `ordinaryFinitePullback`, `ordinaryFinitePushforward` and `ordinaryFiniteTensor`: exact. I read the coefficient abbreviation and all three wrapper bodies; these are the recorded derived functors, not bounded or completed replacements. |
| A_T(1)=mu_N tensor A_T | `ordinaryFiniteLine` uses `Scheme.finiteEtaleTateLine`: exact. I read its presheaf scalar extension and sheafification; its A tensor mu order is the canonical symmetry of the node's order. |
| A_T(-1)=Hom(A_T(1),A_T) | `Scheme.finiteEtaleTateSheaf ... (-1)`: exact, by its `.negSucc 0` clause and the existing `ihom`. |
| O(1) with e0=t^-1 e1 | The `ProjectiveSpace.twist ... 1` inside `ordinaryFiniteP1KummerClass`: exact. I checked `twistOneSection`'s transition rule T_i=(T_i/T_j)T_j, which for i=0,j=1 is precisely t^-1. |
| c is the scalar Kummer Chern morphism | `∃ c, ordinaryFiniteP1ChernSpec ... c ∧ ...`: exact. I opened `ordinaryFiniteClass`, `ordinaryFiniteRootMap` and `ordinaryFiniteP1KummerClass`. The prescribed value is the actual Kummer boundary of the Picard class, followed by z↦1 tensor z, not a free generator or unconstrained class. The realization Hom_D(A,F[2])→H^2(forget F) is the canonical equivalence: in degree zero Hom_A(A,-) is sections, and its derived comparison remains the same after exact forgetting (the free-A/forget adjunction). Thus this predicate determines c, and the existential does not weaken its specification. |
| K=A_S(-1)[-2] | `p1DecompositionTwist A N hA S (-1) (-2)`: exact; the underlying sheaf is put in degree zero before shifting. |
| h is the stated adjoint | `p1DecompositionChernAdjoint`: exact. Its body applies the inverse right-unit comparison, tensors with c, applies the normalized negative-twist pullback, evaluates, and uses the recorded derived adjunction's `homEquiv`. |
| Evaluation in h | `p1DecompositionEvaluation` cancels shifts -2,+2 via `derivedTensorShiftIso`; `p1DecompositionDegreeZeroEvaluation` uses symmetry, `singleFunctorObjTensorIso`, then the actual `ihom.ev`. Exact. Flatness comes from the normalized inverse-product isomorphism via the existing `flat_of_tensorIso`; no coefficient-flatness hypothesis is introduced. Both shifts are even, so no alternative Koszul sign is hidden. |
| Unit 1:A_S→Rq_*A_P | `p1DecompositionUnit` is the adjunct of the canonical constant-object pullback isomorphism: exact. |
| Ordered (1,h) is invertible | `p1DecompositionMap` is literally `biprod.desc` of the unit first and h second, and the conclusion is `IsIso` of that map: exact. This is not existence of an unrelated decomposition isomorphism. |
| Every g:S'→S | `∀ (S' : Scheme.{u}) (g : S' ⟶ S)`: exact. There is no Noetherian, reduced, finite-type, flat or nonempty assumption on S'. |
| Same construction over S' | `c'` satisfies the identical `ordinaryFiniteP1ChernSpec`; `IsIso (p1DecompositionMap ... S' ... c')` uses the same recipe: exact. Invertibility of N is transported by the existing `IsUnit.map` and `map_natCast`, not assumed anew. |
| Proper exchange identifies the pulled-back isomorphism | The final equation first pulls back the specified map, then applies `ordinaryFiniteP1Exchange` and the constant-object comparison; it equals `p1DecompositionSourceMap` followed by the specified map over S': exact, with arrows in the correct direction. I read the exchange body: its middle arrow is the dependency's exact unbounded mate, conjugated by the canonical exact/left-derived comparisons. |
| Identification of the two source summands | `p1DecompositionSourceMap` uses the pullbacks of `biprod.fst` and `biprod.snd`, followed by the constant and signed shifted-twist comparisons: exact, with the unit summand still first. |

The compact `P1DecompositionTwistTransport` is a computational projection of
`Scheme.etaleFiniteTwistPullback`, not a private replacement for the finite twists.
I checked its roots-inclusion equation, pure-tensor equation, exponent-zero and
power equations, negative evaluation equation and (1,-1) product normalization
against the full dependency signature. The roots comparison is determined because
the kernel inclusion is mono and inverse image is exact; pure tensors generate the
scalar-extended sheaf locally; the zero/power and negative-evaluation equations
then determine all signed comparisons. The product used for flatness has exactly
the internal-Hom evaluation as hom. Consequently `Classical.choice` selects
uniquely normalized data, rather than an arbitrary map or bare Nonempty isomorphism.
No definition has sorry data. Its scope is the concrete arrows of this theorem,
so no additional independent definition node is needed.

Edge cases: N=1 forces A=0 and is retained; A=0 with other N is also retained.
Empty S and empty S' are allowed, and there is no implicit nonemptiness instance.
The coordinate index is exactly two, not a varying index set, so an empty-index
case is not part of this node. The zero derived object is not excluded. The
characteristic condition is solely invertibility of N on S; A may have any
characteristic dividing N, e.g. A=Z/2 with N=4. In particular no flatness over Z/N
or field hypothesis appears. Disconnected/nonreduced S and non-Noetherian,
nonreduced S' remain covered. Identity g and empty-base g use the same normalized
comparisons. Universe u is quantified, Scheme has its recorded small site with
objects in u+1 and morphisms in u; ModuleCat uses coefficient universe u+1 as
`DerivedCategoryModule` requires. No equality of site object/morphism universes
or independent smaller test-object universe was added. Every finite coefficient
ring can be placed in this common encoding, with no restriction on its algebra.

Independent H4 searches, using different wording from the worker:

- `msearch.py ... leanfinder "projective line decomposition ordinary finite etale derived category"`:
  eight hits on Scheme.Etale and standard-etale algebra, no decomposition theorem.
- `msearch.py ... loogle '"ProjectiveLine", "IsIso"'`: zero hits.
- `rg -i 'projective.*(decompos|cohomology)|p1.*decompos|chern|tateTwist'`
  in Mathlib AlgebraicGeometry and CategoryTheory/Sites: no exact match.
- `rg` for projective decompositions, P1 decompositions, Chern classes and Tate
  evaluations in upstream WeilConjectures and shared lean/Sheaf: found coherent
  O(n)-cohomology (a different category), abstract Tate orientations (different
  data), supported Kummer maps (a different source), and the recorded
  `OrdinaryFiniteP1Adjunction`/`OrdinaryFiniteP1Data`. I opened the latter: its
  decomposition is A_S(1)[2] plus A_S with twisted target, and its base-change
  quantifiers require Noetherian S'. Its `ordinaryFiniteP1DecompositionSourceMap`
  likewise compares those different summands. None is this untwisted-target,
  negative-twist, arbitrary-base statement or its source comparison. Existing
  coefficient, twist, tensor, unit and exchange notions are reused.

Mismatch repaired: the worker had introduced
`p1DecompositionExponentPullback : ... → IsUnit ...` as a proved Prop-valued `def`
with `linter.defProp` disabled. This is unnecessary proved material in a stage-2
statement module. I removed that declaration and its linter suppression, and
replaced every use by the existing proof `IsUnit.map`, transported along the
existing `map_natCast` equality. No theorem was added, and the only theorem body
is still `sorry`. I removed the deleted name from `lean.declarations` and copied
the final theorem signature verbatim into `lean.statement`. These changes affect
proof arguments only, not the mathematical statement, canonical maps or quantifier
order; no statement correction or citer audit is required. All other helpers,
objects, hypotheses and conclusion clauses were right and were left in place.
The worker's earlier explanation of the deleted helper is superseded by this
paragraph.

H8/H9: module and every remaining declaration have source/blueprint docstrings;
the theorem's docstring includes both full proof steps and the counit/triangle
and Cartier/unit calculations. All recorded proof-dependency modules are imported
directly or through the existing canonical-arrow interface. No axiom, private
notion, file-local notation or file-local instance is added. The `letI` inside
the definition of shifted pullback is the library's existing CommShift structure,
not a new hypothesis or a `let` binder in a theorem statement. All universes and
variables are explicitly bound, all lines are at most 100 characters.

Additional independent LeanSearch check: `msearch.py ... leansearch "ordinary etale
cohomology projective line canonical splitting with negative Tate twist and proper
base change"` returned eight hits on proper/etale base-change stability, etale
algebras and etale sites. I read their returned signatures: none states the
splitting, Chern normalization, or compatibility equation. This completes the
LeanSearch, LeanFinder/Loogle and source-grep searches.

Validation of the final edited module through the prescribed `scompile.py`:
server sandbox check clean in 33.9 seconds and library-path check clean in 33.7
seconds, with the unchanged 60-second per-file limit. No warning or error was
printed. The remaining theorem's proof is exactly `sorry`; the node's
`lean.statement` matches its signature including newlines. The mandatory
`deliver2.py --no-push` server preflight and delivery follow this second reading.
