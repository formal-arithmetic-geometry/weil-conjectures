## Worker report

The new module `Sheaf.Paper.IntegralSemilinearGermSquare` states the completed
one-step integral germ square. The node's mathematical statement is unchanged.
Every new theorem has proof `by sorry`; definitions contain actual compositions
of existing maps and isomorphisms. The main theorem is
`WeilConjectures.integralSemilinearGermSquare`.

Sources read: Deligne, Weil II, printed pp. 150--153, (1.1.3), (1.1.7),
(1.1.10)--(1.1.14), and Stacks `sites-cohomology.tex`,
`remark-base-change` (07A7). The current blueprint proof
`lem-a1-finite-boundary-weights.proof.md` was read: geometric-point evaluation
identifies the summands and transport stabilizes them. The finer completed-system
identities are the agent refinement explicitly identified in this node's source.

### Hypotheses and objects

| Node text | Lean rendering |
| --- | --- |
| Global finite-field datum `(p,a,q,k₀,k)` | `D : FiniteFieldDatum.{u}`, with its prime, positive exponent, cardinality, field and algebraic-closure fields |
| Prime `l ≠ p` | `(l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]` |
| Finite extension E of Q_l inside a fixed algebraic closure | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`, and explicit `(Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (_ι : E →ₐ[ℚ_[l]] Ω)` in the main theorem; the algebra hom is injective since E is a field |
| Valuation ring and uniformizer | Those already used by the imported integral coefficient categories: `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`; no second choice |
| Proper finite-type k₀-scheme | `(Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]`; Mathlib proper supplies locally finite type and quasi-compactness |
| Y, s, a_Y | `(D.geometricFiber Y₀).left`, `Spec (.of D.k)`, `(D.geometricFiber Y₀).hom` |
| h = Spec(gamma), g = id times h | `(frobeniusPointIso D).hom`, `(D.geometricFrobenius Y₀).hom`; the former uses the same `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic` as the latter |
| Completed integral constructible category | `sfIntegralConstructibleCategory l E`, the full subcategory of the derived category of completed coefficient modules |
| A, P, Q, Z_x | `constructibleIntegralPullback l E` at a_Y, g, h, x respectively; `integralDerivedPullback` is used for the same arrows under the full inclusion |
| R | `properFrobeniusIntegralFunctor D Y₀ l E false`, the direct recipe, whose underlying object/action is `directImageFunctor` / `integralDirectImage` / `realize (systemDirect ...)` |
| Ordinary counit epsilon | Existing `ProperSemilinearGerms.integralCounit`: pullback realization, reconstruction counit, system geometric counit, inverse completeness unit |
| Actual completed exchange E_M | Existing `(properFrobeniusIntegralExchange D Y₀ l E false).app M`; the direct recipe is `directIntegral`, using `integralExchange` of the actual `systemExchange` |
| A k-point x | Explicit arrow `x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left` and `hx : x ≫ a_Y = 𝟙 _` |
| u_x inverse | `IntegralSemilinearGerms.unitInverse`, inverse of the specified `integralComparisonUnit`, the equality `hx.symm`, then the published `integralPullbackComposition` |
| theta | `IntegralSemilinearGerms.theta`, inverse c_(a,h), equality from `structure_square`, then c_(g,a) |
| x_1 and b_(1,x,M) | Existing `movingPoint D Y₀ x 0` is g x h^-1; `IntegralSemilinearGerms.square` is inverse c_(h,x_1), the actual moving-point equality, then c_(x,g) |
| v_x^M | Existing `ProperSemilinearGerms.integralGerm`; its body is exactly u_x inverse followed by Z_x(epsilon_M), in the full subcategory |

The closure universe `v` is independent of the scheme/coefficient universe `u`.
No finite-Tor, smoothness, nonemptiness, or Weil-structure binder is introduced.

### Every conclusion

* `IntegralSemilinearGerms.point` is h^(-j) followed by x followed by g^j,
  for every integer j. `point_properties` asserts both `point j ≫ a_Y = id`
  and `h ≫ point (j+1) = point j ≫ g`. These are exactly that the x_j are
  k-points and g x_j = x_(j+1) h. Its `@id (Aut ...)` only retains the existing
  automorphism-group type of the point isomorphism for integer powers.
* `structure_square` states the background equality g a_Y = a_Y h using Lean's
  left-to-right composition order. It supplies the equality proof used in theta
  and in the system exchange, rather than adding an assumption on the square.
* The main theorem's first conjunct is integral germ naturality for every pair
  M, M' and every derived arrow f. In Lean's order it reads
  `v_M ≫ Z_x.map f = R.map f ≫ v_M'`, the node's displayed naturality equation.
* Its second conjunct is `A.map E_M ≫ epsilon_(PM) = theta_(RM) ≫ P.map epsilon_M`.
  Both sides are arrows A Q R M to P M in the full completed integral category.
* Its third conjunct is `u_x(QN)^-1 ≫ Z_x(theta_N) =
  Q(u_(x_1)(N)^-1) ≫ b_(1,x,AN)` for every integral constructible N on s.
  `.hom.hom` and ambient `integralDerivedPullback.map` merely apply the full
  inclusion to the specified isomorphisms; they do not change their coefficients.
* Its fourth conjunct is `E_M ≫ v_x^(PM) = Q(v_(x_1)^M) ≫ b_(1,x,M)`.
  Both sides are exactly Q R M to Z_x P M, for every M.
* Its final conjunct is the first identity on the ordinary derived category
  `coefficientSequenceDerived l E Y`, for every whole-system object C.
  It uses the actual `systemExchange`, `systemAdjunction.counit`, and
  `systemSquare`, before applying any evaluation or limit. In particular it is
  stronger than merely testing the formula at coherent reductions, as appropriate
  for an identity of the indicated system natural transformations.

The image-under-realization clause uses the existing constructions themselves:
`integralExchange` is sourceComparison, then the image of `systemExchange` under
`coefficientSequenceLimit`, then inverse reductionPullbackIso under systemDirect
and that limit. `integralCounit` similarly realizes the system counit with the
reconstruction counit and completeness unit. The completed equation is thus
stated for precisely these transported system maps, not a substitute abstract
mate or an arbitrary arrow with the correct reductions. The proof docstring
explicitly records applying this same functor and the operation comparisons to
identify the image of the system identity with the completed identity. No
finite-reduction detection of equality of derived morphisms is used or assumed.

### Dependency declarations used

All thirteen original dependency nodes and their recorded source signatures and
docstrings were inspected. The relevant declarations are:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.geometricFiber`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
* `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius`, `galoisMap_projections`.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`.
* `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`; the actual system
  direct-image realization has the published `directImage_roos` presentation in
  this notion, so a free choice of a triangle is not used for R.
* `Sheaf.Paper.IntegralPullbackComposition`: `integralPullbackComposition`.
* `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `integralPullbackComparisonRealization`, `integralComparisonUnit`; the existing
  `ProperSemilinearGerms.comparisons` chooses its simultaneous system at the
  universe-lifted base field and identity coefficient embedding.
* `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`:
  the recorded `AlgebraicGeometry.Etale` finite-etale adjunction declarations were
  read and imported. The concrete completed counit required here is already
  constructed by `ProperSemilinearGerms.integralCounit`, and the system adjunction
  is `FrobeniusExchange.systemAdjunction`; no replacement finite-etale category
  is used for the completed coefficients.
* `Sheaf.Paper.FrobeniusGeometricExchange` and its public dependency
  `Sheaf.Paper.SystemOperationExchangeRealization`: actual direct recipe,
  `systemDirect`, `systemAdjunction`, `systemSquare`, `systemExchange`,
  `integralExchange`, `directIntegral`.
* `Sheaf.Paper.SemilinearDerivedSections`: the whole-system derived calculus
  of `SemilinearSections.semilinearDerivedSections`, on which these system
  operations are based.
* `Sheaf.Paper.CompletedRlimFunctor`: `AlgebraicGeometry.Scheme.completedRlim`
  and `completedRlim_computation`; the canonical coefficient sequence limit
  uses the published total derived inverse limit.
* `Sheaf.Paper.BasicOperationsCoefficientReduction`:
  `basicOperationsCoefficientReduction` supplies the proof plan's normalized
  operation comparisons, not additional assumptions in the new theorem.
* `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `mateEquiv_counit`
  (the recorded mathlib match of `def-weil-pbc-adjunction-mate`).

Two already-landed definition owners were added to stmt_deps:
`def-a1-proper-sections-germ-and-moving-point` owns the exact existing comparisons,
`integralCounit`, `integralGerm`, and positive moving-point construction in
`Sheaf.Paper.ProperSectionsSemilinearGerms`;
`def-weil-system-operation-exchange-realization` owns the actual simultaneous
system mate and realization used by the geometric exchange. No new node and no
dependency record repair is needed: these needed notions already exist.

### Edge cases

The index j is an integer, so j=0, negative j, and j=1 are all admitted; j=1 is
the same h^-1 x g used by the existing `movingPoint ... 0`. For Y empty the
point-dependent conclusion has no instances, while `structure_square` remains
meaningful. M=0, N=0, f=0, and identity f are all quantified, without an extra
nonzero condition. Y=s with x=id has the identity-comparison normalization.
No assumption that g is a k-morphism is made; only the semilinearity equation
is asserted. Neither completion nor equality is inferred from independent
finite-level equations. No statement was found false, and no statement correction
or STATEMENT-DISPUTED flag is required.

### Searches actually run

* msearch LeanFinder: `Completed integral semilinear Frobenius adjunction counit
  evaluation moving point germ square`. Eight hits, including
  `ΓSpec.adjunction_counit_app'`, `ModuleCat.Tilde.stalkToFiberLinearMap_germ`,
  and adic-completion maps, none of which states the completed germ square.
* msearch Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction.counit`.
  Four hits: `mateEquiv_counit`, its symmetric form, and the two apply formulas.
  These supply the generic formal calculation, not this geometric/system theorem.
* msearch grep (Mathlib CategoryTheory):
  `semilinear.*germ|germ.*exchange|mateEquiv_counit`. Four hits in
  `Adjunction/Mates.lean` and `Monoidal/Closed/Functor.lean`; only abstract mates.
* msearch LeanSearch: `The adjunction counit germ from completed integral derived
  sections commutes with semilinear Frobenius exchange at a moving geometric point`.
  Eight generic adjunction/derived-counit results, no full statement.
* rg in project `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `semilinear.*germ|germ.*[Ss]quare|integralSemilinearGerm|lem-a1-integral-semilinear-germ-square`.
  The full statement was absent. It found the existing proper rational germ
  theorem and its integral helpers, which are reused here.
* DAG read/search found `def-a1-proper-sections-germ-and-moving-point`, whose
  statement explicitly asserts no germ identity or naturality theorem. It is
  an owner for definitions, not an existing theorem matching this item.

Validation: scompile.py compiles the delivered module separately in sandbox and
library module modes against the published server build (21.2 s and 17.6 s),
with exit 0 and no unexpected warnings. All variables/universes are explicit,
auto-implicit binding is disabled, and no line exceeds 100 characters.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
