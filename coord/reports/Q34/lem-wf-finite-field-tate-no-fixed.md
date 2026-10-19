## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.FiniteFieldJacobianTateNoFixed`
states `AlgebraicGeometry.finiteFieldJacobian_tate_no_fixed`, with its sole proof
`sorry`. No definitions, new nodes, dependency repairs or statement corrections
are introduced. I read the current DAG statement and all three proof steps, the
three statement-dependency nodes and their complete recorded declarations, and
the corresponding main-20261015 blueprint statement. They agree.

Hypothesis and conclusion correspondence:

- The field `F_Q` is `k₀ : Type u` with `[Field k₀] [Fintype k₀]`;
  `Q = Fintype.card k₀`. `K` with `[Field K] [Algebra k₀ K]
  [IsAlgClosure k₀ K] [IsAlgClosed K]` is an arbitrary algebraic closure.
  No prime-power presentation, specified rational point, or particular concrete
  model of the finite field or its algebraic closure is imposed.
- The smooth projective geometrically connected curve is `C₀` with its
  `Scheme.Over` instance, `SmoothOfRelativeDimension 1`, `IsProjective` and
  `GeometricallyConnected` on its structure morphism. Relative dimension one
  records the word curve; projectivity supplies the properness needed by the
  canonical-action dependency.
- `C = C₀ ×_{k₀} K` is expressed by `p : C ⟶ C₀` and `hC : IsPullback ...`.
  The instances `IsCurve`, `Smooth`, `SmoothOfRelativeDimension 1`, `IsProper`
  and `GeometricallyIntegral` on `C` are the inherited geometric-fibre properties
  required to type the existing `IsJacobian` and action declarations. They add
  no geometric restriction: smooth relative dimension one and projectivity
  persist under base change, and a smooth geometrically connected curve is
  geometrically integral. This is the same interface as the recorded action
  dependency and its landed consumer `exists_curveH1_dualTateModule`.
- The fixed Jacobian pair is `J : Over (Spec (.of K))` with `[CommGrpObj J]`
  and `[IsJacobian (C ↘ Spec (.of K)) J]`, together with its representing
  isomorphism `φ` and group-compatibility `hφ : IsPicardZeroMul ... φ`.
  These are the data of the pair in `def-sc-jacobian`, not additional assumptions
  about a chosen descent or an arbitrary action.
- The coefficient prime is `(ℓ : ℕ) [Fact ℓ.Prime]`, with
  `hℓ : ¬ ℓ ∣ Fintype.card k₀` exactly expressing `ℓ ∤ Q`.
- Arithmetic Frobenius is exactly
  `FiniteField.frobeniusAlgEquivOfAlgebraic k₀ K`; its Mathlib declaration has
  value `x ^ Fintype.card k₀`. The scheme action is the unique action selected
  from `existsUnique_geometricJacobian_galoisAction ... .exists`. Its uniqueness
  determines the selected action, as required by the no-hollow-data rule.
- The existentially bound additive homomorphism `F` names the canonical action
  on `J`'s geometric points. Its first conjunct specifies its value at EVERY
  geometric point: the canonical equivalence
  `pointsAddEquivGeometricPoints J` converts to `K`-points, on which the result
  is `Spec(sigma_Q) ≫ x ≫ a_sigma_Q`. In conventional composition this is
  `a_sigma_Q ∘ x ∘ Spec(sigma_Q)`, exactly the recorded dependency's formula.
  Since the equivalence and the forgetful maps on points are injective, this
  equation determines `F` uniquely. No free choice of action or extra
  equivariance assumption is supplied. Existentially naming its graph simply
  avoids duplicating the dependency's construction in a new definition.
- `(T_ℓ J)^{sigma_Q=1} = 0` is the second conjunct,
  `∀ t : IsAbelianVariety.tateModule ℓ J,
  AddCommGroup.tateModule.map F t = t → t = 0`.
  This uses the exact recorded abelian-variety Tate module, definitionally the
  group Tate module on `J`'s geometric points, with its componentwise action.
- The last conjunct is `Function.Bijective
  (AddCommGroup.rationalTateModule.map F - LinearMap.id :
  IsAbelianVariety.rationalTateModule ℓ J →ₗ[ℚ_[ℓ]]
  IsAbelianVariety.rationalTateModule ℓ J)`.
  A bijective linear endomorphism is exactly a linear automorphism; subtraction
  has the required order `sigma_Q - 1`. This asserts surjectivity as well as
  injectivity on the rational module, without imposing integral surjectivity.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.AbelianVariety.GeometricJacobianGaloisAction`:
  `AlgebraicGeometry.existsUnique_geometricJacobian_galoisAction`, including
  its explicit inverse convention for the semilinear base map and its
  source-twisted point-action convention.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`:
  `AlgebraicGeometry.IsJacobian`, together with
  `AlgebraicGeometry.IsPicardZeroMul` and `picardFunctorDegree` from its imports.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`:
  `AlgebraicGeometry.IsAbelianVariety.tateModule`, `rationalTateModule` and
  `pointsAddEquivGeometricPoints`. These are the recorded definitions, not
  private replacements. `AddCommGroup.tateModule.map` and
  `AddCommGroup.rationalTateModule.map` are from the imported upstream
  `WeilConjectures.GroupTheory.TateModule`.
- The proof-only dependency imports retain the DAG plan:
  `Sheaf.AlgebraicGeometry.AbelianVariety.FrobeniusFixedTateModules`,
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Final`,
  `Sheaf.RingTheory.RegularRingSmoothAscent`,
  `Sheaf.AlgebraicGeometry.IsRegularScheme`, and
  `Mathlib.RingTheory.RegularLocalRing.Defs`.
  The Picard/Jacobian existence, smooth-morphism and finite-field convention
  modules are already imported transitively by the action/Tate modules.

Edge cases checked before writing:

- Genus zero is included: both Tate modules are zero and the unique map on the
  zero rational vector space is bijective. No positive-genus assumption occurs.
- A curve without a rational point is included: `φ` is its representing
  isomorphism, not an Abel-Jacobi construction requiring a base point.
- Characteristic two and `ℓ = 2` in odd characteristic are included.
  The excluded case is precisely `ℓ ∣ Q`; no unmentioned parity restriction.
- The empty scheme cannot be a geometrically connected smooth curve of
  relative dimension one; no extra nonemptiness assumption was added.
- The integral conclusion claims only fixed-vector vanishing. In particular,
  rational points of order divisible by `ℓ` do not contradict it, and the
  statement does not claim `sigma_Q - 1` is integrally surjective.
- The point action uses arithmetic Frobenius, not its inverse; the inverse
  appearing inside the dependency's semilinear BASE map is compensated by
  the explicit `Spec(sigma_Q)` twist of the point's source.
- Both field and scheme universes are explicitly `u`, as in the recorded
  dependency; `autoImplicit false` guards against accidental free variables.

Searches for an exact existing statement:

- `msearch.py ... leanfinder` with query “Arithmetic Frobenius has no fixed
  vectors on the Tate module of a geometric Jacobian and Frobenius minus
  identity is bijective on its rational Tate module”: eight hits, concerning
  arithmetic Frobenius at ideals, finite-field automorphisms, Witt vectors and
  isocrystals; none is this theorem.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.IsAbelianVariety, AddCommGroup.tateModule, LinearMap`:
  zero hits; the service reports unknown upstream identifier
  `AlgebraicGeometry.IsAbelianVariety`.
- `msearch.py ... leansearch` with query “Frobenius minus identity is an
  automorphism of the rational Tate module of a Jacobian over a finite field”:
  eight hits, including `FiniteField.frobeniusAlgEquivOfAlgebraic_apply`,
  Frobenius on finite extensions and Witt vectors, but no Tate/Jacobian result.
- `msearch.py ... grep` with expression
  `[Ff]robenius.*[Tt]ate|[Tt]ate.*[Ff]robenius`: zero Mathlib hits.
- `rg` of the upstream `WeilConjectures` and current `lean/Sheaf` for
  `TateModule`, `Frobenius`, `frobeniusAlgEquivOfAlgebraic`, `no_fixed`, and
  `finiteFieldJacobian` found the recorded action and Tate definitions, the
  general abelian-variety fixed-vector theorem, and curve cohomology
  consumers. None states both conclusions for this geometric Jacobian.
- The required `grep -rn 'lem-wf-finite-field-tate-no-fixed'` on the upstream
  source returns only a docstring reference at
  `AlgebraicGeometry/FundamentalGroup/Frobenius.lean:602`. Reading the full
  theorem there shows it asserts existence of a section of an etale torsor,
  not the Tate-module statement. It is not an exact existing match.
- A final direct `rg` of Mathlib, upstream and `lean/Sheaf` for the chosen
  declaration name and Frobenius/bijective combinations found no collision.

No `STATEMENT-DISPUTED` issue or node fault was found. No node field except
`lean` changes. The module compiles cleanly through the prescribed
`scompile.py Q34 lem-wf-finite-field-tate-no-fixed <module>` wrapper, which
compiled its required side overlay and checked the delivered module separately.

## Second reading by Q34

This is the author's second reading, not a claim of independent review; the
maintainer performs the independent reading for this dispatcher delivery.
I reopened the node and final module together. The field cardinality appears
in the exact nondivisibility hypothesis; the geometric fibre is the specified
pullback; projectivity, relative dimension one and geometric connectedness
are all explicit. The fixed representing pair is passed unchanged to the
recorded canonical-action theorem. I checked the composition direction against
that theorem's point-action clause: Lean's left-to-right `≫` yields exactly
`a_sigma ∘ x ∘ Spec(sigma)`. The existential `F` has a value equation on every
point, so the vanishing claims cannot be satisfied by selecting an unrelated
operator. The integral clause quantifies over the recorded `T_ℓ J`, and the
rational clause uses subtraction of `LinearMap.id` and genuine bijectivity on
its recorded rationalization. Genus zero, missing rational base points and
all allowed characteristics remain covered. No mismatch was found and no
statement correction was necessary. The theorem docstring retains all three
proof steps, including the regularity bridge and rational finite-dimensional
linear algebra. There is one named theorem and one `sorry`, with no proof or
data hidden in local definitions.
