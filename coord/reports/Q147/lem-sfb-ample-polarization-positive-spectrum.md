## Worker report

Q147, stage 2, 2026-10-24. The single module
`Sheaf.AlgebraicGeometry.AbelianVariety.AmplePolarizationPositiveSpectrum`
states `AlgebraicGeometry.IsAbelianVariety.ample_polarization_positive_spectrum`.
Its only proof is `sorry`; there are no definitions, helper theorems, new nodes,
dependency replacements, or statement changes. The module docstring cites Milne AV,
and the theorem docstring reproduces all eight proof steps and their dependencies.

Every hypothesis and clause is represented as follows:

- The arbitrary field is `{k : Type u} [Field k]`. The abelian variety is
  `A : Over (Spec (.of k))`, `[GrpObj A] [IsAbelianVariety A]` (proper, smooth,
  connected). There is no algebraic closedness, perfection, characteristic,
  positive-dimension, or symmetry hypothesis.
- `L M : A.left.Modules`, `[hL : L.IsInvertible] [hM : M.IsInvertible]`,
  `hLamp : IsAmple A.left L`, `hMamp : IsAmple A.left M` are exactly the two
  ample invertible modules. These are the recorded definitions, not replacement
  predicates or a stronger notion of ampleness.
- The phrase “use the dual variety and line-module homomorphisms” is expanded
  using the dependency's existing `AbelianDualPoincareDatum A` and the integral
  `φL φM : abelianHom A D.dual`. `hφL` and `hφM` require these actual maps to
  classify the existing normalized translated-difference families. These maps
  are determined by the Poincare universal property; they are not arbitrary.
- `c` is the dependency's rational composition interface. `hc` is verbatim its
  pure-tensor characterization, hence uniquely specifies composition on the
  rational Hom spaces. Categorical order is `c f g = g ∘ f`.
- Rational Hom is the recorded `abelianRationalHom = ℚ ⊗[ℤ] abelianHom`, with
  `abelianHomToRational f = 1 ⊗ f`. Tensor symmetry identifies this with the
  node's factor order `Hom ⊗[ℤ] ℚ`.
- The dependency gives the Hom space and bilinear composition but no ring instance
  on that tensor. Accordingly `E : Type v`, `[Ring E] [Algebra ℚ E]`, and
  `e : E ≃ₗ[ℚ] abelianRationalHom A A` express the same endomorphism algebra
  in an explicitly identified model. `hone` identifies its unit with the identity
  morphism, and `hmul` identifies its multiplication with ordinary composition:
  `e (x*y) = c (e y) (e x)`. These equations and linearity completely determine
  the unital rational algebra structure; no arbitrary algebra or additional
  geometric restriction is substituted. Every model is allowed, at an independent
  universe v. Conversely the usual rationalized endomorphism ring supplies such
  a model, since composition is bilinear. In particular this binder does not
  require finite dimension, a faithful Tate representation, or positivity as input.
- `dQ` is rational duality. Its characterizing equation `hdQ` says on every
  rational pure tensor that its integral map `db` classifies `(b × 1)^* P`:
  the two pullback modules are explicitly written. This is the specialization of
  the existing dependency's dual classifier and its rational extension equation.
  Uniqueness of the Poincare classifier makes this independent of the existential
  witness `db`; additivity extends it to all rational elements. It retains the
  normalization through the same datum, with the same unrigidified-isomorphism
  characterization already used by the recorded dependency.
- `invLambda` and `hinv`, `hinv'` express both inverse identities for
  `lambda = abelianHomToRational φL`, without assuming an integral inverse.
- `u : E`, `hu` identifies the comparison with `lambda⁻¹ ∘ φM`, in categorical
  order `c φM invLambda`. `dagger : E →ₗ[ℚ] E` and `hdagger` identify dagger with
  `lambda⁻¹ ∘ (e x)^vee ∘ lambda`. These are the canonical operations, determined
  by the existing calculus, rather than assumptions of self-adjointness.
- The first conclusion is exactly `dagger u = u`.
- The generated algebra C is the actual Mathlib subalgebra `Algebra.adjoin ℚ {u}`.
  `Algebra.adjoin_singleton_eq_range_aeval` identifies it exactly with the image
  of `Polynomial.aeval u : ℚ[X] →ₐ[ℚ] E` in the node. Its unit, addition,
  multiplication, and rational algebra structure are inherited. Mathlib's
  `Algebra.instCommRingAdjoinSingleton` makes this a commutative unital ring
  even though E need not be commutative. No commutativity assumption on E is added.
- `FiniteDimensional ℚ (Algebra.adjoin ℚ {u})` says precisely that this vector
  space has a finite basis. It is a conclusion, never a hypothesis.
- `∃ d : ℕ` is exactly some integer d ≥ 0, without a redundant inequality.
  `ρ : (ℝ ⊗[ℚ] Algebra.adjoin ℚ {u}) ≃ₐ[ℝ] (Fin d → ℝ)` is the required unital
  real algebra isomorphism with coordinatewise arithmetic. Mathlib uses the
  real factor first so its canonical global `leftAlgebra` instance supplies
  the real action; tensor symmetry exchanges this with the stated C ⊗ ℝ and
  sends `u ⊗ 1` to `1 ⊗ u`. This changes no algebraic assertion.
- `⟨u, Algebra.self_mem_adjoin_singleton ℚ u⟩` is u as an element of that actual
  subalgebra. `∀ i : Fin d, 0 < ρ (1 ⊗ₜ[ℚ] ...) i` is strict positivity of every
  coordinate, not nonnegativity or positivity of a trace or norm.

Dependency declarations inspected and reused:

- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety`, with its full proper/smooth/connected
  signature and the unbundled `GrpObj` convention.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, its local unit-isomorphism
  definition, and the existing module tensor notation.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, the quasi-compact plus affine
  nonvanishing-locus condition.
- `Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculusOverField`:
  `AlgebraicGeometry.IsAbelianVariety.polarization_calculus_over_field`; its
  complete signature and ten-step proof docstring were read. Its existential
  `c`, classifiers, dual extension, inverse identities, and dagger formula supply
  exactly the data characterized in this theorem's binders. Its public imports
  expose `RationalHom` (`abelianHom`, `abelianRationalHom`, `abelianHomMap`,
  `abelianHomComp`, `abelianHomId`, `abelianHomToRational`) and `DualPoincareDatum`
  (`AbelianDualPoincareDatum`, `ClassifiesAbelianDifference`). Both full modules
  were read, and RationalHom was additionally checked with `scompile.py --source`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; the bundled
  morphisms in `abelianHom` are group-scheme homomorphisms. The recorded
  pointwise group instances require the `MonObj` scope, now opened explicitly.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct` and its quotient
  construction; algebra tensor multiplication and scalar extension use
  `Mathlib.RingTheory.TensorProduct.Basic`.
- `Mathlib.RingTheory.Adjoin.Polynomial.Basic`:
  `Algebra.adjoin_singleton_eq_range_aeval`, `instCommRingAdjoinSingleton`.
  `Mathlib.Algebra.Algebra.Equiv`: `AlgEquiv`, which preserves unit and scalars.

All currently recorded proof-dependency modules are imported without `public`,
except those already public for statement data. The still unrecorded proof inputs
(Rosati positivity, Weil pairing, equal-dimension isogeny criterion, multilinear
intersection, relative determinant, mixed-intersection positivity) are listed by
node in the proof docstring and will acquire their imports when stated. None is
needed to type this statement.

Edge cases checked before writing and on rereading:

- Dimension zero: no `Nontrivial E` or positive-dimension binder; zero ring E and
  zero subalgebra C are permitted, `d = 0` has empty `Fin 0`, and positivity is
  vacuous. A unital map from ℚ to the zero ring is allowed by `Algebra`.
- Arbitrary characteristic, including two, and imperfect nonclosed k are covered.
  Only ℚ and ℝ are coefficient fields, so their characteristic zero does not
  restrict the geometric base field.
- L and M need not be symmetric. L=M gives u=1 and all coordinates 1 for
  nonzero C; the trivial abelian variety still has the d=0 case.
- E may be noncommutative, and C is not assumed a field. A product of several
  real factors and the empty product are both expressible.
- No auto-implicit variables; both autoImplicit options are disabled, and u,v
  are explicitly declared. No file-local definitions, notation or instances.

Searches for an existing statement (all 2026-10-24):

- `msearch.py ... leanfinder "The ratio of two ample polarizations of an abelian
  variety generates a rational algebra split over the reals with positive
  eigenvalues"`: eight unrelated root-pairing/number-field hits; no match.
- `msearch.py ... leansearch "The ratio of two ample polarization maps on an
  abelian variety has positive real eigenvalues"`: eight hits, including
  `LinearMap.IsPositive.nonneg_eigenvalues`, symmetric eigenvalues, and root
  polarizations. None proves the geometric positivity assertion.
- `msearch.py ... loogle '"Algebra.adjoin", "TensorProduct", "IsScalarTower"'`:
  zero hits. Targeted query `'"adjoin_singleton_eq_range_aeval"'`: one exact
  structural match, used above; not the geometric theorem.
- `msearch.py ... grep 'Rosati|[Pp]olarization|[Aa]belian[Vv]ariety'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `abelianRational`,
  `RationalEnd`, `rationalEnd`, `positive_spectrum`, and polarization-spectrum
  terms found the rational-Hom/calculus definitions and Tate action, but no
  positive-spectrum theorem. Search of the exact node id in upstream found none;
  the project endomorphism-span theorem mentions this item only as a proof input.
- `rg` in Mathlib for `adjoin.*Comm`, `range.*aeval`, and tensor algebra instances
  located the exact existing definitions used here. The exact new declaration
  name was searched in both libraries and `dag/lean_names_upstream.json`; no clash.

Source verification used the local Milne AV PDF, printed pp.61–62 (PDF pages
67–68), reading the Rosati formula, Proposition 14.2 and Theorem 14.3; the node's
agent deduction supplies the spectral/intersection argument beyond those numbered
results. The supplied example CompactObject Sheaf module is withdrawn; its node
now points to the identical upstream definition. No withdrawn declaration is used.

Validation: `scompile.py` compiled the delivered module in sandbox and library
modes, cleanly, with only the permitted postponed-proof mechanism. The first probe
found the pointwise-group instance scope missing; opening `MonObj` fixed it.
No statement dispute or node fault remains.

## Second reading by Q147

Author self-check, not an independent review (the dispatcher requests direct
worker delivery and prohibits additional agents). Reopened the node, the complete
Lean signature, and the existing polarization-calculus module. Checked c's order,
the two inverse identities, and the threefold dagger composition against Milne's
formula. Checked that u uses φM then invLambda, that E multiplication uses reversed
categorical order, and that hdQ pins duality by the same Poincare pullback family.
The explicit E model is identified with the tensor space and has pinned unit and
product, so it cannot replace the geometric endomorphism algebra by an unrelated
ring. Checked that ampleness is a hypothesis for both modules while finite dimension,
self-adjointness, and splitting are conclusions. Checked the tensor-factor exchange
and the actual `Algebra.adjoin` subtype containing u, and checked strict inequalities
for every `Fin d` coordinate, including the empty case. No mathematical mismatch
was found. The only implementation change was opening the existing `MonObj` scope
for the canonical pointwise abelian group instances. The report records that
change and the successful server compile.
