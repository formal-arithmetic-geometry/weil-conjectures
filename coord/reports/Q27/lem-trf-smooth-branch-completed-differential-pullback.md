## Worker report

Item: `lem-trf-smooth-branch-completed-differential-pullback`, group Q27, stage 2.
The delivery states `Algebra.smooth_branch_completed_differential_pullback` in
`Sheaf.RingTheory.SmoothBranchCompletedDifferentialPullback`. It contains one theorem,
whose entire proof is `by sorry`. No definitions, new nodes, dependency repairs, or
statement corrections are introduced. The existing node changes only in `lean`.

Source read: `literature/stacks-project/curves.tex`, the full coordinate-change proof
of `lemma-fitting-ideal-well-defined` (Tag 0C4B, lines 4065–4092), and the completed
Jacobian passage of `lemma-nodal` (Tag 0C4D, lines 4174–4228). These are the source
places specified by the node; the mixed completion/naturality assertion is the
agent-formulated refinement recorded there, not a verbatim theorem in Stacks. Also
read the current blueprint's `sec-trace-formula/sk-i-curve-zero/_section.md` and
`lem-trf-local-term-locality.md` and its proof. This item is an auxiliary extraction,
not that blueprint unit's own statement.

### Hypotheses and conventions

| Node hypothesis or object | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Finite-type k-algebra S | `[CommRing S] [Algebra k S]`, `hS : (algebraMap k S).FiniteType` |
| Maximal ideal m with residue field k | `(m : Ideal S) [m.IsMaximal]`, `residueS : m.ResidueField ≃ₐ[k] k` |
| A = S_m as a local k-algebra | `[Algebra S A] [IsLocalization.AtPrime A m] [IsLocalRing A]` and `[Algebra k A] [IsScalarTower k S A]` |
| D is a DVR | `[CommRing D] [IsDomain D] [IsDiscreteValuationRing D]` |
| D is the local k-algebra of a rational point of a smooth one-dimensional curve | An affine neighbourhood `Spec B` is supplied: `hcurve : IsCurve (Spec.map (CommRingCat.ofHom (algebraMap k B)))`, `hsmooth : AlgebraicGeometry.Smooth (...)`, `hdim : topologicalKrullDim (Spec (CommRingCat.of B)) = 1`, `(q : Ideal B) [q.IsMaximal]`, `residueB : q.ResidueField ≃ₐ[k] k`, `[Algebra B D] [IsLocalization.AtPrime D q] [Algebra k D] [IsScalarTower k B D]` |
| Local k-algebra map alpha : A → D | `[Algebra A D] [IsScalarTower k A D] [IsLocalHom (algebraMap A D)]`; alpha is `algebraMap A D` |
| R = completion of A, T = completion of D | Existing `Algebra.LocalCompletion A` and `Algebra.LocalCompletion D`, definitionally the maximal-ideal `AdicCompletion` |
| Fixed complete local k-algebra isomorphism T ≃ k[[t]] | `eT : LocalCompletion D ≃ₐ[k] PowerSeries k`; a ring isomorphism preserves maximal ideals and their powers, hence is automatically local and adically continuous |
| F = Frac D | `[Field F] [Algebra D F] [IsFractionRing D F]` with `[Algebra k F] [IsScalarTower k D F]` |
| L = k((t)) and the compatible embeddings | `LaurentSeries k`, Mathlib's `algebraMap (PowerSeries k) (LaurentSeries k)`, and `[Algebra F (LaurentSeries k)]`; `hF` requires its restriction to D to equal the completion map followed by `eT` and the power-series inclusion |
| Differentials, base change, and free differential symbols | `KaehlerDifferential`, `KaehlerDifferential.D`, `TensorProduct`. The scalar factor is first, using the canonical tensor symmetry already adopted by `CompletedDifferentials`. A free module on dt is its coefficient ring; the distinguished generator is 1. |
| Termwise power-series derivative; quotient derivative on L | `PowerSeries.derivative k` and `LaurentSeries.derivative k`. The former is `MvPowerSeries.pderiv k ()`; the latter is the first Hasse derivative and has the usual integer coefficient derivative and quotient rule. |

The affine neighbourhood is a presentation of the given smooth local ring, not an
extra smoothness assumption on A. Every curve in the node admits such a neighbourhood
of its rational point. Conversely the displayed `Spec B` is itself a curve satisfying
all the required conditions. A nonzero-dimensional local DVR forces the neighbourhood
to have dimension one; no connectedness assumption is imposed. `IsLocalization.AtPrime`
and `IsFractionRing` allow arbitrary models of exactly the specified localization
and fraction field. All objects can be placed in a common ambient universe `u`,
which is quantified explicitly; no small test category or test algebra is used.
The algebra structure on L is constrained by `hF`; it is not an arbitrary map.
The universal property of the fraction field makes that extension unique.

### Every conclusion

1. The induced completed map is the existential `ahat`. Its first conjunct is its
   extension equation on all `a : A`; the second is adic continuity in powers of
   the extended maximal ideals. These characterize the induced completion map,
   so later clauses do not assume an unconstrained map.
2. The existential `E : CompletedDifferentials k D ≃ₗ[LocalCompletion D]
   LocalCompletion D` is the stated T-linear isomorphism to T dt. Its formula on
   `1 ⊗ₜ[D] KaehlerDifferential.D k D d` is expressed after applying `eT`.
3. `dD` and `dA` are derivations with the existing
   `IsCompletedDifferentialExtension k D dD` and
   `IsCompletedDifferentialExtension k A dA`. These predicates state exactly
   extension on the algebraic local ring and continuity of the specified derivation.
   `∀ h : LocalCompletion D, eT (E (dD h)) = PowerSeries.derivative k (eT h)`
   is the formula on every element of T, not only on its dense algebraic subring.
4. `delta : KaehlerDifferential k F →ₗ[F] LaurentSeries k` has the required
   formula on every `dz`, and `Function.Injective delta` is a separate conjunct.
   The L-linear equivalence `EL` satisfies `EL (c ⊗ₜ[F] w) = c * delta w`
   for every c and w, so it is the induced scalar extension of delta.
5. `beta : LocalCompletion D ⊗[A] KaehlerDifferential k A →ₗ[LocalCompletion D]
   LocalCompletion D` is defined by its formula on every pure tensor, using
   `KaehlerDifferential.map k k A D` and E. This is precisely algebraic differential
   pullback, extension to T, and composition with E.
6. The semilinear `betaR : CompletedDifferentials k A →ₛₗ[ahat.toRingHom]
   LocalCompletion D` satisfies `betaR (r ⊗ₜ[A] w) = ahat r * beta (1 ⊗ₜ[A] w)`.
   This explicitly gives the tensor-associativity identification used in the node.
   Its equation on `dA h` for every completed h is the displayed completed pullback
   compatibility, including the image of the continuous universal differential.
7. Every finite formal presentation is quantified by n, s, a surjective k-algebra
   map p with kernel generated by g, and adic continuity. Zero constant term of
   each g_j is exactly membership in the ideal of variables. There is no n ≥ 2
   restriction from the project's dummy-variable presentation structure. The first
   conclusion is the formula on `dA (p (MvPowerSeries.X i))` for every i. The second
   is exactly the Jacobian sum, with `MvPowerSeries.pderiv k i (g j)` evaluated by
   p, ahat and eT. This does not substitute polynomial derivatives for formal ones.
8. Rational compatibility is asserted for every `w : KaehlerDifferential k A`
   and `c : LaurentSeries k`. The left side is the scalar extension of beta;
   the right side uses `KaehlerDifferential.map k k A D` and then
   `KaehlerDifferential.map k k D F`, followed by delta. Equality on all pure tensors
   is equivalent to equality of the full L-linear maps, with no generator case omitted.
9. `∀ sigma : PowerSeries k ≃ₐ[k] PowerSeries k` covers all complete local parameter
   changes, using two copies of the same Lean type for the variables t and s.
   Existence of `tau : LaurentSeries k ≃ₐ[k] LaurentSeries k`, its extension formula
   for every power series, and uniqueness among all such field isomorphisms are
   explicit. `IsUnit (PowerSeries.derivative k (sigma PowerSeries.X))` is the unit
   derivative assertion, and the next equation is the chain rule for every h in L.
10. `nu` is a `LinearEquiv` semilinear over `tau.toRingHom`, with inverse ring map
    supplied explicitly from tau. Its formula is precisely tau(h) times v'. The
    set-image equality for the range of `algebraMap (PowerSeries k) (LaurentSeries k)`
    is the assertion that it carries the integral differential lattice onto itself.
11. `Es` is an invertible semilinear map over `(eT.trans sigma).toRingHom`, and
    `betas` is semilinear over that same map. These are the s-parameter maps after
    precomposing with scalar transport. Their equations on dd and da specify the
    differentiated formulas for the new parameter. `deltas` is k-linear, satisfies
    its scalar law `deltas (f • w) = tau (algebraMap F L f) * deltas w`, and its
    equation on dz specifies the rational map for the transported embedding.
    The last three conjuncts commute the E, beta and delta squares for every input
    of their respective modules. Thus the squares are on whole modules, not merely
    the displayed differential generators. Together with the completed compatibility
    and chain rule they also give the completed-element compatibility after change
    of parameter. Semilinear transport encodes exactly omega tensor c mapping to
    omega tensor sigma(c), or tau(c) for rational scalars.

### Dependency declarations and imports

Every statement dependency was read with its full signature and docstring, or its
recorded Mathlib match when there is no Lean record.

- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType`, used directly by hS.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime` and `IsLocalization.AtPrime`; rational residue fields use
  `Ideal.ResidueField` from `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`.
- `def-sc-discrete-valuation-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing` with its required `IsDomain` instance.
- `def-sc-curves`: `WeilConjectures.AlgebraicGeometry.Curve`,
  `AlgebraicGeometry.IsCurve`, used on the chosen affine neighbourhood.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`; the needed algebra structure is the one in
  `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `MvPowerSeries (Fin n) k`; one variable uses the recorded `PowerSeries k` convention.
- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `.D`, `.map`, and its universal property
  `.linearMapEquivDerivation`. No private replacement is made.
- `def-weil-module-base-change`: `Mathlib.LinearAlgebra.TensorProduct.Tower`,
  `TensorProduct` and the scalar-extension convention of `LinearMap.baseChange`.
- `def-trf-completed-differential-extension`:
  `Sheaf.RingTheory.CompletionKaehlerDifferentialComparison`,
  `Algebra.IsCompletedDifferentialExtension`, used twice. Its public imports supply
  `Algebra.LocalCompletion` from `Sheaf.RingTheory.FormalLocalPresentation` and
  `Algebra.CompletedDifferentials` from `Sheaf.RingTheory.CompletedJacobianPresentation`.
- `def-trf-formal-power-series-partial-derivative`:
  `Mathlib.RingTheory.MvPowerSeries.Derivative`, `MvPowerSeries.pderiv`.

The recorded modules for the stated proof dependencies are imported privately:
`Sheaf.SixFunctors.TraceFormula.FormalPowerSeriesContinuousFree`,
`Sheaf.RingTheory.FormalRelativeDerivationExpansion`,
`Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`, and
`Mathlib.RingTheory.Etale.Kaehler` (the recorded
`KaehlerDifferential.isLocalizedModule_map`). The completion comparison module is
already public because it also supplies a statement dependency. No cycle is introduced.
The docstring carries all seven steps of the DAG proof, with the named inputs.

### Edge cases checked

- k may have any characteristic. For alpha sending a local parameter u to t^p
  in characteristic p, beta may be zero; delta remains injective on rational
  differentials of the smooth branch. The statement does not assert beta injective.
- Constant alpha through the rational residue field is included; all its pullback
  derivatives vanish, which is compatible with every displayed formula.
- A=k (take S=k, m=0) and n=0 are included. Its differential module is zero and
  the sums over `Fin 0` are empty. There is no positivity bound on n or s; s=0 is
  the relation-free case.
- The smooth affine line gives D=k[t]_(t), E(dt)=1 and the usual rational
  derivative inclusion. The zero local ring and zero-dimensional smooth D are
  properly excluded by the DVR hypothesis, as in the node.
- Disconnected smooth curves and neighbourhoods with additional zero-dimensional
  components are allowed by `IsCurve` and total dimension one.
- sigma=id and sigma(t)=a*s+s^2 with a nonzero are included (in every characteristic).
  The derivative has nonzero constant term; the explicit inverse-ring-map arguments
  for semilinear equivalences also cover the identity and involutions.
- The tensor formulas are on arbitrary w and arbitrary scalar, so include zero
  tensors and rational poles as well as differential symbols.

### Searches

Prescribed `msearch.py Q27 <item>` searches (2026-10-24):

- LeanFinder: `Completed differential pullback to a smooth curve branch rational
  Laurent series differentials parameter change`. Eight hits, chiefly RatFunc
  Laurent constructions, Laurent-series completion comparisons and Weierstrass
  division; none state this completed differential/naturality theorem.
- Loogle: `"KaehlerDifferential", "AdicCompletion"`. Zero hits.
- LeanSearch: `Smooth curve completed Kahler differential pullback Laurent series
  chain rule`. Eight hits include `KaehlerDifferential.D`, `.map_D`,
  `.tensorKaehlerEquivBase` and the categorical differential map; no whole statement.
- Mathlib grep through msearch: `KaehlerDifferential.*(PowerSeries|AdicCompletion)|
  (PowerSeries|AdicCompletion).*KaehlerDifferential`. Zero hits.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for that pattern,
  `LocalCompletion`, `CompletedDifferentials`, `SmoothBranch`,
  `smooth.branch.*differential`, and the item id. No exact theorem. Read the existing
  completion, Jacobian and continuous-free modules and the upstream curve definition.
  `Sheaf.AlgebraicGeometry.FormalPlaneAdjunctionLattice` ends with an E existence
  clause in its more specialized plane-adjunction theorem; it omits the other clauses
  and cannot replace this node. Its other definitions were not duplicated.
- Read Mathlib's actual power-series, multivariate partial, and Laurent-series
  derivative definitions, the differential map and localization interfaces, and
  `RingHomInvPair.of_ringEquiv` / `.of_ringEquiv_symm`. No new derivative or map
  definition is required. `dag/lean_names_upstream.json` has no attachment for this item.

Validation: all compiles used the prescribed scompile wrapper. Final sandbox-mode
compile and library-mode compile both succeeded, with no errors or warnings.
The final file has explicit universe/variable binders, disables auto-implicit
binding, has no diagnostic commands, and all lines have at most 100 characters.
No STATEMENT-DISPUTED issue or node fault remains.

## Second reading by Q27

This is a separate rereading by the same dispatched worker; no separate agent was
started, as the dispatcher brief prohibits it. Independent review is the maintainer's.
I reopened the node statement, its dependency records, and the delivered Lean file.
The hypothesis/conclusion tables above reflect that second pass. In particular,
I checked that A is the localization rather than the completion, that E is T-linear
rather than merely k-linear, that delta is injective before extension of scalars,
that beta is not asserted injective, and that the formula on dA is for every h in R.
I checked the presentation quantifier has no dummy-variable bound, that g is a
formal series family, and that the Jacobian partials use the recorded derivation.
I checked tau's uniqueness, the lattice equality, and all three squares on whole
modules after the precise semilinear scalar transport. No mathematical mismatch
was found. Elaboration changes during the first pass only qualified
`AlgebraicGeometry.Smooth` and supplied the existing inverse-pair proofs explicitly
in the two `LinearEquiv` types; they changed no hypotheses or conclusions.
