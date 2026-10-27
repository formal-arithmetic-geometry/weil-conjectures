## Worker report

The module `Sheaf.Algebra.Homology.PolynomialDiagonalAdjunctionScalarNaturality`
states `AlgebraicGeometry.polynomial_diagonal_adjunction_scalar_naturality`, with
one postponed proof. It defines only the public abbreviation
`polynomialDiagonalAdjunctionTargets`: the conjunction of the existing
`DerivedCategory.IsPseudoCoherent` and `DerivedCategory.finiteTorAmplitude`
predicates, with restriction along the structure map. This helper groups the
node's two target hypotheses; it introduces no new mathematical construction.
All coinduction, tensor, differential, diagonal-class and comparison data are
existing library constructions. No source statement or proof is changed.

Hypothesis-by-hypothesis correspondence:

- The node's rings R,A,R',A' are the Lean rings R,B,S,D. Each has `CommRing`;
  `Algebra R B` and `Algebra S D` give the structure maps. The binders
  `IsNoetherianRing R`, `IsNoetherianRing B`, `IsNoetherianRing S` are exactly
  the three Noetherian assumptions. There is no extra Noetherian, flatness or
  finite-presentation assumption on D.
- `hflat : RingHom.Flat (algebraMap R B)` and
  `Algebra.FinitePresentation R B` are the original flat finite-presentation
  assumptions. No flatness of `F.base : R →+* S` is imposed.
- `C,E : PolynomialKoszulChart` carry the unprimed/primed polynomial
  presentations. Their quotient maps are surjective by their `surjective`
  fields. `hC,hE : Function.Bijective ...coordinates` say that these are the
  polynomial rings themselves, not proper localizations. Their `n` fields
  are arbitrary natural numbers and include zero. Transport by each coordinate
  algebra isomorphism recovers the literal standard MvPolynomial carrier.
- `F : KoszulDiagonalChartChange C E` carries the base, algebra and ambient
  maps, their commuting equations, equal dimensions and the ordered-variable
  identifications. `F.differential` carries the ordered volume to the primed
  volume. The top line is free rank one, so this fixes that semilinear map.
- `hbase` states that D is the pushout of R→B and R→S: D is exactly B tensor_R S,
  up to the canonical carrier identification. Polynomial coordinates and
  `F.coordinate` identify the ambient map with polynomial coefficient extension,
  hence E.P with C.P tensor_R S. `hquotient` records the induced quotient pushout,
  D = B tensor_(C.P) E.P. Both squares hold for the tensor algebras in the node;
  they express those algebras rather than add a restriction on scalar extension.
- Q,Q' are literally `B ⊗[R] B`, `D ⊗[S] D`. The first coprojections are the
  displayed `Algebra.TensorProduct.includeLeft` ring maps. The diagonal rings
  are related by `F.diagonalRing`, acting on both tensor factors.
- All objects and arrows lie in ordinary `DerivedCategory (ModuleCat ...)`.
  These use the existing ordinary-module closed derived tensor construction
  and its K-flat scalar extension. There is no abstract substitute category.
- The node's C,C' are `C.model,E.model`, coinduction of their top differential
  line in degree -n. `PolynomialKoszulChart.coefficientShiftIso` is the existing
  identification with Omega^n[0][n]; coinduction commutes with shift. Thus this
  is the displayed coinduction-of-Omega shifted by n, including its
  precomposition action, not just its underlying polynomial-ring object.
- `polynomialDiagonalAdjunctionTargets R B T` imposes pseudo-coherence over B
  and finite Tor amplitude of the restriction over R. The imported
  `finiteTorAmplitude` tests tensor with every R-module in degree zero in a
  single finite interval. Its definition permits a>b only for a zero object;
  widening to [min a b,max a b] gives a≤b, so this is exactly the node's
  finite-interval condition, including the zero case. The analogous predicate
  over S,D is applied explicitly to the scalar extension of T in `hT'`.

Clause-by-clause correspondence:

- The existential `c` is an isomorphism from derived extension of `C.model`
  to `E.model`. `F.IsComparison c` fixes it by the extended evaluation-at-one
  counit and `F.coefficientMap`. That coefficient map is the scalar mate of
  the ordered differential map in degree -n. This is precisely the shifted,
  coefficient-identified exchange of
  `lem-sfb-perfect-coinduction-tor-independent-exchange`, not an arbitrary
  isomorphism of the two objects.
- The existential κ,κ' satisfy `IsKoszulDiagonalNormalization`. This predicate
  pastes the evaluation-normalized graph exchange, coinduction transitivity
  and the ordered top Koszul cocycle. Their `diagonalClass` is the actual
  coinduction adjunct of the inverse graph trace. The two `IsIso` class-map
  clauses are the relative-dualizing pair condition. These are the normalized
  affine polynomial-chart pairs chosen in the node, with contraction of the
  ordered dual equation and differential to 1. No independently chosen global
  dualizing pair is assumed or compared.
- `ρ,ρ'` are simultaneous families of `Equiv` on precisely the two Hom sets
  in the node, for every allowable target. Their existential quantifiers precede
  the target quantifiers. The first two conjuncts assert naturality for every
  morphism between allowable targets in each category.
- The next two conjuncts supply allowability of each dualizing model and the
  equations `ρ C.model h (C.diagonalClass κ) = 𝟙 C.model` and its primed version.
  These are exactly both specified normalizations. The theorem uses Hom
  equivalences, as requested; the polynomial RHom reduction is imported and
  used by the six-step proof. A natural Hom family with this normalization
  is uniquely determined: naturality at f:C→T forces its inverse to send f
  to xi followed by f_1. Hence the normalized family obtained by H^0 of that
  reduction is exactly the family characterized here; a second unrelated
  adjunction or an arbitrary normalization is not permitted by the statement.
- The existential `h` is the first-coprojection commuting equation used to
  form the canonical tensor associator `koszulDiagonalExtensionSquare`.
  The existential diagonal iso `d` satisfies `F.IsDiagonalComparison d`,
  which fixes its underlying ordinary map on every b to `F.ring b` and takes
  the actual degree-zero scalar mate. Thus d is the canonical
  A tensor_Q^L Q' ≅ A' comparison.
- For every allowable T, its allowable extension and every v, the final equation
  applies ρ' to `d.inv ≫ extension.map v ≫ square.hom.app T`. This is v' under
  exactly the two tensor identifications specified in the node. Its right side
  is `c.inv ≫ extension.map (ρ T hT v)`. Lean's `≫` reads in application order,
  so it is `(ρ_T(v) tensor_A^L A') ∘ c^{-1}` as written in the node. The source
  of this last composition is C', and its target is T'. No gluing or proper
  duality statement has been added.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `Module.Flat`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`; chart coordinates and
  quotients use the existing polynomial algebra evaluation interface.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`:
  `DerivedCategory.exists_derivedTensor_second_factor_functor`; the scalar
  extension used is `relativeDualizingDerivedExtension` in
  `Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, the existing closed Hom.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`:
  `ModuleCat.derivedCoinduction`, `ModuleCat.derivedCoinductionAdjunction` and
  their evaluation/model constructions.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, its derivation;
  `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `exteriorPower`,
  `ExteriorAlgebra`; chart top lines and volumes use these, including 0th power.
- `Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentExchange`:
  `ModuleCat.perfectCoinduction_torIndependent_exchange` and the actual counit
  mate `ModuleCat.coinductionScalarExchange`; the chart `IsComparison` equation
  specifies the same mate after identifying its derived scalar presentations.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`.
- `Sheaf.TraceFormula.PolynomialDiagonalRhomReduction`:
  `AlgebraicGeometry.polynomial_diagonal_rhom_reduction` and its natural family.
- `Sheaf.AlgebraicGeometry.RelativeDualityPolynomialChart`:
  `AlgebraicGeometry.exists_relativeDualityPolynomialChart`; the ordered
  affine interpretation uses its normalized chart convention.
- `Sheaf.Algebra.Homology.PolynomialKoszulDiagonalData`:
  `PolynomialKoszulChart` and its `model`, `coefficientShiftIso`, `diagonalClass`;
  `IsKoszulDiagonalNormalization`; `KoszulDiagonalChartChange`, its
  `IsComparison`, `IsDiagonalComparison`, `diagonalRing`; and
  `koszulDiagonalExtensionSquare`. Its already-landed owner
  `def-sfb-polynomial-koszul-diagonal-data` is added to stmt_deps, as allowed
  for use of landed definitions. No dependency repair or new node is needed.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`:
  `DerivedCategory.finiteTorAmplitude` and `DerivedCategory.torAmplitudeIn`.

All already-stated proof dependencies are imported, publicly when also statement
inputs and privately otherwise. Mathlib leaves are imported from
`Mathlib.RingTheory.FiniteType`, `Mathlib.RingTheory.Flat.Basic` and
`Mathlib.CategoryTheory.Monoidal.Tor`. The proof docstring contains all six DAG
steps and names their dependencies, including relative perfection, the perfect
polynomial quotient, the normalized Koszul class and H^0 of RHom.

Edge cases checked mathematically before writing:

- n=0: the chart's top coefficient and graph contraction are the empty wedge
  and empty Koszul complex; no positivity or nonempty-index assumption occurs.
- A=0 and A'=0: all corresponding Hom sets are singletons, including the
  identity normalization; no `Nontrivial` instance is assumed.
- T=0: pseudo-coherence and finite Tor amplitude hold; its equivalences and
  scalar equation have the unique possible values.
- Identity base change: the first-pullback and diagonal maps are the normalized
  identity identifications, and the equation reduces to the same adjunction.
- R'=R/I: flatness of the base change is never assumed; the Tor independence
  uses the R-flatness of A and P, not that of R'.
- A=R[t]/(t²): there is no smoothness, invertibility or perfectness-over-Q
  hypothesis; only the flat finite-presentation hypotheses enter.
- Universes: every ring and module test is in the common ambient universe u,
  as in the recorded polynomial/Koszul constructions; no smaller independently
  quantified module-testing universe is introduced.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Naturality under scalar extension of polynomial
  diagonal derived Hom adjunction normalized by its universal class"`: eight
  hits, including `PolynomialLaw.isCompat`, `PolynomialLaw.toFun'_eq_of_diagram`
  and polynomial-law tensor formulas; no derived polynomial adjunction.
- `msearch.py ... loogle '"dualizing", "baseChange"'`: OK, zero hits.
- `msearch.py ... grep 'polynomial.*diagonal|diagonal.*coinduction'`: two
  unrelated hits, Matrix/Charpoly/Univ.lean:93 and PowerSeries/Substitution.lean:636.
- `msearch.py ... leansearch "A normalized polynomial diagonal derived Hom
  adjunction is natural under scalar extension of the base ring"`: eight
  ordinary ModuleCat scalar restriction/extension/coextension adjunction hits;
  no derived diagonal normalization or scalar square.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for `polynomial.*diagonal.*adjunction|diagonal.*scalar.*naturality` and both
  proposed declaration names: no existing declaration. Exact item-id search
  on the upstream Lean tree also had no hits.
- Reading the nearby `ArbitraryPolynomialGraphClassBaseChange` and
  `PolynomialKoszulDiagonal{Data,System,Class}` modules found the exact canonical
  class and mate definitions reused here, but no arbitrary-target Hom naturality
  statement. Those existing objects are used without private copies.

Validation: prescribed `scompile.py` compiled both its sandbox probe and the final
library module cleanly (2.1 s and 2.0 s); no errors or warnings. There is exactly
one `sorry`, in the main theorem. The helper abbreviation has real data.
No STATEMENT-DISPUTED flag, source correction, new node or dependency module.

## Second reading by Q22

This is a separate self-check pass by the dispatcher worker; the user explicitly
prohibited subagents. It does not claim another worker has reviewed the statement.
The maintainer's independent review remains the next mathematical review.

Reopened the node and final Lean file and checked every clause above. In particular,
checked that the two families are outside the target quantifier; both source and
primed naturality equations allow arbitrary morphisms; both normalizations supply
the required target hypotheses rather than assume them; all ring-zero cases remain;
`F.IsComparison` fixes the coinduction mate; `d` is fixed on ordinary elements; and
the final `c.inv ≫ ...` has the required direction. Also checked that the source
ring of the first coprojection is B, not the multiplication ring, and that the
scalar map acts on both diagonal factors. The chart and pushout presentation changes
only carriers, not hypotheses or objects. Finite Tor amplitude uses existing
ordinary-module tensor and all base modules. No mismatch or further edit was found.
