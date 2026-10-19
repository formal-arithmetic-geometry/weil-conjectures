## Worker report

The module `Sheaf.Paper.TwFrobeniusAction` defines the geometric Frobenius
automorphisms for the canonical constant coefficient object. `twFrobeniusComplex`
returns the ordinary and compact-support automorphisms of the cohomology complexes;
`twFrobeniusAction` applies the homology functor in every integer degree.
`twFrobeniusOrdinaryIso` and `twFrobeniusCompactIso` are construction helpers
which perform the same canonical composite on a supplied Weil pair before
specializing to the fixed constant pair. All data
are actual composites of the recorded maps. This delivery introduces no theorem,
axiom, extra node, dependency module, or postponed proof.

Hypotheses and clauses, read against the complete current node:

* `D : FiniteFieldDatum.{u}` contains the prime `p`, positive exponent, `q = p^r`,
  finite field of cardinality `q`, fixed algebraic closure, and its algebra map.
  `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give exactly the coefficient prime.
* `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`, and
  `[IsAlgClosure (Padic l) Ω]` specify the chosen coefficient closure. The scheme
  and coefficient universes are independent.
* `Y₀ : Over (Spec (.of D.k₀))` is the finite-field model. The instances
  `LocallyOfFiniteType Y₀.hom`, `QuasiCompact Y₀.hom`, and `IsSeparated Y₀.hom`
  express separated finite type. The geometric scheme is the dependency's
  `(D.geometricFiber Y₀).left`, with its recorded structure map.
* `c₀ : Compactification Y₀.hom` retains a presentation of the compact-support
  functor, as in both recorded transport declarations. Such presentations exist
  for the given separated finite-type schemes over the field; this argument
  requires neither properness nor smoothness of `Y₀`.
* The coefficient category is the existing
  `generalAlgebraicallyClosedConstructibleCategory`, also the literal carrier of
  the currently recorded `intrinsicPbcQbarCategory`. Its stages use
  `sfIntegralConstructibleCategory` and raw `sfRationalConstructibleCategory`.
  The completed coefficient sheaf, uniform reduction amplitude, scalar extensions,
  and finite-compositum Hom quotients are inherited, not defined again here.
  The integral stratified-perfect characterization and finite-free completed
  scalar comparison are the node's supplied justification for using this
  presentation of the conventions. Their tensor and reduction identifications
  remain the recorded canonical ones; no equivalence is postulated in this file.
* `constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω` is exactly the canonical
  constant Weil object of the recorded dependency. Its defining stage is
  `Padic.finiteCoefficientBase l Ω`, the image of `ℚₗ` in `Ω`; its `.carrier`
  is the constant coefficient pair and `.str` is the canonical Weil isomorphism.
* The pullback in this fixed pair is the recorded geometric Galois Frobenius,
  `D.geometricFrobenius Y₀`, namely `id × Spec(γ)` with `γ(z)` the inverse of
  `z ↦ z^q`. Its affine formula and semilinearity are inherited from
  `FrobeniusDetailed`; no inverse to the relative scheme Frobenius is used.
* `frobeniusCohomologyTransport ... W.carrier` gives precisely `τ` and `τ_c`.
  `frobeniusCohomologyQbarFunctor ... false` and `... true` give ordinary and
  compact cohomology on the entire common-stage category. Each component of
  `twFrobeniusComplex` uses the helper composite `eqToIso sourceEq`, then
  `asIso τ`, then `(eqToIso targetEq).symm`, then that functor's `mapIso W.str`.
  These equality isomorphisms use only the recorded source and target
  identifications, starting and ending at the common-stage functor value. Thus the underlying arrows are the two displayed formulas
  `RΓ(θ) ∘ τ` and `RΓ_c(θ) ∘ τ_c`, in Lean's forward composition order.
* The two `IsIso` instances are the third clause of
  `frobeniusCohomologyTransport_isIso`, projected from its algebraically closed
  coefficient case. Functors carry the Weil isomorphism to an isomorphism.
  Consequently the outputs are actual isomorphisms, including their inverses.
* `i : ℤ` and `DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) i`
  give exactly `H^i` for every integer. `H.mapIso` produces the two requested
  `Ω`-linear automorphisms, since arrows in `ModuleCat Ω` are linear maps.
  No finite-dimensionality or nonvanishing assumption is added.
* Repeating the definition with another specified finite-field model and its
  geometric Frobenius gives the same notation after base change. This clause
  asserts no extra comparison equation between unrelated models.

Dependency declarations read and used (directly, or through their recorded
construction):

| Node | Module | Declaration |
| --- | --- | --- |
| def-tw-conventions | Sheaf.Paper.TwConventions | WeilConjectures.TwConventions |
| def-weil-pbc-qbar-category | Sheaf.Paper.IntrinsicQbarCategory | WeilConjectures.intrinsicPbcQbarCategory |
| lem-weil-pbc-integral-stratified-perfect-characterization | Sheaf.Paper.IntegralStratifiedPerfectCharacterization | AlgebraicGeometry.Scheme.integralStratifiedPerfectCharacterization |
| def-weil-derived-complete-integral-detailed | Sheaf.Paper.SfIntegralConstructible | WeilConjectures.sfIntegralConstructible |
| lem-weil-finite-free-completed-scalar-comparison | Sheaf.Paper.FiniteFreeCompletedScalarComparison | WeilConjectures.finiteFreeCompletedScalarComparison |
| def-weil-rationalization-karoubi | Sheaf.Paper.SfRationalizationKaroubi | WeilConjectures.sfRationalConstructibleCategory |
| prop-weil-pbc-scalar-extension | Sheaf.Paper.PbcScalarExtension | AlgebraicGeometry.Scheme.pbcCoherentScalarExtension |
| def-weil-algebraically-closed-coefficients | Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | WeilConjectures.generalAlgebraicallyClosedConstructibleCategory |
| def-weil-frobenius-detailed | Sheaf.AlgebraicGeometry.FrobeniusDetailed | WeilConjectures.FiniteFieldDatum.geometricFrobenius |
| def-weil-constant-weil-structure | Sheaf.Paper.ConstantWeilStructure | WeilConjectures.constantWeilAlgebraicallyClosedComplex |
| def-weil-ordinary-compact-cohomology | Sheaf.Paper.CommonStageCompactWeilCohomology | WeilConjectures.adicOrdinaryCohomology / adicCompactCohomology, and the reexported coefficient-complex functors |
| def-weil-frobenius-cohomology-transport | Sheaf.SixFunctors.FrobeniusCohomologyTransport | WeilConjectures.frobeniusCohomologyTransport |
| def-weil-global-geometric-frobenius | Sheaf.Paper.GlobalGeometricFrobenius | WeilConjectures.globalGeometricFrobenius |
| lem-weil-frobenius-cohomology-transport-iso | Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | WeilConjectures.frobeniusCohomologyTransport_isIso; frobeniusCohomologyQbarFunctor, frobeniusCohomologyQbarSourceEq, frobeniusCohomologyQbarTargetEq |

The global-geometric-Frobenius dependency states the identical two-arrow recipe
at a finite rational stage; this definition performs its constant-object
specialization in the recorded algebraically closed common-stage presentation.

Edge cases checked: the empty scheme and zero cohomology require no nonempty or
nonzero binder, and functorial images of isomorphisms still apply. Negative, zero,
and positive degrees all occur because the degree is an integer. The smallest
prime field and exponent one are allowed by `FiniteFieldDatum`; `l = p` is
excluded exactly as in the source. The coefficient stage is the base stage,
including identity extensions; no strict extension is assumed. Independent
coefficient and scheme universes are preserved by the dependency's exact ULift
coefficient transport. Nonproper separated finite-type schemes are allowed.

Searches for an existing declaration:

* `msearch.py ... leanfinder "geometric Frobenius action automorphism ordinary
  compactly supported etale cohomology constant coefficients"`: eight results
  about arithmetic Frobenius or Witt-vector isocrystals, no such cohomology
  construction.
* `msearch.py ... loogle '"frobenius", "cohomology"'`: zero hits.
* `msearch.py ... grep 'geometricFrobenius|geometric Frobenius|frobeniusCohomology'
  AlgebraicGeometry`: zero Mathlib hits.
* `msearch.py ... leansearch "geometric Frobenius action on ordinary and compact
  support cohomology with algebraically closed l-adic coefficients"`: eight
  results, all field Frobenius, semilinear ring Frobenius, or Witt-vector
  isocrystals; none defines the requested action.
* `rg` for `twFrobenius|def-tw-frobenius-action|FrobeniusAction` in the upstream
  `WeilConjectures`, side `lean/Sheaf`, and upstream name index found no match.
* The broader upstream Frobenius/cohomology search found
  `WeilConjectures/WeilSheaf/Cohomology.lean`. Its full ordinary and compact
  cohomology signatures were read: they use the older `AlgebraicGeometry.WeilComplex`
  and fixed `PadicAlgCl` coefficients, rather than the node's intrinsic
  common-stage completed-coefficient constant object and arbitrary chosen
  coefficient closure. They are not an existing declaration of this node.
  The side search found the recorded generic transport and finite-stage global
  operator dependencies, reused here.

No new statement correction is made. The existing node already spells out the
geometric Galois Frobenius correction to the blueprint's informal inverse phrase;
its reviewed split report explains that correction. The current blueprint
main-20261015 statement was opened and checked. There is no unresolved statement
dispute.

## Second reading by Q87

Re-read the current node and the draft as a separate pass, checking each binder,
the base coefficient stage, the order of composition, both endpoint equality
transports, and every integer degree. The ordinary component uses `false` and
the compact component uses `true` consistently. The source equality first
identifies the common-stage functor value with the transport source. The inverse
of the target equality precedes `mapIso W.str`, returning to the original
common-stage functor value. This reading found and corrected the earlier placement
of the source equality, which had instead mixed these endpoint conventions.
The construction helpers abstract the Weil pair during elaboration, avoiding
repeated unfolding of the constant object without changing the composite. `H.mapIso` therefore yields
endomorphism isomorphisms, not merely maps to the pullback cohomology. The
recorded `IsIso` projections select both transports, rather than only the exchange
maps. No private coefficient category, arbitrary operator, properness hypothesis,
or finite-dimensionality hypothesis was found. This is the dispatched worker's
second reading; the maintainer supplies the independent review, as the dispatch
brief specifies, and no additional agent was started.

Validation uses the required `scompile.py` and `deliver2.py` wrappers. The
endpoint repair compiled cleanly as a sandbox and as the named library module
in 10.4 and 10.1 seconds respectively, within the unchanged 60-second limit.
All fourteen recorded dependency modules are imported directly in the final
module. The final dry run checks the updated imports and all delivery fields.
