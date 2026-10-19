## Worker report

The module `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` states
`WeilConjectures.FiniteFieldDatum.schemeGaloisComparison_coefficientChange`.
Its only proof is `sorry`. There are no new definitions, postponed helper theorems,
new nodes, dependency repairs, or statement corrections.

Sources read: the complete item and its four proof steps; all eight statement-dependency
node statements and their Lean records; the recorded primary declarations and docstrings;
`thm-trf-finite-coefficient-map.proof.md` (final sentence) and
`prop-trf-scheme-galois-comparison.proof.md` (both paragraphs), in blueprint main-20261015.
No repair-note file for this item was present. The proof docstring reproduces the four-step
factorization/compositor/trivialization calculation of the node.

Hypothesis and clause correspondence:

- The prime p, a >= 1, q = p^a, finite field k0 of cardinality q, its fixed algebraic
  closure k, and the base inclusion are exactly `(D : FiniteFieldDatum.{u})`. The
  structure fields are `prime`, `exponent_pos`, `cardinality_eq`, `card_base`,
  `algebra_closure`, and `isAlgClosure`.
- The finite-type k0-scheme is `X₀ : Over (Spec (CommRingCat.of D.k₀))` with
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`. Their conjunction is finite type.
  X is `(D.geometricFiber X₀).left`, the existing actual base change.
- Phi^m is `D.schemeFrobeniusIterate X₀ m`. The geometric Galois iterate is
  `HPow.hPow (α := End (D.geometricFiber X₀).left) (D.geometricGaloisFrobenius X₀) m`.
  Both are underlying scheme endomorphisms; no false k-linearity is assumed for g.
- A and B are arbitrary `Type u` with `[CommRing] [Finite]`; the zero ring is allowed.
  `φ : A →+* B` is any unital map. `hA` and `hB` each state existence of an integer
  annihilator n with `IsUnit (n : D.k)`. Since the datum gives characteristic p, an
  integer is a unit in k precisely when it is prime to p. Thus these are exactly the
  two prime-to-p annihilator conditions, in the recorded comparison's own signature.
- `K : proEtaleDerivedCategory (D.geometricFiber X₀).left A` is arbitrary in the
  ordinary unbounded derived category of constant A-module sheaves. Its underlying
  definition is the standard localization of cochain complexes, with coefficient
  `constantSheaf ... CommRingCat` of `ULift A`. This is the constant-ring presentation
  of `def-weil-pbc-proetale-modules`, whose canonical constants-to-continuous-functions
  realization identifies the finite continuous-function coefficient sheaf.
- T is `directImageScalarExtension φ X`, an abbreviation for
  `proEtaleRingDerivedExtension (proEtaleConstantRingMap φ)` and hence the universal
  ordinary derived tensor, with its K-flat computation, rather than an arbitrary functor.
- The specified inverse comparison c_h is `(directImageScalarPullbackIso φ h).hom`.
  This is the published constant-ring specialization of `proEtaleReductionPullbackIso`.
  Its source is `T ⋙ h_B^*`, its target `h_A^* ⋙ T`, and its coefficient square is
  naturality of the canonical constant-section maps. Its ordinary tensor-unit
  normalization is the inverse mate of the exact restriction/pullback comparison.
  The scalar-six comparison is the mate of the same restriction comparison in internal
  condensed modules. Under the finite-discrete monoidal constant-ring identifications,
  the scalar unit and sectionwise restriction comparison agree. Thus the existing
  constant-ring comparison is precisely the transported inverse of scalar-six (1),
  rather than a freely chosen isomorphism. This avoids building a second transport.
- Kappa is the existing `D.canonicalSchemeGaloisComparison X₀ A hA m hm` (and B).
  Its definition selects the same iterate family from `schemeGaloisComparison`, with
  the site-relative-Frobenius projection equation, adjunction-unit section equation,
  factorization equation and multiplicativity clauses retained. It is not a bare
  choice of a natural isomorphism.
- `(m : ℕ) (hm : 1 ≤ m)` is every positive integer, including 1. No separate stronger
  assertion for m = 0 is imposed.
- Lean composes left to right with `≫`. Accordingly the left side is
  `c_Phi.hom.app K ≫ T.map (kappa_A.hom.app K)`; the right side is
  `kappa_B.hom.app (T.obj K) ≫ c_g.hom.app K`. These are exactly the displayed equality
  of the node, from `L(Phi^m)_B^*(TK)` to `T(L(g^m)_A^*K)` in D_B.
- There are no flatness, finite Tor-amplitude, boundedness, constructibility,
  separatedness or nonemptiness binders.

Dependencies used (recorded modules/declarations):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, `.geometricFiber`.
- `Sheaf.SixFunctors.SchemeFrobenius`: `.schemeFrobeniusIterate`, `.geometricGaloisFrobenius`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientScalarMap_locallyBijective`
  and its published realization; the signature uses the same constant coefficients
  in `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem specify
  ordinary universal derived extension. `directImageScalarExtension` reuses the
  existing pro-etale specialization of this universal derived operation.
- `Sheaf.SixFunctors.ScalarSixPullback`: `scalarSixPullback`,
  `ScalarSixPullbackData.theta`, `.thetaNormalization`, `.composition`.
- `Sheaf.Paper.FiniteDiscreteCondensedRing`:
  `Profinite.finiteDiscreteCondensedRing_constant`; and
  `Sheaf.Paper.FiniteDiscreteSchemeRing`:
  `AlgebraicGeometry.ProEtale.finiteDiscreteSchemeRing_constant` (current server sources
  read using `scompile.py --source`, as these two sources are absent locally).
- `Sheaf.SixFunctors.SelectedSchemeGaloisComparison`:
  `WeilConjectures.FiniteFieldDatum.canonicalSchemeGaloisComparison`.
- Added the already landed definition node `def-sp-constant-scalar-pullback-comparison`
  to `stmt_deps`, as expressly permitted for landed notions. Its existing
  `Sheaf.SecSmoothPurity.DirectImageScalarExchange` declarations
  `directImageScalarExtension` and `directImageScalarPullbackIso` supply exactly T and c.
  Its full statement, node record, source signatures and normalization docstrings were read.
- Proof imports: `Sheaf.Paper.IntegralFinitePullbackComposition` (the recorded general
  canonical composition alias) and `Sheaf.AlgebraicGeometry.FrobeniusFactorization`.
  The other stated proof dependencies are already public imports. The proof prerequisite
  `lem-trf-absolute-frobenius-coefficient-naturality` has no recorded Lean declaration,
  so there is no module to import; it is named in the proof docstring. The statement
  needs no declaration from that theorem and does not manufacture one.

Edge cases checked mathematically before writing: m = 1 is included; arbitrary nonreduced
and empty X0 are allowed; A or B zero is allowed (the unit-annihilator witness can be n = 1
for the zero ring); φ can be the identity; φ can be non-flat, for example
Z/ell^2 -> F_ell with ell != p; K can be zero or unbounded. All use the same ordinary
uncompleted tensor and specified maps. Scheme and coefficient sizes use the existing
universe-u constant-ring interface and its u+1 section universe, without equating the
site's distinct object and morphism universes.

Searches performed:

- `msearch.py ... leanfinder` query "The canonical scheme Frobenius to geometric Galois
  Frobenius pullback comparison commutes with derived extension of finite coefficient rings":
  8 hits, scheme pullback tensor-spectrum identities and Witt-vector isocrystal Frobenius;
  none states this derived coefficient square.
- `msearch.py ... loogle` query `Functor.map, NatTrans.app`: 0 hits with unknown identifier
  `NatTrans.app`; recorded as an invalid query, not evidence of mathematical absence.
- `msearch.py ... grep` query
  `(Frobenius|frobenius).*(scalar|coeff|tensor)|(scalar|coeff|tensor).*(Frobenius|frobenius)`
  under Mathlib/AlgebraicGeometry: 0 hits.
- `msearch.py ... leansearch` query "Canonical pullback comparison for change of coefficient
  ring on sheaves of modules commutes with Frobenius trivialization": 8 hits, generic
  sheaf-module pullback, pullback adjunction, free-pullback isomorphisms, and vector-bundle
  Trivialization.pullback_linear. No exact derived Frobenius statement.
- `rg` of Frobenius/coefficient/scalar/tensor combinations in the source project's
  `WeilConjectures` and the shared `lean/Sheaf` found specialized quotient-level
  `frobeniusSchemeGalois_reduction` and citations in local-Frobenius transport, but no
  theorem for arbitrary finite ring homomorphisms. The source's trace-formula Frobenius
  framework and WeilSheaf tensor identities concern other coefficient structures.
- Exact item-id grep in the source project has no hit. The side project has citations
  in `LocalFrobeniusTransportNormalization.lean` and `FrobeniusCoefficientReductionCoherence.lean`.
- Searches for the proposed declaration/module name in Mathlib, the source project,
  side project and `dag/lean_names_upstream.json` found no existing declaration.
- Search of the DAG for constant-scalar/pullback constructors found the existing owner
  `def-sp-constant-scalar-pullback-comparison`; no new definition node was created.

Validation: required `scompile.py Q65 lem-trf-scheme-galois-coefficient-change <module>`
passed both sandbox and library contexts (5.3 s and 5.9 s), with no errors or warnings.

## Second reading by Q65

I reread the node and completed file after compilation. This is a worker self-check;
the maintainer supplies the independent delivery review under the dispatcher brief.
The datum fields contain all p,a,q,k0,k hypotheses. Finite type is locally finite type
plus quasi-compact, with no separatedness. The two rings each have precisely the finite,
commutative and prime-to-p annihilator hypotheses, including the zero ring. The homomorphism
is arbitrary and the object is in the ordinary unbounded category. I checked the source
and target of `directImageScalarPullbackIso`: its hom, rather than its inverse, is c_h
in this node's direction. Reading the comparison selector's body confirms that kappa is
selected from the normalized iterate family, not supplied as a parameter. Both sides use
that same selector at the identical exponent and object; the displayed `≫` order is the
reverse of the source's right-to-left composition notation, as required. No missing
hypothesis or clause was found. The only node addition is the existing definition owner
for T and c. No definitions, helper proofs or interface repairs were needed.
