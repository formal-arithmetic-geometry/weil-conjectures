## Worker report

States `WeilConjectures.PurityFiniteSetting.isIso_smoothPurityMap` in
`Sheaf.Paper.FiniteCoefficientSmoothPurity`. Its sole proof is `sorry`.
No definitions, dependency repairs, new nodes, or statement changes are delivered.
The existing `smoothPurityMap` supplies the canonical arrow; the conclusion is
`IsIso (P.smoothPurityMap f d K hK)`, rather than existence of an unspecified iso.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Global finite-field datum `(p,a,q,k₀,k)` | `P : PurityFiniteSetting.{u}`, field `P.field : FiniteFieldDatum.{u}`; its prime, positive exponent, cardinality equation and fixed algebraic closure are bundled |
| Prime `ell ≠ p` and fixed coefficient closure | `P.coefficients`, with `[Fact P.coefficients.l.Prime]`, `.different`, and `.Qbar` with its algebraic-closure structure |
| Finite extension in the fixed closure | `P.extension : IntermediateField (Padic P.coefficients.l) P.coefficients.Qbar`, with `P.finiteExtension` |
| Valuation ring, uniformizer, and quotient A | `P.Ring`, definitionally `Padic.coefficientExtensionRing P.coefficients.l P.extension P.level`; its recorded construction uses `coefficientExtensionIntegers` and `coefficientExtensionUniformizer` |
| Positive integer n | `P.level : ℕ`, `P.level_pos : 1 ≤ P.level` |
| X and Y are k-schemes | `[X.Over (Spec (.of P.field.k))]`, and the corresponding instance for Y |
| X and Y are finite type over k | `LocallyOfFiniteType` and `QuasiCompact` on both structure morphisms |
| X and Y are separated over k | `IsSeparated` on both structure morphisms |
| Morphism f over k | `(f : X ⟶ Y)` and `[f.IsOver (Spec (.of P.field.k))]` |
| Separated f | `[IsSeparated f]` |
| Finite type of f | `[LocallyOfFiniteType f] [QuasiCompact f]`; these are source-implied properties of a morphism between the stated finite-type k-schemes, also explicitly present in the recorded map's signature |
| Smooth, pure relative dimension d ≥ 0 | `(d : ℕ) [SmoothOfRelativeDimension d f]`; this class implies `Smooth f` and expresses constant fibre dimension using standard smooth charts |
| Small pro-etale derived category with finite coefficients | `(K : Scheme.proEtaleDerivedCategory Y P.Ring)`, modules over the actual constant coefficient ring sheaf |
| Bounded constructibility and finite Tor amplitude | `hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K`; this is the conjunction of `intrinsicFiniteTorsionConstructible` and `HasFiniteProEtaleTorAmplitude` |
| Twist convention K(m) = K tensor A(m) | Reused inside `smoothPurityMap`: `smoothPurityReassociation` and `diagonalTwist` from the coefficient-twist dependency; no new twist is introduced |
| Source Lf* K(d)[2d] and target Rf! K | Exactly the source and target of the recorded `P.smoothPurityMap f d K hK`; it retains the intrinsic object K and realizes the specified exceptional functor |
| The specified gamma is an isomorphism | `IsIso (P.smoothPurityMap f d K hK)` |
| Six operations and bounded-class adjunction conventions | Those of the recorded map and its dependencies, with the explicit bounded-class discharge module imported; no unrestricted ambient adjunction assumption |

Dependency declarations read and reused (transitive public imports suffice where noted):

- `Sheaf.Paper.SmoothPurityMap`:
  `WeilConjectures.PurityFiniteSetting.smoothPurityMap`, its reassociation,
  tensor composite, exceptional functor and exact realization helpers.
- `Sheaf.Paper.PurityFiniteSetting` (through the map):
  `WeilConjectures.PurityFiniteSetting`, `.Ring`, `.Coefficient`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` and
  `Sheaf.Paper.FiniteTorAmplitude` (through the map):
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible` and
  `WeilConjectures.finiteTorConstructible`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth` (through the map):
  `AlgebraicGeometry.SmoothOfRelativeDimension`, whose docstring and full signature
  specify standard-smooth relative dimension; also read `Smooth`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale` (transitive):
  `AlgebraicGeometry.Scheme.ProEt`, the weakly-etale small site, with object universe
  u+1 and morphism universe u. These universes are retained in the intrinsic category.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt` (through the map):
  `AlgebraicGeometry.ProEtale.sfFiniteExceptionalAt`, the exact transported etale
  right adjoint at a compactification.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`:
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`, read using
  `scompile.py --source` because the recorded module is absent in both local trees;
  its formula is exact extension by zero followed by derived proper pushforward.
- `Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge`:
  `AlgebraicGeometry.ProEtale.sfConstructibleExceptionalAdjointDischarge`, the
  natural class-restricted Hom bijections, not an ambient pro-etale right adjoint.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  `WeilConjectures.finiteDerivedPullback`, `finiteIntrinsicDerivedTensor`,
  `finiteIntrinsicDerivedInternalHom`; also read its primary recorded declaration
  `commonStageDerivedInternalHom_existsUnique` and the module's coefficient domains.
- `Sheaf.Paper.PbcCoefficientTwists`:
  `AlgebraicGeometry.Scheme.pbcTateTwist` and its reexported finite interfaces;
  `Sheaf.Paper.FixedFinitePositiveCoefficientTwist` provides `.diagonalTwist`,
  the finite A(d)[2d] actually used by this map. Positive levels do not require
  divisibility by the ramification index.
- `def-weil-scheme-morphism-properties` is explicitly a collecting node with no
  notion of its own and no Lean record; its relevant finite-type, smooth and
  separated properties are the existing classes in the statement above.

The docstring carries all six recorded proof steps. Steps 1–4 prove invertibility
of the three specified factors and give the ordered inverse. Steps 5–6 retain the
node's extra vector-bundle-model normalization argument without adding that extra
clause to the theorem's conclusion. Available proof dependencies are imported,
including diagonal dualizing orientation (through the map), vector bundle purity,
vector integration, affine-space trace, twist local freeness, Noetherian facts and
fully faithful degree-zero embedding.

Proof-import exception requiring maintainer attention: importing
`Sheaf.Paper.CohomologicalSmoothnessTheorem` with the recorded map fails because
its `CohomologicalSmoothnessComparison` imports the old
`WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude`, which imports the old
`ProEtale.Derived.Comparison`. The map uses the current
`ProEtale.FiniteCoefficient.Derived.Comparison`. Lean reports that the environment
already contains `AlgebraicGeometry.ProEtale.derivedComparisonAdjunctionPlus`.
The current server source was checked with `scompile.py --source` and has the same
import. Following the launcher's duplicate-import repair instruction, this proof-only
import is omitted; the proof dependency and its full mathematical use remain recorded
in the node and docstring. No foreign module or dependency node is modified.
The five other proof-only dependencies without Lean records are not imported:
`cor-pur-vector-bundle-purity`, `def-pur-affine-space-comparison`,
`def-pur-affine-line-purity-comparison`, `cor-pur-dualizing-object-purity`,
`lem-pur-projection-purity-agreement`.

Edge cases checked before writing:

- d = 0 is included; twist and shift are zero, including identity and etale maps.
- Empty X, and empty Y (hence empty X), are allowed: no nonemptiness binder,
  stalk choice or dimension maximum appears.
- Zero K is allowed; its bounded support and finite Tor amplitude satisfy hK.
- Every positive level occurs, including n = 1 and levels not divisible by the
  ramification index; n = 0 is excluded exactly by the source.
- Ramified coefficient extensions are included; there is no unramified or
  characteristic-zero residue-ring assumption. The sole coefficient-prime
  restriction is the bundled ell ≠ p.
- Smooth need not be proper or surjective; those hypotheses are absent.
- Arbitrary nonnegative d and arbitrary scheme universe u are bound explicitly;
  no smaller independent test-object universe or equality of site universes is added.

Searches for an existing exact statement (2026-10-17 UTC):

- `msearch.py ... leanfinder`: “For a smooth separated morphism of pure relative
  dimension d, the finite coefficient smooth purity map from pullback twisted d
  shifted 2d to exceptional inverse image is an isomorphism”. Eight hits, including
  `IsSmoothOfRelativeDimension` and Proj pullback comparisons; no purity theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.Smooth, CategoryTheory.IsIso`.
  One normalization-under-smooth-base-change theorem, unrelated to purity.
- `msearch.py ... grep`: `smoothPurity|smooth_purity|finiteCoefficientSmoothPurity`.
  Zero Mathlib hits.
- `rg` with the same pattern in upstream `WeilConjectures` and side `lean/Sheaf`:
  upstream `EtaleCohomology/Purity/Smooth/Basic.lean` defines `smoothPurityIso`
  using arbitrary orientation and tensor isomorphism arguments, on the ordinary
  etale site; `nonempty_iso_rightDerivedUpperShriek_twistShift` asserts an endpoint
  isomorphism. Neither is invertibility of this specified canonical pro-etale map.
  The side has the map and a Qbar transport theorem, but no finite-level assertion.
- Upstream grep for this exact blueprint id found the same endpoint-existence
  theorem's docstring. Its full signature and the `smoothPurityIso` docstring
  were read; the tag alone does not make it an exact match.
- `rg` of `dag/lean_names_upstream.json` found no occurrence of the new theorem name.

Sources: the item's current statement and six-step proof, its dependencies' node
statements and declarations, and the current blueprint main-20261015 item file.
The current node already corrects the snapshot's ambient-adjoint wording to the
constructible bounded-class formulation. This delivery preserves that statement
and every field other than `lean`; no new dispute or correction is needed.

Validation: `scompile.py NP thm-pur-finite-coefficient-smooth-purity` compiled the
sandbox and the delivered module in separate file checks (3.3 s and 3.7 s), with
no errors or warnings after removal of the incompatible proof-only import.

## Second reading by NP

Independent reading by the maintainer reviewer (cc review service, 2026-10-18), who did not
write this delivery; it replaces the earlier placeholder, which recorded no reading (H11).
I had the node, the module and the recorded map `Sheaf/Paper/SmoothPurityMap.lean` open.

Node clauses and their Lean, with verdicts:

- Purity conventions: finite-field datum (p,a,q,k0,k), prime ell != p, E/Q_ell finite in the
  fixed closure, n >= 1, A = O_E/varpi^n. Lean: `P : PurityFiniteSetting.{u}` (fields `field`,
  `coefficients`, `extension`, `finiteExtension`, `level`, `level_pos : 1 <= level`), coefficient
  ring `P.Ring = Padic.coefficientExtensionRing ...`. Correct; the same bundle as
  def-pur-conventions and the recorded map.
- X, Y separated finite-type k-schemes. Lean: `X.Over`, `Y.Over` Spec k with
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on both structure maps. Correct.
- f a k-morphism, separated, smooth of pure relative dimension d in Z>=0. Lean:
  `f.IsOver`, `[IsSeparated f]`, `(d : ℕ) [SmoothOfRelativeDimension d f]` (Mathlib: at each
  point standard smooth of relative dimension d, implies `Smooth f`). Correct.
  `[LocallyOfFiniteType f] [QuasiCompact f]` are implied (smoothness; X quasi-compact over k and
  Y separated over k), so nothing stronger is assumed; they are also in the signature of the map.
- K in D^b_ctf(Y_proet, A). Lean: `K : Scheme.proEtaleDerivedCategory Y P.Ring` with
  `hK : finiteTorConstructible ...` (bounded constructible and finite Tor amplitude, the records of
  def-weil-finite-torsion-constructibility / def-weil-finite-tor-amplitude). Correct.
- Conclusion: the specified gamma_{f,K} : Lf^*K(d)[2d] -> Rf^!K of def-pur-smooth-purity-map is an
  isomorphism. Lean: `IsIso (P.smoothPurityMap f d K hK)`, the recorded declaration of that node
  (reassociation tau, then 1 tensor Pi_f^{-1} and theta inside `smoothPurityTensorMap`), with the
  constructible exceptional inverse image of the bounded-class adjunction. Not an existence
  statement. Correct.

Edge cases: d = 0, empty X or Y, K = 0, n = 1, ramified E all admitted; universe u bound once,
no extra universe equality. Statement field equals the file signature verbatim (checked by script).
Searches: `isIso_smoothPurityMap|smoothPurityMap` over side `lean/` finds only the recorded map
module; the node had no `lean` record before; Mathlib has no purity statement.
Docstrings carry the source place, `(blueprint: thm-pur-finite-coefficient-smooth-purity)` and the
six proof steps; the proof is `sorry` only. The omitted proof-only import
`Sheaf.Paper.CohomologicalSmoothnessTheorem` was rechecked: adding it fails with the duplicate
`derivedComparisonAdjunctionPlus` environment error, as the worker report says.
Mismatches found: none in the statement; only this section was replaced.
