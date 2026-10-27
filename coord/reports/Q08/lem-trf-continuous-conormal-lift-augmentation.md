## Worker report

The module `Sheaf.TraceFormula.ContinuousConormalLiftAugmentation` states
`Algebra.ContinuousConormal.continuous_conormal_lift_augmentation`, with its entire
proof `sorry`. Nothing is proved. All other declarations are transparent helper
records bundling this node's quantified objects or its displayed equations, and
two abbreviations calling Mathlib's actual `Extension.ofSurjective`. They are
listed in `lean.declarations`. No data definition depends on a postponed theorem.
The node is unchanged outside `lean`; no statement correction or new node is needed.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
| --- | --- |
| Field k | `{k : Type u} [Field k]` |
| Finite-type k-algebra S | `{S : Type v} [CommRing S] [Algebra k S]` and `hS : (algebraMap k S).FiniteType` |
| Maximal ideal m with residue k | `(m : Ideal S) [m.IsMaximal]`, `hm : Nonempty (m.ResidueField ≃ₐ[k] k)`; an algebra equivalence fixes the structural k-action |
| A = S_m | The theorem uses the actual `Localization.AtPrime m`, not an independently given local algebra |
| R = completion of A | `Algebra.LocalCompletion (Localization.AtPrime m)` is the existing abbreviation for `AdicCompletion (IsLocalRing.maximalIdeal A) A` |
| Completed module M_R | The existing `Algebra.CompletedDifferentials k A = LocalCompletion A ⊗[A] KaehlerDifferential k A`; tensor symmetry accounts for the source's reversed factors |
| Specified continuous universal differential extension | `D` is a k-derivation on that actual completion and `hD : Algebra.IsCompletedDifferentialExtension k A D`, using the recorded predicate unchanged |
| P = localized polynomial ring at a rational maximal ideal | `PolynomialPresentation` records `m`, `q`, `maximal`, and `rational : Nonempty ((MvPolynomial (Fin m) k ⧸ q) ≃ₐ[k] k)` |
| A = P/I | `PolynomialPresentation.map` and `surjective` retain the actual quotient map; `extension.ker` is its actual kernel I; no additional local-map assumption is required for this quotient |
| Arbitrary formal presentation pi with kernel J | `FormalPresentation k R a` records `n`, a k-algebra `map`, `surjective`, `local_map`, and continuity; `extension.ker` is the actual J |
| Continuity of pi | `continuous` is the neighbourhood-of-zero criterion: each a-power contains the image of some variable-ideal power. In the theorem `a = m_A R`, matching the recorded completion-extension predicate |

Clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| C_P degree -1 is I/I², degree 0 is A tensor Omega_P/k | `P.extension.Cotangent` and `P.extension.CotangentSpace`, from Mathlib `Extension.Cotangent` and `Extension.CotangentSpace` |
| Algebraic differential, including extension to R | `P.extension.cotangentComplex`, and `LinearMap.baseChange (LocalCompletion A)` of it |
| C_T degree -1 is J/J² and degree 0 is R^n | `T.extension.Cotangent` and `(Fin T.n → R)` |
| Formal differential is reduction of termwise partial derivatives | `FormalData.differential_class` for every `h : T.extension.ker`, using exactly `MvPowerSeries.pderiv k i h.val` |
| A local polynomial lift exists | `System.lifts`, giving `Nonempty (Lift P T)` for every P and T; `Lift.commutes` is pi alpha = completion-map composed with P's quotient, and `Lift.local_map` is locality |
| Every lift induces the indicated map on ideal classes | `System.liftMap` quantifies every `α : Lift P T`; `LiftMap.neg_class` is precisely `[h] tensor 1 ↦ [alpha(h)]`, with a target kernel element carrying the actual representative |
| Every lift induces the indicated map on polynomial differentials | `LiftMap.pos_d` specifies `d x ↦ gradient(alpha x) mod J` for every x, in particular for each localized polynomial coordinate. Universal differentials and their scalar multiples generate, so this specifies precisely the map in the node |
| The maps are chain maps | `LiftMap.chain` is the exact equality `f0 (d_P tensor R) = d_T fminus`; `FormalMap.chain` is the corresponding equality for formal presentation maps |
| Continuous chain rule for every h | `System.chain_rule` quantifies each T and every `h : MvPowerSeries (Fin T.n) k`, with the exact sum over all coordinates |
| Polynomial augmentation | `PolynomialData.augmentation_d` sends `1 tensor (1 tensor d x)` to `1 tensor d(P.map x)`; `augmentation_differential` says it annihilates the conormal differential |
| Formal augmentation | `FormalData.augmentation_basis` sends `Pi.single i 1` to `D (T.map (MvPowerSeries.X i))`; `augmentation_differential` says it annihilates the formal conormal differential |
| q_T f_alpha = q_P | `LiftMap.augmentation` is equality of the actual R-linear composites, for every lift |
| Arbitrary second formal presentation and continuous local beta over R | `System.formalMap` quantifies T, U and every `FormalHom T U`; this records its map, quotient square `commutes`, locality, and variable-adic continuity |
| beta-induced map on ideal classes | `FormalMap.neg_class`, for every actual kernel element, fixes the representative beta(g) |
| beta-induced coordinate map | `FormalMap.pos_basis` is exactly `e_i ↦ (pi'(partial_j beta(z_i)))_j` |
| q_T' h_beta = q_T | `FormalMap.augmentation`, equality on the entire degree-zero module |
| Formal identities | `System.formal_identity` gives identities in both degrees whenever the presentation map is the identity |
| Formal composition | `System.formal_composition` gives component equality for every composable pair and the map with their composite underlying algebra homomorphism |
| Formal change after polynomial lift | `System.lift_formal_composition` gives `h_beta f_alpha = f_(beta alpha)` in both degrees |
| Algebraic local presentation changes | `PolynomialHom` uses Mathlib's actual `Extension.Hom` over the identities of k and A, plus locality, retaining the quotient square |
| Algebraic chain maps and original augmentations | `System.algebraic_chain` and `algebraic_augmentation` use exactly `Extension.Cotangent.map`, `Extension.CotangentSpace.map`, `cotangentComplex` and `toKaehler` |
| Algebraic augmentations after scalar extension | `System.algebraic_completed_augmentation` is the equality after `LinearMap.baseChange R` |
| Algebraic identities/composition and polynomial change followed by a lift | `System.algebraic_identity`, `algebraic_composition`, and `lift_algebraic_composition` |

A two-term chain map in degrees -1 and 0 is exactly the pair of degree maps
satisfying the displayed square. The records `LiftMap` and `FormalMap` use this
component description, not a cohomology-only comparison. Every other degree map
to or from a zero term is uniquely zero. Likewise the augmentation is exactly a
map to M_R[0]: its negative component is zero, and its chain equation is the
recorded augmentation-differential equation. Thus no choice of an unrelated
complex or map is introduced. `Nonempty (System ...)` asserts existence of all
these uniquely characterized maps; it is the conclusion, not an assumed system.
The simultaneous form is equivalent to the node's universal assertions because
the class/differential/basis formulas determine each linear map uniquely.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (and its underlying `Algebra.FiniteType`).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`; `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, `IsAdicComplete`; the existing `Algebra.LocalCompletion` from `Sheaf.RingTheory.FormalLocalPresentation`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`, and its universal property `KaehlerDifferential.linearMapEquivDerivation`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct`, pure tensors and `LinearMap.baseChange`.
- `Sheaf.RingTheory.CompletionKaehlerDifferentialComparison`: exactly the recorded `Algebra.IsCompletedDifferentialExtension`, as well as the proof dependency `Algebra.completion_kahler_differential_comparison`; its public dependency `Sheaf.RingTheory.CompletedJacobianPresentation` provides `Algebra.CompletedDifferentials`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`; `Mathlib.RingTheory.MvPowerSeries.Derivative`: `MvPowerSeries.pderiv` as a derivation with the coefficient formula and coordinate values read.
- `Mathlib.RingTheory.Extension.Cotangent.Basic`: the existing `Extension.ofSurjective`, `Extension.Cotangent`, `Extension.Cotangent.mk`, `Extension.CotangentSpace`, `Extension.cotangentComplex`, `Extension.Hom`, its k-algebra map, the two induced maps, and `Extension.toKaehler`. Their full definitions and representative formulas were read. No conormal module or Kähler module is redefined.

Proof-only imports are `Sheaf.RingTheory.FormalRelativeDerivationExpansion`
(`MvPowerSeries.formal_relative_derivation_expansion`),
`Mathlib.RingTheory.Etale.Kaehler`
(`KaehlerDifferential.isLocalizedModule_map`), and
`Mathlib.RingTheory.Kaehler.Polynomial`
(`KaehlerDifferential.mvPolynomialBasis`). The power-series local-ring interface
is `Mathlib.RingTheory.MvPowerSeries.Inverse`; its public import also supplies the
local ring structure required to state locality. The finite-level gradient-control
proof dependency currently has neither a Lean record nor an upstream audit
record; there is no importable recorded module for that proof-only dependency.
It is not a missing notion in this statement. The completion-comparison module
is public because the theorem uses its extension predicate.

The pre-existing records in
`Sheaf.TraceFormula.CompletedConormalDeterminantComparison` were examined.
Its algebraic and formal presentations impose regular equations and prescribed
codimension, hence cannot express this assertion without changing its scope.
The helpers here simply bundle this node's own input objects and component
formulas. The downstream determinant-comparison module is not imported, avoiding
a dependency cycle. No helper assumes that conormal modules are free.

Edge cases checked before finalizing: zero polynomial variables; zero formal
variables (empty gradient sum and zero coordinate module); unequal source and
target numbers of variables; I = 0; J = 0; arbitrary redundant relations;
nonreduced and singular A; arbitrary characteristic including positive
characteristic. No dummy-variable bound, reducedness, smoothness, regular sequence,
finite free conormal hypothesis, or division by integers appears. The zero ring
case is already excluded by the stated maximal ideal, not by an added hypothesis.
The coefficient universe u and finite-type algebra universe v remain independent;
the actual tensor products infer their maximum universes. The auxiliary module
universe w in `FormalData` and `FormalMap` is explicit. There are no auto-bound
variables.

Searches actually run with the authorized msearch wrapper (logs in searches.jsonl):

- LeanFinder: `Continuous local presentation lifts induce conormal chain maps compatible with completed Kahler differential augmentations`: 8 hits, including `Algebra.Presentation.differentials.comm₂₃`, `CommRingCat.KaehlerDifferential.map_d` and ordinary universal-derivation lemmas. None is the continuous assertion with the formal conormal maps and functorial augmentations.
- Loogle: `MvPowerSeries.pderiv, Ideal.Cotangent`: successful query, zero hits.
- Mathlib grep: `conormal|Cotangent.*map|chain_rule` in `RingTheory/`: 25 hits, concerning algebraic cotangent maps, Jacobi--Zariski, and ordinary differentials. Their existing conormal APIs are used instead of copied.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for conormal/continuous conormal/lift names and the item id: no exact statement. The formal-continuous-conormal sequence is a right-exactness result for quotients, and the completed-conormal determinant system has the additional regularity hypotheses just noted.

No STATEMENT-DISPUTED issue or source correction was found. The source places
were read in the local Stacks text: the rational coefficient presentation in
varieties.tex (0C52) and the coordinate-change chain-rule paragraph in curves.tex
(0C4B). The node itself supplies the detailed agent-formulated assembly, faithfully
included step by step in the theorem docstring.

Validation: `scompile.py Q08 lem-trf-continuous-conormal-lift-augmentation <module>`
passed both its sandbox and named-library checks (32.7 s and 26.3 s respectively),
with no errors or non-sorry warnings. The final dry run and delivery use deliver2.py.

## Second reading by Q08

A second pass reopened the node and the complete final module, independently of
the initial drafting pass. The dispatcher forbids starting another agent; this
section records Q08's own second reading, and the maintainer supplies the
independent delivery review.

I checked the full correspondence table above against the actual fields, rather
than judging only the main theorem's short signature. In particular, `System` is
the conclusion, not a hypothesis; its universal binders include EVERY lift and
EVERY presentation change. The `neg_class` fields specify actual representatives
in kernel cotangents, `pos_d` and `pos_basis` specify the prescribed gradients,
and the `chain` and `augmentation` fields compare entire linear maps. The scalar
extension is of the actual algebraic differential and not the kernel of P to R.
No relation generators or regularity have slipped into the presentation records.
The polynomial quotient has only surjectivity; its automatic local quotient
property is not added as an extra field.
Both sorts of composition and both mixed compositions were checked, including
zero-variable cases. The auxiliary records do not assume the theorem conclusions
in the hypotheses of the theorem: they are all under `Nonempty (System ...)`.

Drafting issues repaired before this pass: the preliminary formal chain square
used the ordinary algebraic differential of the power-series ring, whose target
is not R^n; the final `FormalData.differential_class` instead uses the termwise
formal partial derivatives required by the node. The final version also makes
all augmentation maps conclusion data, supplies every formal and algebraic
functoriality clause, and uses the recorded completion-extension predicate
through a public import. The module compiles cleanly with these repairs. The
node's natural-language statement and dependencies have not changed.
