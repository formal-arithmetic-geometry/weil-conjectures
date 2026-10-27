## Worker report

The module `Sheaf.Analysis.CompactSubmersionPhaseEstimate` states
`EuclideanSpace.compactSubmersion_phase_estimate`, with its proof postponed by `sorry`.
The concrete helper `EuclideanSpace.compactSupportDerivativeSeminorm` expands this
node's own p_N notation; it contains no postponed data or proof. The existing coordinate derivative is now owned by the definition node
`def-sfb-euclidean-multi-index-partial-derivative`, with no change to its data.

Clause-by-clause reading:

- The specified real and complex fields are Mathlib `ℝ` and `ℂ`, instances of the
  dependency's `Field` (`Mathlib.Algebra.Field.Defs`). The spaces are
  `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin k)`, with their Euclidean
  norms, real inner products and canonical Lebesgue `volume`. These are finite
  coordinate spaces, not the sup-normed function-space encoding.
- `hn : 1 ≤ n` and `hk : 1 ≤ k` render both positive dimension assumptions.
- `U C : Set ...`, `hU : IsOpen U`, `hC : IsCompact C`, and `hCU : C ⊆ U`
  render the open domain, compact support set and containment separately.
- `H : ... → ...` and `hH : ContDiffOn ℝ ∞ H U` render the smooth phase map
  on U. An ambient function represents any arbitrary extension from U. No
  smoothness or other constraint is imposed outside U. On an open U, its ambient
  derivative at each point of U is exactly the derivative of the function on U.
- `hsub : ∀ z ∈ U, Function.Surjective (fderiv ℝ H z)` is precisely pointwise
  surjectivity of DH on U, with no constant-rank, global-surjectivity, uniform
  lower-bound or properness hypothesis added.
- `∀ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ...` renders every nonnegative integer N and
  a finite nonnegative constant A_N. Real-valuedness supplies finiteness. A is
  chosen after U,C,H,N and before u and η, so depends only on the specified data.
- The amplitude is quantified as `∀ u : ... → ℂ, ContDiffOn ℝ ∞ u U →
  (∀ z ∈ U, z ∉ C → u z = 0) → ...`. This is precisely smoothness on U
  and vanishing off C within U, with no restrictions on the ambient extension.
- `compactSupportDerivativeSeminorm U N u` is the real `sSup` of all
  `‖multiIndexPartialDeriv α u z‖` for `∑ j, α j ≤ N` and `z ∈ U`.
  The imported existing helper differentiates in coordinate order, repeating
  coordinate j exactly α j times. Thus it is the usual mixed derivative on smooth
  functions. For finitely many admissible multi-indices the supremum over this
  union equals the node's maximum of suprema. Compact support inside the open
  set ensures boundedness of every derivative, so the conditional real supremum
  has its intended meaning. No bound or finiteness assumption is imposed on u.
- `∀ η : EuclideanSpace ℝ (Fin k)` allows every frequency. The complex norm
  of the set integral on U is the specified absolute value. The integrand is
  `Complex.exp (Complex.I * (inner ℝ (H z) η : ℂ)) * u z`, with exactly the
  positive i phase and no Fourier normalization factor. The set integral uses
  Lebesgue measure, and `(1 + ‖η‖) ^ (-(N : ℤ))` is exactly the inverse
  Nth power. The right-hand multiplication is A_N times this factor times p_N(u).

Dependency declarations:

- `Field` in `Mathlib.Algebra.Field.Defs`: read its complete signature and
  accompanying field/division-ring documentation; no new field structure is defined.
- `EuclideanSpace.multiIndexPartialDeriv` in
  `Sheaf.Analysis.MultiIndexPartialDeriv`: the existing signature and coordinate-fold
  construction were extracted unchanged from the Fourier theorem module. The item
  cites its definition node `def-sfb-euclidean-multi-index-partial-derivative`;
  it neither imports nor cites the Fourier theorem as a statement dependency.
- Proof dependencies are imported non-publicly: the recorded
  `CoordinateDifferentialOperator.weightedAdjoint_spec` module, and the Mathlib
  modules supplying `IsCompact.exists_bound_of_continuousOn`,
  `isCompact_sphere` and finite-dimensional properness,
  `ContinuousOn.integrableOn_compact`, `MeasureTheory.Integrable.mono'`,
  `MeasureTheory.norm_integral_le_of_norm_le`,
  `MeasureTheory.norm_setIntegral_le_of_norm_le_const`, and `ContDiffOn.inv`.
  The six-step natural-language proof is recorded in the theorem docstring,
  including the coefficient recursion, uniform compact-sphere bound and the
  separate small-frequency estimate.

Edge cases checked before writing:

- C empty: u is identically zero on U, as are its local derivatives. If U is
  nonempty the supremum's set is {0}; if U is empty it is empty, and the real
  supremum is zero. Thus p_N(u)=0 exactly as required. A_N=0 works.
- U empty: C is empty by containment, smoothness and derivative surjectivity
  are vacuous, and the integral and seminorm are zero. No Nonempty U is imposed.
- N=0: the zero multi-index is included, its derivative is u, and the decay
  factor is one; this is the elementary volume-times-supremum estimate.
- η=0: the phase equals one and the decay factor is one. There is no division
  by frequency in the statement.
- Zero amplitude and zero-volume compact sets: the integral is zero and the
  asserted inequality remains valid. No positive-volume assumption appears.
- k>n and U nonempty: the surjective-derivative hypothesis is impossible;
  empty U is nevertheless included without an artificial dimension inequality.
- Arbitrary behavior outside U affects neither derivatives at points of open U,
  nor the seminorm, support hypothesis or restricted integral.

Searches made:

- `msearch.py leanfinder`, query "Uniform compact support oscillatory integral
  decay for a smooth submersion phase with amplitude derivative seminorm": eight
  Fourier-decay/Riemann-Lebesgue/Schwartz hits. Their phases are linear or their
  conclusions only give convergence; none states this nonlinear submersion bound.
- `msearch.py loogle`, query `iteratedFDeriv, lineDeriv`: zero hits.
- `msearch.py grep`, query `nonstationary|submersion.phase|oscillatory` in
  Mathlib Analysis: zero hits.
- `msearch.py leansearch`, query "Smooth compactly supported function coordinate
  derivative supremum seminorm": eight related hits, including
  `ContDiffMapSupportedIn.seminorm` and its bounds. Read that definition: it is
  a norm of the full multilinear iterated derivative at a fixed order, not the
  maximum of the absolute values of coordinate derivatives through order N.
  Substituting that norm would change the specified p_N. The helper here expands
  the exact p_N rather than introducing an alternative seminorm on bundled tests.
- `rg` of Mathlib Calculus for iterated/partial derivative APIs and of Mathlib
  Analysis for derivative seminorms; `rg` of `lean/Sheaf` and
  `lean/WeilConjectures` for multi-index derivatives, partial derivatives,
  submersion/nonstationary/oscillatory bounds and the item id. Found and reused
  `EuclideanSpace.multiIndexPartialDeriv`; found no existing declaration of the
  requested theorem or the exact coordinate-maximum seminorm. The upstream tree
  has no separate `Analysis` subdirectory; searches were completed over its root.
- `rg` of both project roots for the two proposed declaration names: no matches.

Source reading: opened the supplemental Demailly notes at
https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf.
Their coordinate differential operators and formal adjoints support the proof
plan; as the node explicitly says, the nonlinear uniform estimate is an
agent-written extension, not a theorem attributed to that text.

There is no statement correction or disputed assertion. The ownership repair below
addresses the maintainer return.
The module compiled cleanly with `scompile.py`, in both sandbox and library modes,
with no non-sorry warning. The first compile exposed an incorrect exponential
module path; replacing it by `Mathlib.Analysis.Complex.Exponential` fixed that import.

## Repair of returned delivery 07fdadb874c0

H2/H13 is repaired by extracting the existing `EuclideanSpace.multiIndexPartialDeriv`
into `Sheaf.Analysis.MultiIndexPartialDeriv`, owned by the new definition node
`def-sfb-euclidean-multi-index-partial-derivative`. The derivative signature and
body are unchanged. The Fourier theorem module removes the old definition and
publicly imports the new module, so all existing clients keep the same name.
The item replaces the theorem import by the definition import and replaces the
incorrect theorem statement dependency by the definition node. No artificial
proof dependency on the unrelated Fourier theorem is introduced.

The item's current base has only `def-weil-field` in stmt_deps; the erroneous
additional dependency was only in the returned delivery. The item is regenerated
from that current node, retaining its current unrelated metadata. The delivery
wrapper rebases the packet on current main. The existing Fourier module and node
were compared with the current server source obtained using scompile --source.

## New nodes

`def-sfb-euclidean-multi-index-partial-derivative` owns the concrete coordinate
multi-index derivative in `Sheaf.Analysis.MultiIndexPartialDeriv`. It is a move
of the existing construction, not a second derivative definition. Its statement
specifies arbitrary functions, the total Mathlib fderiv convention, the right-fold
coordinate order and zero-order/zero-dimension cases. Its only dependency is
`def-weil-field`. Source: Demailly's coordinate convention in section 1 (1.1), p.1,
and the pre-existing derivative construction. LeanSearch, LeanFinder, Mathlib
grep, both project trees, DAG definition nodes and blueprint references were
searched; their raw results are in the node's mathlib_searches. No existing
standalone definition node was found.

## Dependency modules

`lem-sfb-l2-weak-derivative-fourier-identity`: its module previously owned both a
plain derivative definition and its independent Fourier theorem. As explicitly
requested by the return, it now imports/re-exports the derivative definition
module and retains exactly its theorem signature, docstring and sorry proof.
The node's lean.declarations removes the moved helper; its lean.note describes
the extraction. This is an authorized ownership refactor of the former owner,
not a mathematical premise of the estimate. It is deliberately not added to
the item's statement or proof dependencies merely to pass a delivery gate.

## Second reading by Q78

Author's renewed reading after the return (not an independent worker review):
compared each hypothesis and conclusion with the maintainer's accepted clause
list; the theorem signature is byte-for-byte unchanged. Compared the moved
multiIndexPartialDeriv signature and right-fold body with the current original;
both are byte-for-byte unchanged. The only semantic-graph change for the item
is that its imported coordinate derivative is attributed to a definition node,
not to the independent Fourier theorem. Checked the extracted module contains
only that concrete definition, and the old module imports it publicly and has
no remaining declaration of the same name. Checked empty coordinate lists and
the zero multi-index return f, so no edge case changes. No separate worker was
started, as this dispatch prohibits subagents; independent review remains with
the maintainer. This records the actual renewed checks rather than asserting
an independent reading that did not occur.

Compile repair: added the explicit Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import to supply the Euclidean volume instance previously imported transitively.

All three repaired files compiled cleanly with scompile.py in sandbox and library modes.
The final dry run passes preflight and compilation. The maintenance ownership extraction
has now landed on current main: the definition node owns MultiIndexPartialDeriv, and the
Fourier theorem node records that definition as its statement dependency. The current
server source was read again using scompile.py --source for both modules: the definition
has the unchanged concrete body, and the Fourier module publicly imports/re-exports it.
The sandbox copies of these already landed nodes were refreshed from current main,
retaining their review metadata and the Fourier node's corrected statement dependency.
Thus this delivery now changes only the estimate module, its node, and this report.
The previous missing-owner gate failure is resolved by the maintenance landing; no
artificial theorem dependency or tool workaround was introduced.
