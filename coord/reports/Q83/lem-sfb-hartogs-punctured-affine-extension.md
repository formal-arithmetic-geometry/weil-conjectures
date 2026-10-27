## Worker report

The module `Sheaf.Analysis.Complex.HartogsPuncturedAffineExtension` states
`Complex.existsUnique_entire_extension_of_punctured_affine`, with `sorry` as its
only proof. No definition, helper, new node, dependency repair, or statement
correction is needed. Only the item's `lean` field changes.

The inherited BLOCKED ending confused a stage-1 merge with completion of stage 2.
The Q19 PASS in the ledger accepts the split and its three children. The current
item has no Lean record and is queued for stage 2. This delivery preserves that
accepted split verbatim and supplies its Lean statement, as authorized by the
stage-handoff paragraph of coord/brief-stage2.md §0.

### Each hypothesis and conclusion

- Work over C: the scalar field and codomain are Mathlib's `ℂ`, with its canonical
  `Field`, norm and normed-space structures. No variable field or extra hypothesis
  is introduced.
- Integer dimension m at least two: `(m : ℕ) (hm : 2 ≤ m)`. The stated integer is
  necessarily nonnegative; natural numbers thus encode exactly the permitted
  dimensions. The space is the finite product `Fin m → ℂ` with its usual norm
  and topology, not an infinite-dimensional space.
- The input function on C^m minus the origin: `(f : (Fin m → ℂ) → ℂ)` is a total
  representative, and every input condition refers only to
  `({0}ᶜ : Set (Fin m → ℂ))`. Its value at zero is completely arbitrary and is
  neither constrained by the hypothesis nor used by the extension conclusion.
  Conversely every function on the punctured subtype has a total representative
  by assigning any complex value at zero. Since the punctured space is open,
  the local germs there are independent of this assignment. Thus this is exactly
  the punctured-domain datum, with no requirement to extend continuously at zero.
- Holomorphic means locally represented by convergent complex power series:
  `hf : AnalyticOnNhd ℂ f ({0}ᶜ : Set (Fin m → ℂ))`. Mathlib's
  `AnalyticOnNhd` unfolds to `AnalyticAt` at every point of this set;
  `AnalyticAt` asserts an actual convergent `FormalMultilinearSeries` on a ball
  of positive radius. In a finite product of complex lines its homogeneous
  multilinear terms are precisely homogeneous coordinate polynomials. This is
  the stated power-series notion, rather than an added continuity assumption.
- Existence and uniqueness: `∃! F : (Fin m → ℂ) → ℂ, ...`. The unique object is
  the actual entire function, so uniqueness is equality on all of C^m, including
  the origin.
- Entire holomorphic: `AnalyticOnNhd ℂ F Set.univ`, giving the same power-series
  notion at every point, including zero.
- Restriction equals f: `Set.EqOn F f ({0}ᶜ : Set (Fin m → ℂ))`, meaning exactly
  equality at every nonzero vector. It deliberately does not assert `F 0 = f 0`.
- No boundedness or prescribed limit: there is no boundedness, limit, continuity
  at zero, or differentiability at zero hypothesis on `f`.

### Dependencies and proof plan

The sole statement dependency `def-weil-field` has status `mathlib` and match
`Field` in `Mathlib.Algebra.Field.Defs` (definition/docstring read at lines
171–180). Mathlib's canonical complex field supplies it; it needs no new Lean
record. `Mathlib.Analysis.Complex.Basic` publicly provides the complex normed
structures, and `Mathlib.Analysis.Analytic.Basic` publicly provides
`AnalyticOnNhd`, `AnalyticAt`, `HasFPowerSeriesAt`, `HasFPowerSeriesOnBall`, whose
full signatures/docstrings were read at lines 65–119.

The proof dependencies already stated in Mathlib are imported privately:

- `lem-sfb-complex-analytic-function-operations`: `analyticAt_const`,
  `AnalyticAt.add`, `AnalyticAt.mul`, `AnalyticAt.inv`, `AnalyticAt.pi` from
  `Mathlib.Analysis.Analytic.Constructions`, together with its public imports
  giving `ContinuousLinearMap.analyticAt` from `Mathlib.Analysis.Analytic.Linear`
  and `AnalyticAt.comp` from `Mathlib.Analysis.Analytic.Composition`;
  `AnalyticAt.continuousAt` is in the already public Basic module.
- `lem-sfb-analytic-germ-differentiable`: `AnalyticAt.differentiableAt` from
  `Mathlib.Analysis.Calculus.FDeriv.Analytic` (signature read at line 126).
- `lem-sfb-cauchy-circle-formula`:
  `DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul` from
  `Mathlib.Analysis.Complex.CauchyIntegral` (docstring/signature read at 548–555).

`lem-sfb-holomorphic-circle-integral-parameters` is presently an unstated proof
prerequisite, with no `lean` record or `mathlib_match`, so there is no module to
import yet. Its statement was read. It is not needed to type this theorem and
is not introduced again here; stage 2 rule 7 assigns the later proof import to
the maintainer once it has a module. Its ID and role are retained in the proof
docstring and in the unchanged `proof_deps`.

The theorem's docstring contains all five proof steps: circle-integral local
extension, Cauchy equality on nonzero parameter slices, continuity along nonzero
parameter vectors, gluing at zero, and uniqueness by continuity along an explicit
sequence. The source was downloaded and read: Demailly, Complex Analytic and
Differential Geometry, I §3.D, (3.28), printed p.28, with the following proof.
Its specialization is Ω=C^m and K={0}; the punctured space is connected for the
stated dimensions. Source URL:
https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf .
The accepted split uses the more explicit Cauchy-integral proof, which remains
unchanged.

### Edge cases

The minimal m=2 has one nonzero parameter direction, so the proof's sequence
argument works. m=1 is excluded as required: 1/z gives a counterexample there.
m=0 is excluded too. Zero functions, constants, and arbitrary polynomials are
included. Altering a polynomial's total representative only at zero preserves
`hf` and preserves the uniquely determined extension; this checks that the
statement imposes no compatibility with an arbitrary assigned `f 0`. The entire
function need not be bounded (a coordinate function is included). Only the
origin is removed, not any coordinate hyperplane. There is no universe parameter
or hidden auto-implicit; `autoImplicit` is disabled.

### Searches actually run

- `msearch.py leanfinder`: “Every holomorphic function on punctured complex affine
  space of dimension at least two extends uniquely holomorphically across the
  origin”. Eight hits: one-variable removable-singularity declarations and
  meromorphic-normal-form declarations. In particular
  `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` requires
  continuity at zero and has one-dimensional source. No exact statement found.
- `msearch.py loogle`: `"Hartogs"`. OK, zero hits.
- `msearch.py leansearch`: “Hartogs extension theorem for holomorphic functions
  on punctured complex affine space in dimension at least two”. Eight hits,
  chiefly the same one-variable removable-singularity results, plus local
  analytic-neighborhood lemmas. No several-variable Hartogs extension.
- `msearch.py grep`: `Hartogs|punctured.*analytic|isolated.*singular` in
  `Mathlib/Analysis`. OK, zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `hartogs|Hartogs|punctured.*(holomorphic|analytic)` found algebraic depth-two
  Hartogs results, not this complex-analytic statement. A separate search for
  the exact item ID in both trees and repair notes found no declaration or
  released repair. The selected theorem name contains no existing match.

### Validation

Compiled through the prescribed `scompile.py` against the published live
library, both as the sandbox module and under the delivery module name. Both
passed, with no errors or warnings. The theorem is left `sorry` as stage 2
requires. No `STATEMENT-DISPUTED` issue was found.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
