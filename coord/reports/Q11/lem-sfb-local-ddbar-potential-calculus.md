## Worker report

The module `Sheaf.Geometry.Complex.LocalDdbarPotentialCalculus` states
`ComplexManifold.local_ddbar_potential_calculus` with one `sorry`, and supplies real
constructions `ddbarCoordinateWedge` and `ddbarPotential` for the objects introduced
by the item's own statement. These helper definitions belong to this notion and
are listed in `lean.declarations`, under the brief's missing-helper authorization.
No independent new notion or postponed auxiliary theorem is introduced.

Source read: Demailly, Complex Analytic and Differential Geometry, downloaded from
https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf into the
sandbox scratchpad and read through `pdftotext -layout`: I §3.C, (3.13)–(3.19),
printed pp.23–25, and VI §4, Example (4.4), printed p.297; V §13 supplies the
line-bundle curvature interpretation. The coordinate exterior product uses the
unnormalized alternating product, so there is no extra factor of two. The PDF
browser timed out; the direct author-PDF download succeeded.

Hypothesis and clause correspondence:

- The fields are Mathlib `ℝ` and `ℂ`, instances of `Field` (def-weil-field's
  `mathlib_match`; `Mathlib.Algebra.Field.Defs`, class `Field`, line 180).
- `d : ℕ` and the universally quantified `e : ℕ` allow every nonnegative dimension.
  `Model d` is the existing `Fin d → ℂ`; no manifold or metric is assumed.
- `U : Set (Model d)` and `hU : IsOpen U` give the first open domain; `V` and
  `IsOpen V` give the second open domain inside the pullback clause.
- `φ : Model d → ℝ` with `hφ : ContDiffOn ℝ ∞ φ U` is a real smooth potential.
  Ambient functions represent functions on an open domain by restriction; all
  derivatives are within the domain and every comparison is on that domain.
  Any function defined only on U has an ambient extension by assigning zero off U;
  no smoothness of that extension off U is required.
- `wirtingerPartial` and `wirtingerBarPartial` are reused without alteration from
  `Sheaf.Geometry.Manifold.KahlerCoordinateData`. Their signatures and docstrings
  were read: they are `(D_x - i D_y)/2` and `(D_x + i D_y)/2` using real
  `fderivWithin` and the existing real coordinate vectors.
- `ddbarCoordinateWedge r s` alternates the product of real-linear coordinate
  evaluation `dz_r` and conjugate coordinate evaluation `dbar_z_s`. Its type is
  `ContinuousAlternatingMap ℝ (Model d) ℂ (Fin 2)`, so these are complex-valued
  alternating multilinear functions on real tangent vectors. Continuity excludes
  no alternating tensor here because the tangent spaces are finite dimensional.
- `ddbarPotential U φ z` is the double sum of those wedges with coefficient
  `Complex.I / (2 * (Real.pi : ℂ)) * ∂z_r(∂bar_z_s φ)`. The real potential is
  coerced to complex coefficients before applying the existing operators. This
  is exactly the displayed definition; no abstract ddbar operator is assumed.
- `ContDiffOn ℝ ∞ (ddbarPotential U φ) U` states smoothness of the tensor field.
- The second conjunct quantifies over points in U and every tuple of real tangent
  vectors, asserting `star (D z v) = D z v`: fixed by conjugation, hence reality.
- The third conjunct is `extDerivWithin (ddbarPotential U φ) U z = 0` for every
  `z ∈ U`: actual exterior closedness, with Mathlib's standard alternating
  derivative (`Mathlib.Analysis.Calculus.DifferentialForm.Basic`, lines 73–91).
- The fourth conjunct exhibits coefficients `H` for a sum of `dz_r ∧ dbar_z_s`.
  This is precisely the stated type (1,1); it imposes no positivity or metric.
- The fifth conjunct quantifies over every other smooth potential ψ and every
  pair of real constants a,b, and uses `Set.EqOn` to assert
  `D(aφ+bψ)=aDφ+bDψ` on U. No complex-linearity is asserted.
- The sixth conjunct quantifies over every e,V,F, requires `Set.MapsTo F V U`,
  and requires `AnalyticOnNhd ℂ (fun z ↦ F z r) V` for each coordinate r.
  AnalyticOnNhd is locally convergent complex power series, as specified by the
  node. Pullback is literally `compContinuousLinearMap (fderivWithin ℝ F V z)`.
  `Set.EqOn` asserts equality with `ddbarPotential V (φ ∘ F)` on V; smoothness
  of the composite is also stated, as established in proof step 5.
- The final conjunct quantifies over every analytic h with `∀ z ∈ U, h z ≠ 0`.
  It states both `ContDiffOn ℝ ∞ (fun z ↦ Real.log (‖h z‖ ^ 2)) U` and equality
  of its ddbar with zero on U. This is the real logarithm of squared modulus,
  without choosing a global complex logarithm.

Dependency declarations: the recorded Field Mathlib match above, and the already
landed definition node `def-sfb-kahler-coordinate-data`, whose module supplies
`ComplexManifold.Model` (via HermitianDolbeaultData), `wirtingerPartial`, and
`wirtingerBarPartial`. The latter node is added to stmt_deps under the rule
allowing already landed nodes. Its complete statement and Lean source were read.
We do not use a Hermitian metric in the statement. Mathlib proof-dependency
modules are imported non-publicly: ContDiff.Comp/Operations, FDeriv.Symmetric,
FDeriv.Analytic/RestrictScalars, Analytic.Constructions/Composition/Linear and
SpecialFunctions.Log.Deriv. These implement the node's five recorded Mathlib
calculus leaves; no dependency is copied or restated.

Edge cases checked before writing: if U or V is empty, the corresponding EqOn,
MapsTo and pointwise assertions are vacuous, with smoothness on the empty set.
For d=0 the double sum is the zero alternating two-form and the coordinatewise
analyticity condition for a map to ℂ⁰ is correctly empty. For e=0 the real
differential has zero source tangent space and every pulled-back two-form
vanishes. Constant potentials have zero Hessian, and the nonzero constant-unit
case gives a constant real logarithm. The nowhere-zero assumption is restricted
to U, so h may vanish elsewhere. No global smoothness, connectedness, positive
dimension, nonempty-domain or logarithm-branch hypothesis was added.

Searches performed (all msearch calls used group Q11 and this item):

- LeanFinder: "For a smooth real potential its complex Hessian is a real closed
  (1,1) form natural under holomorphic pullback and vanishes on log squared modulus
  of a holomorphic unit" returned eight hits, including
  `AnalyticAt.harmonicAt_log_norm`, `Complex.kahler`, and one-dimensional
  Laplacian formulas. None states the arbitrary-dimensional Hessian-form theorem.
- Loogle: `"ddbar"` returned zero hits.
- msearch grep: `ddbar|pluriharmonic|Wirtinger|Dolbeault` in Analysis returned zero.
- LeanSearch: "Complex Hessian differential form constructed from Wirtinger
  derivatives on an open subset of complex Euclidean space" returned eight hits
  on one-dimensional derivatives, Laplacians and analyticity, no exact theorem.
- `rg` in live WeilConjectures and Sheaf for
  `ddbar|Wirtinger|Dolbeault|complexHessian|ComplexHessian` found the existing
  Wirtinger operators in KahlerCoordinateData and the general Hermitian
  Dolbeault data, but no complex-Hessian potential construction or theorem.
  A search for the item id in WeilConjectures had no hits. A full-name search
  for the three proposed declarations in Mathlib Analysis, WeilConjectures,
  Sheaf, and dag/lean_names_upstream.json had no hits.
- DAG search for ddbar/Wirtinger/complex-Hessian terminology located this item,
  the calculus leaves, the local scalar Dolbeault lemma, and the recorded
  KahlerCoordinateData node. `tools/blueprint_refs.py search 'complex Hessian'`
  returned zero blueprint-node matches. The ancestor query produced no output
  (the item's from.node is null); no new node is needed.

No statement correction or STATEMENT-DISPUTED issue was found. Each theorem proof
is exactly sorry; both helper definitions have complete data with no proof holes.
The first scompile.py check passed both the sandbox and library-module passes
(1.8 seconds each), with no errors or unexpected warnings.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
