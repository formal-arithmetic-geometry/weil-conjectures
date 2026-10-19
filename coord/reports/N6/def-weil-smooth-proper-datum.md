## Worker report

The module `Sheaf.Paper.SmoothProperDatum` defines
`WeilConjectures.SmoothProperDatum`, parameterized by the global finite-field datum
`D : FiniteFieldDatum`.  Its `X₀` field is an object of
`Over (Spec (CommRingCat.of D.k₀))`; the instance field `isProper` gives
`IsProper X₀.hom`; `d : ℕ` renders the source's integer `d ≥ 0`; and
`smoothOfPureDimension` is exactly
`D.IsSmoothOfPureDimension X₀ d`.  The instance field
`geometricallyConnected` gives `GeometricallyConnected X₀.hom`.  The properness
instance supplies the locally-finite-type and quasi-compact hypotheses required by
`IsSmoothOfPureDimension` and by the canonical geometric-fibre construction.

The module also defines `WeilConjectures.SmoothProperDatum.X`.  It is the canonical
`D.geometricFiber 𝓧.X₀` (the `Over` pullback along `Spec k → Spec k₀`), so the `X` in
`(X₀,d,X)` is determined by `X₀` and `D`, rather than an independently chosen scheme.
This renders the source's geometric-fibre/base-change clause and its convention that
the resulting datum is a function of `X₀` and `d`.

The statement clauses and their Lean rendering are:

* The fixed global finite-field datum is the explicit parameter `D` and its fields
  `D.p`, `D.a`, `D.q`, `D.k₀`, and `D.k`; the inherited `FiniteFieldDatum` declaration
  supplies `q = p^a`, the finite field, and fixed algebraic closure.
* A `k₀`-scheme is `X₀ : Over (Spec (CommRingCat.of D.k₀))`.
* Properness is the instance field `[isProper : IsProper X₀.hom]`; this is the
  Mathlib predicate containing separatedness, universal closedness and locally finite
  type, and it yields the finite-type/quasi-compact assumptions used by the source.
* Smoothness and pure dimension are the field
  `smoothOfPureDimension : D.IsSmoothOfPureDimension X₀ d`, whose definition is
  `Smooth X₀.hom ∧ (D.geometricFiber X₀).left.IsPureDimension d`.
* The nonnegative integer is represented by `d : ℕ`.
* Geometric connectedness is the instance field
  `[geometricallyConnected : GeometricallyConnected X₀.hom]`; the Mathlib class includes
  the nonemptiness/connectedness condition on every field extension.
* The geometric fibre is rendered by
  `noncomputable def SmoothProperDatum.X ... := D.geometricFiber 𝓧.X₀`, the existing
  canonical base-change/pullback construction over `Spec D.k`.

The dependency declarations used are:

* `WeilConjectures.FiniteFieldDatum` and
  `WeilConjectures.FiniteFieldDatum.geometricFiber` from
  `Sheaf.Paper.FiniteFieldFiber` (node `def-weil-finite-field-fiber`).
* `AlgebraicGeometry.Scheme.Over` from Mathlib's
  `Mathlib.AlgebraicGeometry.Over` (node `def-weil-scheme-over-base`).
* `WeilConjectures.FiniteFieldDatum.IsSmoothOfPureDimension` from
  `Sheaf.Paper.GeometricHypotheses` (node `def-weil-geometric-hypotheses`).
* The base-change notion is supplied by the recorded
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChange` bundle and its
  `baseChange_morphism_projections`, `baseChange_iterated`, `baseChange_fiber`, and
  `Scheme.Hom.geometricFiberAt` declarations in
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` (node
  `def-pc-base-change`); the actual geometric fibre used here is the more specific
  `FiniteFieldDatum.geometricFiber` above.
* `AlgebraicGeometry.IsProper` and
  `AlgebraicGeometry.GeometricallyConnected` are Mathlib predicates imported by
  `Sheaf.Paper.GeometricHypotheses`.

Edge cases checked: `d = 0` is admitted by `ℕ`; no positive-dimension assumption is
introduced.  Empty schemes are excluded exactly by geometric connectedness, while the
pure-dimension predicate itself imposes no extra nonemptiness condition.  The geometric
fibre is fixed canonically and cannot be replaced by an arbitrary scheme.  The finite
field characteristic and the possibility of any allowed prime `p`, exponent `a ≥ 1`,
and algebraic closure are inherited from `D`; no characteristic or universe restriction
was added.  Properness is used through its existing class, so its finite-type clause is
not duplicated as an extra hypothesis.

Searches made: `msearch.py N6 def-weil-smooth-proper-datum leanfinder "smooth proper datum structure finite field scheme geometric fiber"` returned only unrelated Mathlib morphism declarations; `msearch.py ... loogle "SmoothProperDatum, IsSmoothOfPureDimension, GeometricallyConnected, IsProper"` returned no match; and `msearch.py ... grep "SmoothProperDatum|smooth.?proper.?datum" Mathlib/AlgebraicGeometry` returned no match.  `rg` over `WeilConjectures/` and `lean/Sheaf` found no bundled smooth-proper datum (only the component predicates and existing geometric-fibre uses).  The node's recorded Mathlib grep searches were also checked: Mathlib has the four component predicates but no bundled datum or named geometric-fibre construction matching this notion.

No statement correction or `STATEMENT-DISPUTED` flag is needed.  The file compiles cleanly with `scompile.py`; the only postponed material is none, since this node is a definition and all its data is explicit.

## Second reading by N6

Independent maintainer second reading, 2026-10-17, of immutable delivery
`6d85595a08bc4f7094b600d9d0d89361695e8028`. This reading was performed by the
maintainer reviewer, not by a second N6 worker. It replaces the delivered placeholder.

Read the item node and all four statement-dependency nodes in the immutable snapshot,
the delivered module and report, and the exact dependency declarations in the read-only
sources. Read the source definition in
`literature/blueprint/slopmaster2/src/version/sketch/01_final_weil_conjectures.tex`,
lines 2866–2875 (`def:smooth-proper-datum`), and its convention at lines 2910–2911.
Also read the master geometric-hypotheses definition, order 412.

Clause-by-clause reading:

* Fixed `(p,a,q,k₀,k)`: the explicit parameter `D : FiniteFieldDatum.{u}` reuses
  `Sheaf.Paper.FiniteFieldFiber`. Its fields specify prime `p`, `1 ≤ a`, `q = p^a`,
  the cardinality of `k₀`, and a fixed algebraic closure with its algebra structure.
  There is no additional choice of coefficient prime or field. Matches.
* A `k₀`-scheme: `X₀ : Over (Spec (CommRingCat.of D.k₀))` bundles the scheme and
  structure morphism. Mathlib's `CategoryTheory.Over` is the bundled version of the
  recorded `Scheme.Over` convention, not a private replacement. Matches.
* Properness: `[isProper : IsProper X₀.hom]` uses Mathlib's separated, universally
  closed, locally-finite-type predicate. Universal closedness supplies quasi-compactness;
  together these supply exactly the finite-type requirements of the dependencies.
  They impose no extra assumption beyond properness. Matches.
* Nonnegative dimension: `d : ℕ` represents precisely the source's integer `d ≥ 0`.
  Matches, including zero.
* Smoothness and pure dimension:
  `smoothOfPureDimension : D.IsSmoothOfPureDimension X₀ d` reuses the recorded
  declaration in `Sheaf.Paper.GeometricHypotheses`. Its body is
  `Smooth X₀.hom ∧ (D.geometricFiber X₀).left.IsPureDimension d`.
  `Scheme.IsPureDimension` quantifies over every irreducible component and requires
  its subspace topological Krull dimension to equal `(d : WithBot ℕ∞)`. It does not
  merely constrain the largest component or silently assume integrality. Matches.
* Geometric connectedness: the field
  `[geometricallyConnected : GeometricallyConnected X₀.hom]` uses Mathlib's test
  on all field-valued base changes. `ConnectedSpace` includes nonemptiness.
  This is the dependency's geometric connectedness, without replacing it by a
  geometrically integral hypothesis. Matches.
* Geometric fibre: `SmoothProperDatum.X` is the real construction
  `D.geometricFiber 𝓧.X₀`, with a local properness instance. The dependency expands
  to `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj 𝓧.X₀`.
  Its underlying scheme is the categorical pullback, with structure map the second
  projection. This is exactly the base change in `def-pc-base-change`; the latter's
  primary module-sheaf declaration is not mistaken for scheme base change.
  The dependency module `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
  was read using `scompile.py --source` because it is absent from the local clones.
  Matches; `X` is determined, not arbitrary extra data.
* The resulting datum for given `X₀,d` has this same canonical fibre. Remaining
  fields are proofs of properties and are proof-irrelevant. The convention that
  future invariants depend on the datum introduces no additional invariant to define
  in this node; the record and its fibre projection provide the required argument.
  Matches.

Edge cases: `d = 0` is allowed; the empty scheme is excluded by geometric
connectedness, as in the source, even though pure dimension alone is vacuous there.
Infinite-dimensional components cannot satisfy a finite `d`. No characteristic or
positive-dimensional restriction was added. The only universe `u` is bound explicitly;
the scheme and fields use the inherited dependency universe, with no new universe
equality or restriction introduced by this module.

Independent `rg` searches for `SmoothProperDatum`, smooth-proper datum, and bundled
smooth/proper structures in Mathlib algebraic geometry, upstream `WeilConjectures`,
project `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing matching
bundle. The worker's LeanFinder, Loogle and grep search records were read. Component
predicates and the geometric-fibre construction are reused. No missing helper,
new node, dependency repair, or source-based statement correction is necessary.

The node's `lean.statement` is verbatim
`structure SmoothProperDatum (D : FiniteFieldDatum.{u})`, matching the signature
before `where`. Both listed declarations exist. Module and declaration docstrings
name the source and blueprint id. All lines meet the 100-character limit. The only
import is used. There is no hollow data, theorem, local proof, axiom, or `sorry` in
this delivered module, and no pro-etale substitute.

Compiler reproduction: ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N6 def-weil-smooth-proper-datum snapshot/lean/Sheaf/Paper/SmoothProperDatum.lean`
from the immutable review directory. Exit code 0; sandbox
`Sheaf/Stage2/Sandbox0.lean` passed in 1.8 s and library-path
`Sheaf/Paper/SmoothProperDatum.lean` passed in 1.9 s, with no diagnostics.
The installed wrapper currently runs the server side overlay, despite the older
brief describing a local-first implementation. No direct SSH, global build, live
Lean write, repository edit, delivery, or Git mutation was performed by the reviewer.
The worker had recorded a clean `scompile.py` result without a detailed log; this
independent reproduction supplies the concrete per-file evidence.

Findings and corrections: H11 (second reading not a reading): the delivered section
explicitly said that no second reading occurred. Replaced it with this actual
independent reading under the required heading, preserving attribution. Also corrected
the worker report's `D.geometricFiber 𝓧` typo to `D.geometricFiber 𝓧.X₀`.
No Lean or node-record correction is needed. All mathematical clauses pass.
