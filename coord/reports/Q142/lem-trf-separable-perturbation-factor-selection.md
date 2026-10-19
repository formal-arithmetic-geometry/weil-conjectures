## Worker report

`Sheaf.TraceFormula.SeparablePerturbationFactorSelection` states
`ValuationSubring.exists_separable_irreducible_transcendental_residue`, with its proof `sorry`.
It introduces no new definitions or auxiliary theorems. It uses the already published
`ValuationSubring.comapResidueFieldMap` from `Sheaf.FieldTheory.AbhyankarInequality`.
The landed owner `lem-trf-abhyankar-inequality` is added to `stmt_deps` because its canonical
residue-field embedding now appears in the signature; it was already a proof dependency.
No natural-language statement or proof changes.

Clause-by-clause match with the node:

- A separably closed field K: `{K : Type u} [Field K] [IsSepClosed K]`.
- The rational function field K(t): `RatFunc K`, with indeterminate `RatFunc.X`. Polynomial
  evaluation `Polynomial.eval₂ (algebraMap K (RatFunc K)) RatFunc.X f` is precisely f(t).
- A valuation subring O: `O : ValuationSubring (RatFunc K)`. Mathlib's defining alternative
  includes zero as well; at zero it is automatic, so it is equivalent to the node's
  alternative for nonzero elements.
- R = O ∩ K: `O.comap (algebraMap K (RatFunc K))`. This is a construction, not an arbitrary
  extra ring with an assumed identification.
- The quotient fields κ(R) and κ(O): `IsLocalRing.ResidueField` of those valuation rings;
  their maximal ideals are the nonunits by Mathlib's local-ring structure.
- A monic irreducible polynomial f: `f : Polynomial K`, `hf_monic : f.Monic`, and
  `hf_irreducible : Irreducible f`. Over a field, irreducibility entails nonzero and
  nonunit and has exactly the unit-factor condition stated by the node.
- A nonzero scalar π: `π : Kˣ`. Over a field units are precisely nonzero scalars, with no
  restriction that π itself belong to R or its maximal ideal.
- f(t)/π is a unit of O: `v : Oˣ` and `hv` equating its underlying rational function to
  the specified quotient. Supplying the witness as a binder is equivalent to the node's
  unit-membership hypothesis: all witnesses have the same underlying element and residue.
- Its residue is transcendental over κ(R): `htrans` is Mathlib's `Transcendental` of
  `IsLocalRing.residue O (v : O)`, with the algebra instance explicitly supplied by
  `(O.comapResidueFieldMap (algebraMap K (RatFunc K))).toAlgebra`. This is the canonical
  residue-field inclusion, not an arbitrary algebra structure.
- The output is an existential `g : Polynomial K`, `π' : Kˣ`, and `w : Oˣ` with
  `g.Monic ∧ g.Separable ∧ Irreducible g`, the normalized-evaluation equality, and the
  identical `Transcendental` condition for the residue of w. These are exactly the
  polynomial, nonzero scalar, unit, and transcendental-residue clauses of the node.
- The last sentence is a separate universal conjunct:
  `∀ g : Polynomial K, g.Monic → g.Separable → Irreducible g → g.degree = 1`.
  It asserts degree one for every polynomial specified there, not just the output witness.

Dependency declarations and source signatures/docstrings inspected:

- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`; it supplies the field
  inclusion `algebraMap K (RatFunc K)` and the algebra induced by a residue ring homomorphism.
- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-kun-transcendence-degree`: `Algebra.trdeg`,
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`; imported as the recorded dependency
  and used in the natural-language proof plan. For the single residue element the exact
  Mathlib predicate is `Transcendental`, defined as `¬ IsAlgebraic` in
  `Mathlib.RingTheory.Algebraic.Defs`.
- `def-kun-separably-closed`: `IsSepClosed`, `Mathlib.FieldTheory.IsSepClosed`; the recorded
  list contains both `IsSepClosed` and `IsSepClosure`. Only the former is needed here.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`;
  degree and leading coefficient use Mathlib's polynomial API.
- `def-weil-rational-function-field`: `RatFunc`, `Mathlib.FieldTheory.RatFunc.Defs`, and
  its variable/evaluation API in `Mathlib.FieldTheory.RatFunc.AsPolynomial`.
- `def-pc-separable-polynomial`: `Polynomial.Separable`, `Mathlib.FieldTheory.Separable`,
  literally `IsCoprime g (derivative g)`.
- `lem-trf-abhyankar-inequality`: `ValuationSubring.comapResidueFieldMap`,
  `Sheaf.FieldTheory.AbhyankarInequality`; read the full module, including its
  `comapInclusion` and named localness theorem. Its map is Mathlib's quotient-induced map
  on residue fields for the specified field inclusion.

The proof dependencies with declarations are imported: the relative algebraic closure
through `import Mathlib.FieldTheory.AlgebraicClosure`, and the derivative and splitting
facts through the public separability and separably-closed imports already required by the
statement. `lem-trf-residual-curve-value-group` has no recorded declaration or Mathlib match
in the base read for this delivery, so there is no proof-only module to import for it yet.
No missing statement prerequisite is being postponed.

Edge cases checked before finalizing the statement: arbitrary characteristic, including
imperfect separably closed fields; the trivial restricted valuation R = K; O the whole
rational function field; t outside O; π outside R; and inseparable f. No discrete valuation,
rank-one valuation, perfectness, finite-height, integrality of t, or nontriviality of R's
valuation is assumed. Zero/unit polynomials cannot satisfy irreducibility, and the empty
factor list only occurs for the unit polynomial. Degree one is stated using `degree`, so
no convention for the degree of zero affects the conclusion. The only universe is K's
arbitrary universe u; RatFunc, the subrings and their residue fields live in that universe.

Searches performed for this delivery, rather than relying on the inherited search record:

- `msearch.py` LeanFinder: "For a valuation subring of K(t) over a separably closed field,
  replace an irreducible polynomial with transcendental normalized residue by a separable
  irreducible polynomial". Eight generic hits; `Polynomial.exists_separable_of_irreducible`
  concerns Frobenius expansion in characteristic p, and the other hits concern Weierstrass
  curves, purely inseparable extensions, or polynomial preparation. None includes this
  valuation/residue conclusion.
- `msearch.py` Loogle: `Polynomial.Separable, ValuationSubring`. Zero hits.
- `msearch.py` grep in `RingTheory`: `perturb|transcendental.*residue|residue.*transcendental`.
  One hit, `Mathlib/RingTheory/QuasiFinite/Polynomial.lean`, using
  `RatFunc.transcendental_X`; no perturbation/factor-selection statement.
- Direct `rg` of Mathlib, `WeilConjectures/`, the shared `lean/Sheaf/`, and
  `dag/lean_names_upstream.json` for the item id, the proposed theorem name,
  separable-perturbation names, and valuation/residue helpers found no existing exact
  statement. The helper search found the already landed Abhyankar module; all temporary
  duplicate helpers from the early draft were removed in favor of its canonical map.

Source checked: https://arxiv.org/pdf/0707.3953v3, printed p. 28, Proposition 4.3.1 proof,
separable perturbation paragraph. The node already expands this source argument to
unrestricted t and the trivial restriction valuation; the eight-step proof docstring
retains that expansion and its named dependencies. No statement dispute or correction.

Validation: final module compiled through `scompile.py`; delivery preflight and per-file
compilation are run through `deliver2.py --no-push` before the push.

## Second reading by Q142

This is the dispatcher's worker's separate self-check; no second worker was spawned.
With the complete node and the final file open, I rechecked every hypothesis and output:
Field/IsSepClosed, RatFunc with its own indeterminate, ValuationSubring, comap for O ∩ K,
monic/irreducible f, nonzero π as a field unit, the actual normalized unit witness v, and
its residue via the canonical restricted-field map. I then checked the output g, its
three polynomial predicates, nonzero π', unit w, normalized quotient equality, and
transcendental residue. The universal degree-one assertion is outside the existential,
so it applies to every monic separable irreducible polynomial as the node says.

The initial draft duplicated a canonical residue-field construction and included an
auxiliary localness theorem. The final file removes all five helper declarations and
uses the published `ValuationSubring.comapResidueFieldMap`, adding its landed owner to
`stmt_deps`. Thus there is only the item's named theorem with `sorry`. I also checked
that `lean.statement` stops before the proof delimiter, as the preflight parser expects,
and that the date is the date returned by `date -u +%F`. No mismatch in the final
mathematical signature remains.
