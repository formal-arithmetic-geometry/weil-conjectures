## Worker report

The module defines `IsN1` and `IsN2` for a domain `R` and its fraction field `K`.
`IsN2` is the Japanese condition. It also states `isN1_of_isN2`, the last sentence of
the node; its proof is postponed as required for stage 2.

Node hypothesis and clause mapping:

- Integral domain `R`: `(R : Type u) [CommRing R] [IsDomain R]` in both definitions.
- Fraction field `K`: `(K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]`.
- N-1 integral closure in `K`: `integralClosure R K` in `IsN1`.
- N-1 finite `R`-module: `Module.Finite R (integralClosure R K)` in `IsN1`.
- Every finite field extension `L/K`: `∀ (L : Type v) [Field L] [Algebra K L]
  [FiniteDimensional K L]` in `IsN2`. The instance quantifiers range over all
  structures of the specified type, including inseparable extensions.
- `R` acts on `L` through `K`: `[Algebra R L] [IsScalarTower R K L]`.
- Integral closure in each `L` finite over `R`:
  `Module.Finite R (integralClosure R L)`.
- N-2 implies N-1 by `L = K`: `isN1_of_isN2 (h : IsN2 R K) : IsN1 R K`.

Dependency declarations: `integralClosure` from
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (the carrier is `IsIntegral R`);
`Module.Finite` from `Mathlib.RingTheory.Finiteness.Defs`;
`Algebra` from `Mathlib.Algebra.Algebra.Defs` (field extension);
`FiniteDimensional` from `Mathlib.LinearAlgebra.FiniteDimensional.Defs`;
`IsFractionRing` from `Mathlib.RingTheory.Localization.FractionRing`.
The three node dependencies are Mathlib matches, so no project import is needed.

Edge cases: no Noetherian or integrally closed hypothesis was added. The quantifier
includes `L = K` and extensions of degree one, inseparable finite extensions,
and characteristic zero or positive. The fraction field condition excludes the
zero ring as required by the node's domain hypothesis. `L : Type v` is at the
field's universe level; every finite extension can be represented at that level.

Searches: `msearch leanfinder` with "Japanese domain N-2 finite integral closure
in every finite extension of its fraction field" returned only finiteness
theorems such as `IsIntegralClosure.finite`, no Japanese predicate. `msearch
loogle` on `IsJapanese, IsN1, IsN2` returned no hit. `msearch grep` on
`Japanese|IsN1|IsN2|Nagata` in `RingTheory` returned only a Noether
normalization comment. `rg` over Mathlib, `WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` found no predicate. `grep -rn` for the node id
in `WeilConjectures` found nothing. Stacks Tag 032F was checked on its website;
the local `literature/stacks-project/algebra.tex` is absent in this checkout.

Server compile: clean, exit code 0.

## Second reading by J1

I reopened the node `def-weil-pbc-japanese-domain`, its recorded Mathlib
dependencies, and `lean/Sheaf/RingTheory/JapaneseDomain.lean`.  The source is
Stacks Algebra, Definition 032F (`definition-N`).

Statement list and rendering:

- The object `R` is an integral domain: the binders
  `(R : Type u) [CommRing R] [IsDomain R]` occur in both `IsN1` and `IsN2`.
- The object `K` is the field of fractions of `R`: `[Field K] [Algebra R K]
  [IsFractionRing R K]` occurs in both definitions.  This is exactly the
  fraction-field hypothesis, with no Noetherian or integrally-closed premise.
- N-1 means that the integral closure of `R` in `K` is finite as an `R`-module:
  `IsN1` is `Module.Finite R (integralClosure R K)`.
- For N-2, `IsN2` quantifies a field `L : Type v` with
  `[Field L] [Algebra K L] [FiniteDimensional K L]`, so the extension is finite.
  The additional `[Algebra R L] [IsScalarTower R K L]` expresses the required
  composite `R`-algebra structure through `K`.
- The N-2 conclusion is exactly
  `Module.Finite R (integralClosure R L)` for each such `L`; no separability,
  characteristic, or other restriction is added.
- The final source clause, N-2 implies N-1 by taking `L = K`, is represented by
  `isN1_of_isN2 (h : IsN2 R K) : IsN1 R K`.

Verdict: every object, hypothesis, quantifier, and conclusion clause agrees
with the node.  The universe choice `L : Type v` is the same convention used by
the recorded finite-extension encoding; it includes `L = K`, degree-one and
inseparable extensions, and works in both characteristic zero and positive
characteristic.  The domain/fraction-field assumptions exclude the zero-ring
case as in the node.  No mismatch was found and no source or Lean change was
needed.

I rechecked the existing-definition searches recorded by the worker: LeanFinder,
Loogle, LeanSearch, grep over Mathlib and `WeilConjectures`, and local-search
all found no N-1/N-2/Japanese predicate.  The declarations used are Mathlib's
`integralClosure`, `Module.Finite`, `Algebra`, `FiniteDimensional`, and
`IsFractionRing`; none is a private duplicate.  The module compiles cleanly
with `scompile.py` (only the permitted postponed proof is present).
