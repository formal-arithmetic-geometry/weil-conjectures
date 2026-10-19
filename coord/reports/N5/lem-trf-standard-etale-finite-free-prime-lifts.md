## Worker report

The module `Sheaf.TraceFormula.StandardEtaleFiniteFreePrimeLifts` states the finite-free
standard-etale domination and prescribed prime-lift theorem from Stacks Project Algebra,
Tag 00UF (lemma-standard-etale-finite-flat-Zariski, clauses (1)--(3)).  The declaration
uses Mathlib's `Polynomial`, ideal quotient, `Localization.Away`, `CommRingCat`,
`Module.Basis`, `AlgebraicGeometry.Spec.map`, `PrimeSpectrum`, and the `Surjective`
class.  The derivative-unit hypothesis is the image of `f.derivative` under the
canonical polynomial-quotient map followed by localization.

The Lean statement renders the hypotheses as follows: `R : Type u` with `[CommRing R]`,
polynomials `f g : R[X]`, and `hf : f.Monic`; `hunit` says the image of the formal
polynomial derivative is a unit in the localized quotient algebra.  Its first conclusion
is an existential commutative ring object `C : CommRingCat.{u}`, a natural number `r`,
and an `R`-algebra structure on `C`.  `Nonempty (Module.Basis (Fin r) R C)` is the
finite basis indexed by `{1,...,r}` up to the canonical `Fin r` reindexing.  The next
conjunct states the nonzero-ring clause `Nontrivial R → 1 ≤ r`.  The following conjunct
is surjectivity of `Spec C → Spec R` via `Spec.map`.  Finally, for every
`q : PrimeSpectrum B` and `q' : PrimeSpectrum C` whose contractions along the two
`algebraMap R` maps agree, it gives `c ∉ q'.asIdeal` and an `R`-algebra homomorphism
`φ : B →ₐ[R] Localization.Away c`; the displayed ideal-comap equality is exactly
`φ⁻¹(q' C_c) = q` (the extension is written as `Ideal.map` into `C_c`).  Here
`B` is the explicit localized quotient
`Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)`.  Natural numbers already
include `r ≥ 0`; the zero ring and constant monic polynomial cases are not excluded.

The statement dependencies used are the recorded Mathlib declarations:

- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic.Polynomial`.
- `def-weil-ring-localization-away`: `Mathlib.GroupTheory.MonoidLocalization.Away.Localization.Away`.
- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic.Module.Free`; the
  finite-index basis is rendered directly by `Module.Basis (Fin r)`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme.AlgebraicGeometry.Spec`
  and `Spec.map`.
- `def-weil-surjective-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap.AlgebraicGeometry.Surjective`.

The stage-1 proof dependencies (finite-free splitting, integrality/lying-over, residue
factor selection, and standard-etale root maps) remain DAG proof dependencies; they do
not have stage-2 declarations to import, so the statement module only imports Mathlib
modules needed to type the statement.

Edge cases checked: `r = 0` is allowed for the zero ring; `Nontrivial R` forces
`1 ≤ r`; constant monic polynomials are retained; `Fin r` allows the empty basis when
`r = 0`; zero polynomials and zero quotient rings remain legal; `PrimeSpectrum` quantifies
vacuously when the relevant ring has no primes; localization at `c` is used only after
requiring `c ∉ q'.asIdeal`.

Searches made before writing:

- `msearch.py ... leanfinder "Every standard etale algebra is dominated ... prescribed
  prime lifts"`: returned standard-etale presentations and etale-locus results, with no
  finite-free prescribed-lifts theorem.
- `msearch.py ... leansearch "For a standard etale algebra R[t] localized at g modulo a
  monic f ... prescribed prime image"`: returned standard-etale presentation and
  localization APIs, no exact theorem.
- `msearch.py ... loogle "StandardEtalePair, Module.Free"`: zero hits.
- `msearch.py ... grep "standard.etale.*finite.*(flat|free)|finite.*(flat|free).*standard.etale"`:
  zero hits in Mathlib.
- Source grep for `standard.etale.*finite.*free` in `WeilConjectures`: zero hits.
- DAG grep for the item and its finite-free/prime-lift wording: only this item and its
  already recorded stage-1 auxiliary nodes; no existing statement declaration.

Compilation was run with:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N5
lem-trf-standard-etale-finite-free-prime-lifts
lean/Sheaf/TraceFormula/StandardEtaleFiniteFreePrimeLifts.lean`.
Both sandbox and library compilation completed without errors or warnings.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
