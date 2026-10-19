## Worker report

The module defines the canonical idempotent ideal and quotient component ring for a connected
component of an affine spectrum, a residue quotient separable-algebraicity predicate, and states
Artin's henselian tensor residue dichotomy. The hypotheses bind commutative rings `R`, `B₁`, and
`B₂`, their `R`-algebra structures, and `Algebra.IndEtale` instances. The hypotheses `h₁` and
`h₂` render the assumption that every component quotient of each factor is henselian local.
The first conclusion quantifies over every point of the tensor-product spectrum and renders both
henselian locality of its component quotient and equality of the quotient spectrum's image with
that connected component. The second conclusion quantifies over every maximal ideal `m`; its
first disjunct renders separable closedness of the residue quotient, while the two existential
disjuncts render contraction to a maximal ideal of `B₁` or `B₂`, the canonical quotient-map
commuting square, and separable algebraicity of the induced residue field map.

The component ideal is `Ideal.span` of the idempotents whose zero locus contains the connected
component, exactly the node's `I_Z`; the component ring is the corresponding ideal quotient.
`RingHom.IsSeparableAlgebraic` installs the canonical quotient field and algebra structures before
using `Algebra.IsAlgebraic` and `Algebra.IsSeparable`. `Ideal.IsSepClosedQuotient` similarly
installs the maximal-ideal quotient field before `IsSepClosed`.

Dependencies used are `AlgebraicGeometry.Spec` from Mathlib (the affine-spectrum convention),
`Algebra.IndEtale` from `Sheaf.RingTheory.IndPrincipalZariski`, and `HenselianLocalRing` from
`WeilConjectures.Mathlib.RingTheory.Henselian`. The proof is intentionally `sorry` at stage 2;
its docstring records the six component, tensor, Artin-join, contraction, and residue-separability
steps from the node proof.

Edge cases checked: the zero tensor product has empty spectrum and no maximal ideals, making both
conclusions vacuous; the component quantifier uses `PrimeSpectrum` points and does not assume
finiteness or nonemptiness; both factor alternatives are retained explicitly.

Searches made: `msearch.py` LeanFinder and LeanSearch queries for the Artin henselian tensor
residue statement (no match); `msearch.py` Loogle for `Algebra.Etale, HenselianLocalRing` (no
match); `msearch.py` grep for `quasi.?acyclic|hensel.*tensor|tensor.*hensel` (no match); `rg` over
Mathlib and `WeilConjectures` for Artin/henselian tensor/residue declarations (no matching theorem).

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (NT-cc, 2026-10-18)

H4: `PrimeSpectrum.componentIdeal`, `PrimeSpectrum.componentRing` and its quotient `CommRing`
instance duplicated `AlgebraicGeometry.componentIdeal`, `AlgebraicGeometry.componentRing` and
`AlgebraicGeometry.componentSpectrumMap`. These were already in the delivery's base (05b876bbde),
in `Sheaf.TraceFormula.AffineEtaleCoverComponentCriterion` (lem-trf-affine-etale-cover-component-criterion).
They give the same convention: `I_Z` is spanned by the idempotents vanishing on `Z`, and
`C_Z = C / I_Z`. The fix states the theorem with them, writes the range clause with
`componentSpectrumMap`, drops the duplicates, drops the unused `Mathlib.AlgebraicGeometry.Scheme`
import, and gives the six node proof steps in the statement docstring (H8). The mathematics
is unchanged. The fixed file compiles clean through nt_compile.py.
