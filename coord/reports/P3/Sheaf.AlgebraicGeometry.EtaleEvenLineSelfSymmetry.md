## What changed

Filled `AlgebraicGeometry.Etale.CoordinateTrace.evenLineSelfSymmetry` in the assigned
module. Its statement and public import are unchanged. Two new proved modules supply
ordinary etale line flatness/self-braiding and the generic derived even-shift computation.
Their private helpers calculate the signed braiding on every total-tensor summand,
cancel the canonical K-flat comparison, and transport along the single/shift isomorphism.
The assigned theorem combines these two results. No shared definition is changed.

The ordinary etale lemma and final specialization locally disable
`ModuleCat.MonoidalCategory.instBraidedCategory`, following existing library practice.
This selects the braiding inherited from the symmetric structure, exactly as the published
derived symmetry does, and avoids expensive kernel comparison of two definitionally
equal braiding instances. This attribute is limited to each declaration; no importer
sees an instance change. A private irreducible wrapper constructs the canonical shift
isomorphism. The new modules use Mathlib's local `suppress_compilation` command for
noncomputable categorical constructions; every theorem remains kernel checked.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.CoordinateTrace.evenLineSelfSymmetry`
(node `lem-sfb-etale-even-line-self-symmetry`), the module's sole original hole.
Added: zero holes. Remaining in the delivered module: zero holes.
No unproved intermediate statement is split off. The two new public theorems are
proved, with zero `sorry` in either new module.

## No longer needed

The proof does not need the planned generic ringed-site modules
`Sheaf.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair`
(`lem-pur-sheaf-line-evaluation-inverse-pair`),
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
(`lem-weil-pbc-site-derived-tensor-descent`), or
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
(`lem-sfb-ringed-derived-monoidal-comparisons`). These were planned dependencies,
not imports in the original item. The existing etale tensor-inverse construction,
explicit signed cochain braiding, and source localization comparison prove the
needed special cases directly, avoiding conversion to arbitrary ringed sites.
No existing module is withdrawn. The original public data import is retained. An unused proof import of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse` is omitted
from the generic even-shift module; the ordinary etale module uses it.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The DAG's proposed general ringed-site interfaces are
unnecessary for this etale special case: the adopted source already provides the
canonical evaluation inverse and the precise braiding/localization comparison.
The unit route is unchanged. Ordinary local joint faithfulness is applied only to
sheaf morphisms, never to arbitrary derived morphisms. The single-complex proof
includes all other summands as zero-source cases and treats every even integer,
including negative degrees; no nonzero-ring or nonempty-scheme assumption is used.

## New nodes

- `lem-sfb-etale-line-flat-braiding`, module
  `Sheaf.AlgebraicGeometry.EtaleLineFlatBraiding`: ordinary rank-one flatness and identity
  self-braiding, proved from the etale tensor inverse and jointly faithful pullbacks.
- `lem-sfb-even-shift-canonical-self-symmetry`, module
  `Sheaf.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry`: canonical self-symmetry
  of any even shifted flat object with identity ordinary self-braiding, proved by the
  explicit Koszul formula and K-flat localization comparison.

Validation: all three modules compiled together via `lcompile.py --all` before delivery:
generic even-shift 47.9 s, ordinary etale line 41.4 s, assigned item 47.0 s.
The delivery preflight repeats compilation against the delivered packet and checks axioms.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
