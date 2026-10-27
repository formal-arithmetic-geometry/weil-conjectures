## What changed

Completed `AlgebraicGeometry.ProEtale.snc_root_stage_system` in
`Sheaf.AlgebraicGeometry.SNCRootStageSystem`, preserving its statement and all four
existing definitions. The repaired proof imports the already proved generic
basis and evaluator from `Sheaf.RingTheory.HenselianParameterRootRegularity`.
That unclaimed module is included solely to expose six existing helpers with
unchanged types and bodies: `Algebra.rootCoordinate_pow`, `Algebra.root_basis`,
`Algebra.rootEval`, `Algebra.rootEval_scalar`, `Algebra.rootEval_coordinate`,
and `Algebra.rootHom_ext`. Source docstrings were added. No source-library
file, existing public statement, or mathematical definition changes.

The proof uses the existing root monomial basis, whose proof is the explicit
exponent-reduction normal form. The existing quotient evaluator constructs the
transition maps, inclusions, iterated-root equivalences and compatible-root colimit map. Localization transports
the relative bases. The Gamma-Spec adjunction supplies the scheme limit property.
The existing finite-root-face regularity and branch-equation nonzerodivisor
results give the regular coordinate Cartier divisors. Coefficient-change pushouts
for the literal root quotient and its localization give the normalized affine
base change; equal ranges of open immersions give the open-pair comparison.

Addressed all eight duplicates in the return at `cd41909f028`: removed the
local `regular_localization` and all seven listed normal-form/evaluation lemmas.
The normal-form block and evaluator construction are removed entirely. All
finite-stage scalar evaluation uses `Algebra.rootEval_scalar`; the basis comes
from `Algebra.root_basis`. Two coordinate-notation wrappers apply the existing
power relation and extensionality theorem directly. The first delivery compile hit the fixed 60-second limit. The evaluator,
transition, inclusion and localized-map private definitions are now irreducible,
with explicit unfolding only in their formula lemmas. Coordinate formulas use
the existing `Algebra.rootEval_coordinate` API directly. This avoids repeatedly
expanding quotient presentations during later inference and checking; the final
version compiled in 57.0 seconds without warnings. No file or proof was split.
Both localization uses now
apply the existing public `RingTheory.isRegularRing_of_localization` with its
standard unit, fraction, and zero criteria. The private upstream helper stays
unchanged.

The change record is `coord/changes/H9-snc-root-existing-api.md`; it inventories
all downstream consumers and records the additive visibility change. Updated
the existing henselian node's Lean attachment with these six helpers and the
stage-system node's proof dependencies to record their reuse. The unit
statement and route are preserved. Earlier unused draft modules were removed
from the sandbox; none existed in the shared library and none is withdrawn.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.snc_root_stage_system`
(node `lem-sfb-snc-root-stage-system`). Proved 1 of 1 original sorries.
Added zero holes and split off zero statements. The delivered Lean module contains
zero `sorry` tokens; every private helper is proved and every definition is an
explicit construction. The imported root-face and branch-equation results have
complete proofs in the current library.

Validation: the exposed API module compiled with `lcompile.py` (24.5 seconds).
The complete stage-system module compiled without warnings (57.0 seconds, final version).
The import-pruning and duplicate-statement check passed for both changed modules.
All three direct consumers compiled against the changed API without warnings:
`HenselianParameterRootDomainTower` (42.4 seconds), `ParameterRootBoundaryDvrs`
(39.6 seconds), and `StrictLocalPrimeToPKummerSplitting` (45.0 seconds).
They need no adaptations; their temporary byte-identical validation copies were
removed from the sandbox. Delivery preflight performs the final signature/axiom
checks. The main theorem signature and four public definitions were also checked
byte-for-byte against the current shared source.

## No longer needed

Removed the repeated private normal-form construction, all seven returned
normal-form/evaluation duplicate lemmas, the repeated root quotient evaluator,
and `regular_localization`. Their existing proved implementations are reused.
This removes three additional proof imports from the returned packet:
`Mathlib.LinearAlgebra.Finsupp.LinearCombination`,
`Mathlib.LinearAlgebra.Quotient.Basic`, and
`Mathlib.LinearAlgebra.Finsupp.VectorSpace`. No module is withdrawn.

Removed these original proof imports:

- `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleRegularDivisorBaseChange`:
  etale regularity follows directly from the existing stalk theorem.
- `Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType`: Mathlib composition instances
  supply the required finite type assertions.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`: scheme weak-etale base change
  needs no ring ind-etale transport.
- `WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise`:
  direct presentation pushouts prove coefficient base change.
- `Mathlib.RingTheory.MvPolynomial.Localization`: localization universal
  properties and finite type instances suffice.
- `Mathlib.RingTheory.Localization.BaseChange`: the ring pushout and iterated
  principal-localization APIs suffice.
- `Mathlib.RingTheory.Etale.Weakly`: scheme base-change instances suffice.
- `Mathlib.RingTheory.AdjoinRoot`: the existing generic monomial-basis theorem
  supplies the bases.

Consequently this proof no longer uses these original planned dependency nodes:
`lem-sbc-etale-regular-divisor-base-change`, `lem-kun-etale-lfp`,
`lem-weil-pbc-monic-quotient-free`,
`lem-weil-pbc-localization-away-polynomial-quotient`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-exc-weakly-etale-ring-base-change-composition`,
`def-weil-pbc-ind-etale-algebra`,
`lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise`, and
`lem-weil-pbc-localization-tensor-over-base`.
The retained public definition dependency may still import some of their modules
for its own purposes; this is pruning of this proof's route, not a claim that
those declarations can be removed from the adopted source tree.

Removed obsolete tool-use entries for the etale divisor lemma, etale finite type
lemma and filtered-colimit tensor lemma; retained the localization-regularity
entry in its original order.

## Where the brief, the DAG or earlier work was wrong

The returned proof unnecessarily duplicated private implementation lemmas
already present in HenselianParameterRootRegularity. Exposing its existing
proved API removes that duplication. The similarly named localization helper
in the adopted source library is private; using its public underlying theorem
avoids changing the adopted source file. The SNC and parameter-root coordinates
are definitionally equal but have different names; explicit applications of
the existing power and extensionality theorems provide the SNC rewrite forms.

No statement correction was needed. The planned monic-quotient induction and
filtered-colimit tensor calculation were longer than the direct normal-form
and presentation-pushout proofs formalized here. The node and theorem proof
explanation now describe the implemented argument. Zero rings, empty tuples,
order one, zero localizations and empty coordinate divisors require no extra
nonemptiness or nonzero hypotheses.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
