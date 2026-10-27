## What changed

Repair of returned delivery 6140f535d51 (reviewer C-6140f): the landing ledger
reported `<unattributed:42:1744>` in the item. This is the `sorry` component of
`set_option warn.sorry false`, before the first declaration, rather than a proof
hole. Removed that option from the item, canonical data, and both split modules.
The source census now records only the two named theorem holes. No declaration, signature,
proof, or canonical construction changed during this repair. Compared the retained
packet with the current shared source; its original canonical declarations and
main theorem signature remain unchanged. The delivery tool rebases the packet on
the freshly fetched `origin/sheaf-dag` and runs compilation and server preflight.

Validation: `lcompile.py --all` compiled all five retained Lean files successfully
(exit code 0). The exact returned ledger diagnostic was reproduced by restoring
the removed option in memory, and `sorry_ledger.missing_gate` passes on every
repaired file against the current shared source.

Reduced `AlgebraicGeometry.ProEtale.finiteGeneralRingSmoothPurity` to two independent,
strictly smaller geometric assertions, while preserving its signature and all clauses.
The proof derives finite-type geometric witnesses, constructs theta as the inverse
canonical dualizing-unit comparison followed by comparison of alpha, and proves both
required comparison equations. The tensor formula is proved from the generic private
arguments already proved in `FiniteSmoothLevelOfOrientation`, using a proof-only
`import all`; no source module or private proof was changed or duplicated. Naturality
of a line-variable source-to-origin transformation proves equality of the entire gamma
maps from the common-level orientation equation. This last calculation holds on every
pro-etale object, so in particular on the required intrinsic Dctf domain.

Extracted all existing canonical definitions and the finite quotient instance verbatim
into `FiniteGeneralRingData`, publicly re-exported by the original module. This avoids
cycles between the theorem and its separate proof steps. All six original public
imports remain verbatim. The original declaration types, bodies, visibility and
instance behavior are unchanged. See
`coord/changes/X2-finite-general-ring-data-extraction.md` for the nine downstream users.

## Proved and sorry left

Original item: one hole, `AlgebraicGeometry.ProEtale.finiteGeneralRingSmoothPurity`
(`det-sp-finite-general-ring`). Its proof is now complete from the two split statements.
This is a decomposition, not a completed mathematical proof: one upper hole closed,
two lower holes added, net minus one. The tensor clause is fully proved by
`AlgebraicGeometry.ProEtale.finiteGeneralRingTensorFormula`
(`lem-pur-finite-general-ring-tensor-formula`), with no new hole.

Every remaining hole, each in its own new module with proof exactly `by sorry`:

- `AlgebraicGeometry.ProEtale.finiteGeneralRingOrientation`, node
  `lem-sp-general-ring-orientation`: coefficient-extension/direct-orientation agreement,
  excluding both the tensor formula and exponent independence.
- `AlgebraicGeometry.ProEtale.finiteGeneralRingExponent`, node
  `lem-sp-general-ring-exponent`: Kummer comparison of normalized orientations through
  the common maximum exponent, excluding tensor maps and scalar extension from Q_ell.

The canonical data module has zero holes. No definition chooses an arbitrary witness
from an unproved existence assertion. The proof only destructs existence theorems within
its proposition and constructs theta from the explicitly prescribed isomorphisms.

## No longer needed

All original proof-only imports were removed from the item:

- `Sheaf.Paper.LocalizingExceptionalAdjoint`.
- `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`.
- `Sheaf.Paper.VectorBundlePurity`.
- `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`.
- `Sheaf.AlgebraicGeometry.VectorBundleIntegration`.
- `Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration`.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`.
- `Sheaf.Paper.PurityDiagonalBaseChangeCompared`.
- `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
- `Sheaf.AlgebraicGeometry.SmoothTensorDuality`.
- `Sheaf.Paper.FiniteSmoothGammaNormalization`.
- `Sheaf.Paper.NoetherianEtaleSectionSpecialization`.
- `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose`.
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`.
- `Sheaf.Paper.FiniteComparisonLocalizing`.
- `Sheaf.Paper.PurityDncFamilyIntrinsic`.
- `Sheaf.Paper.PurityDncInvariance`.
- `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport`.

Their mathematical use is now localized as follows. The orientation split retains the
original diagonal/Rees/vector-integration argument and its dependency nodes; the
exponent split retains the Kummer/trace/normalization argument. Thus those original
orientation dependencies are deferred to their genuine substeps, not claimed pruned
from the target closure. The tensor proof uses the existing generic finite-ring origins,
ordinary smooth exceptional bounds and smooth tensor duality, so it does not use the
old localizing-category assembly route. In particular
`det-ctf-finite-comparison-whole`, `det-ctf-finite-comparison-localizing`, and
`sk-prop-sf-existence` are unnecessary for this tensor proof; no claim is made that
these modules are globally unreachable. Compactification is supplied directly by
`def-asd-compactifiable` rather than the condensed-ring compactification wrapper.
No module is withdrawn. No adopted source declaration or public import is removed.

## Where the brief, the DAG or earlier work was wrong

The previous packet retained a warning-suppression option that the landing source
hole census interprets as a hole token. Removing it repairs the exact returned
failure; the source-only census now attributes both actual holes to their named
public theorems and finds no unattributed holes in any of the five Lean files.
There is no corresponding module build-error file in the shared clone; the return
entry itself contains the ledger diagnostic.

The original planned tensor comparison is longer than necessary: the actual defined
proGamma already is comparison of the ordinary tensor mate after its canonical
source-to-origin map. Existing proved private generic lemmas establish its isomorphism,
constructibility and naturality for arbitrary finite rings. Only the public theorem
in that file specializes to literal prime powers; the private arguments do not.

The smooth-of-relative-dimension hypothesis is not itself a registered instance of
Smooth. The assembly explicitly supplies `SmoothOfRelativeDimension.smooth` before
deriving local finite type and applying compactifiability. No statement correction
or change in target meaning is needed.

The sandbox already contained an initial tensor-formula lemma and searches at the
start of this session. That proved lemma was retained and integrated; no other agent
was started. The report gives the actual final two-hole decomposition.

## New nodes

`def-sp-general-ring-canonical-data`: exact extraction of the existing canonical data
and finite-ring instance; no new mathematical notion. The old module re-exports it.

`lem-sp-general-ring-orientation`: original proof (1)-(2), comparing all three direct
orientation factors under coefficient extension. Edge cases: rank zero, empty schemes,
zero ring, and nonflat finite A are included. The equation uses the specified unit and
scalar maps, so no orientation is unconstrained.

`lem-sp-general-ring-exponent`: original proof (3), Kummer-normalized common-exponent
orientation comparison. Both exponents are positive; the maximum annihilates A by
multiplicity. Rank-zero tensor powers are identities; zero rings and empty schemes
satisfy the same equations. The conclusion only compares orientations.

`lem-pur-finite-general-ring-tensor-formula`: proved arbitrary-finite-ring tensor and
constructibility lemma, with arbitrary L and orientation alpha; N need not be a prime
power. Its proof uses the previously proved generic arguments in the source module.

Mathlib searches covered LeanSearch, Loogle, LeanFinder and grep; generic category
isomorphism lemmas were found, but none supplies the geometric normalization assertions.
Blueprint-wide searches for exponent independence, coefficient orientation, tensor
purity and Kummer power found no duplicate statement.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
