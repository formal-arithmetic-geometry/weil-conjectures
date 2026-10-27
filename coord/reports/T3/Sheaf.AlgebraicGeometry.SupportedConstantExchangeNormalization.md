## What changed

Filled the six proof bodies in
`lean/Sheaf/AlgebraicGeometry/SupportedConstantExchangeNormalization.lean`.
The argument follows the node's eight steps: cokernel presentations, normalized
open and closed adjunction mates, cokernel uniqueness, kernel restrictions of
section maps, and the unit equation for the prescribed comparison.
Added private proof helpers and private proof imports.
For the returned delivery, removed the seven rejected duplicate theorems and
also removed the duplicate constantDirect, constantInverse,
constantComparisonTerminal constructions and their redundant supporting lemmas.
The proof now imports all of SupportQuotientPairPullback and
SupportSiteComparison privately and directly uses Scheme.constantInverse_comp,
CachedConstantCoherence.proConstant_eq_inverse,
CachedConstantCoherence.constantComparisonTerminal_eq_inverse and
CachedConstantCoherence.constantComparisonTerminal_square. The existing
constantDirect_unit, constantDirect_comp, homEquiv_mate,
constantInverse_composite_adjunct and transportedHom remain proved once in
their original modules. The only retained ConstantProof helper identifies the
monoidal unit with the existing Scheme.constantDirect construction. All existing public
signatures are preserved. Factored the body of `openBackward` through the
public generic data construction `openTranspose`; unfolding it recovers the
old composite definitionally. The Boolean topology alias and site category
instance have more transparent reducibility hints, with their bodies unchanged.
These changes repair expensive definitional conversion in the open mate.

Change records:
`coord/changes/supported-constant-open-transpose.md` and
`coord/changes/supported-constant-site-reducibility.md`.
No consumer requires a forced adaptation.

## Proved and sorry left

Proved all six original holed declarations:

- `AlgebraicGeometry.SupportedConstantNormalization.presentation`
- `AlgebraicGeometry.SupportedConstantNormalization.scheme_normalization`
- `AlgebraicGeometry.SupportedConstantNormalization.site_normalization`
- `AlgebraicGeometry.SupportedConstantNormalization.sectionMap_existsUnique`
- `AlgebraicGeometry.SupportedConstantNormalization.compareSectionMap_existsUnique`
- `AlgebraicGeometry.SupportedConstantNormalization.comparison_square`

Closed 6 original holes; added 0 holes; split off 0 statements. There are no
remaining `sorry` declarations in the item and no other Lean file is delivered.
The returned-delivery repair compiled with exit code 0 in 53.0 seconds at the
standard project limit, with no errors or warnings. The six public theorem signatures
were compared with the archived original and are unchanged.

## No longer needed

No module is withdrawn, and all ten original public imports remain.
The returned packet's duplicate ConstantProof.constantDirect_unit,
constantDirect_comp, homEquiv_mate, constantInverse_composite_adjunct,
constantInverse_comp, transportedHom and constantComparisonTerminal_square are
no longer needed, nor are its duplicate constant constructions or auxiliary
constant identification proofs: the existing declarations are imported and used.
SupportQuotientPairPullback and SupportSiteComparison are retained dependencies,
not pruned modules. The unit's
eight-step route is preserved. These planned direct dependencies were removed
from this node:

- `lem-pe-constant-left-module-inverse-image`: constant coherence is proved
  directly using sheafification and the actual inverse-image adjunctions.
- `lem-weil-pbc-localize-ringed-site-morphism`: supported section maps are
  constructed directly from the kernel universal property and unit naturality.
- `prop-weil-pbc-inverse-image-modules-exact`: the existing inverse-image
  functors already supply the required finite-limit and finite-colimit instances.

The corresponding unused planned proof imports are
`Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`,
`Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`, and
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
The ordinary source-library open base-change and comparison constructions also
avoid the separate wrappers
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`,
`Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`, and
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
The pro-etale base-change node remains a dependency: its already proved
underived source-library realization is used directly.

The draft's redundant imports of `Mathlib.CategoryTheory.Adjunction.Basic`,
`Mathlib.CategoryTheory.Adjunction.Mates`,
`WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal`, and
`WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal` were removed.
No declaration from the adopted source library is removed or weakened.
Dependencies retained by other source declarations remain needed there; these
are removals of direct proof dependencies, not withdrawals from the library.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The previous missing `Mathlib.olean`
problem has been resolved by the compile service. The repaired module now compiles. The
subsequent failures were expensive definitional conversions in adjunction mates,
resolved by the generic data factorization; imported unproved statements were
used as the stage intends.

The archived original item source is byte-for-byte identical to the current
shared source. The generic transpose refactor checks the open invertibility
argument in 6.9 seconds at a reduced diagnostic heartbeat limit; the unchanged
expanded form exceeded 60 seconds during kernel conversion. The whole-module
check uses the standard project limits.

The earlier packet unnecessarily duplicated existing constant-coherence proofs.
The return names seven such theorems; all seven duplicates are removed, rather
than renamed or restated. The current shared source contains both
SupportQuotientPairPullback and SupportSiteComparison. Their existing private
helpers are reused through private import-all directives. Neither module is
modified, restored or withdrawn by this packet. Their DAG nodes are now explicit
proof dependencies of step 1. The Lean import and DAG dependency graphs were
checked: neither module/node reaches this item, so reuse creates no cycle.
The retained sandbox was compared with current main: the original module is
still byte-for-byte identical to its archived baseline. Existing public theorem
statements remain unchanged; the repair contains zero sorry occurrences.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
