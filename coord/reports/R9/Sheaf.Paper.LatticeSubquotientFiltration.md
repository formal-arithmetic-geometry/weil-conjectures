## What changed

Repair of returned head `82478733d86` (reviewer C-82478). The mathematical review passed;
landing rejected a reviewer fix addressed as `R9-lattice-subquotient-proof-context.md`.
The change record is now corrected directly at its canonical delivery path,
`coord/changes/R9-lattice-subquotient-proof-context.md`. It accurately describes the
actual local attributes and the unfinished spectral specialization, without requiring a
basename-only reviewer fix. The delivery tool rebases the packet on current `sheaf-dag`.

The reviewed Lean files are preserved: two private abstract assembly proofs in the item,
a proved ordered-filtration theorem, a proved ordinary scalar-extension comparison,
and separate ordered-lattice and extension-composition statements. Both existing
predicate definitions and the public theorem signature match the current main source
verbatim. The unused public BoundedConstructible import is removed; both direct consumers
already import that module independently. Three small Mathlib imports expose prerequisites.

## Proved and sorry left

The original hole remains as the named theorem `AlgebraicGeometry.ProEtale.exists_latticeSubquotientFiltration`, because its final spectral specialization repeatedly exceeded the fixed compile limit. Proved new theorem:
`AlgebraicGeometry.ProEtale.exists_locallyClosedOrderedFiltration`
(`lem-sfb-locally-closed-ordered-filtration`), including exact transport of endpoints,
inclusions, and cokernels. Also proved
`AlgebraicGeometry.ProEtale.condensedLocallyClosedExtension_scalar`
(`lem-sfb-condensed-locally-closed-scalar-extension`), for arbitrary ordinary coefficient
change and the concrete closure-factorization extension.

Added two holes, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.ProEtale.exists_orderedSpectralLattices`
  (`lem-sfb-ordered-spectral-lattices`), in `Sheaf.Paper.OrderedSpectralLattices`.
- `AlgebraicGeometry.ProEtale.locallyClosedCoefficientExtension_composition`
  (`lem-sfb-internal-locally-closed-extension-composition`), in
  `Sheaf.Paper.LocallyClosedCoefficientExtensionComposition`.

The item closes 0 of its 1 original holes and adds 2 named lower holes: 3 holes in the
delivered files in total. The complete abstract assembly and scalar comparison provide
partial progress, while the original spectral specialization remains open. No
axiom or hollow definition is introduced. The first statement has no ambient extension or
filtration; the second has no lattices, coefficient inclusion, or filtration. There are
no new definitions choosing data from a mere existence theorem.

## No longer needed

Reduced unused public interfaces:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
  (both direct importers already import it explicitly).

Removed direct proof imports:

- `Mathlib.AlgebraicGeometry.Noetherian` (available through the new filtration module).
- `Sheaf.Paper.StratifiedLattice` (needed inside the new lattice step, not directly here).
- `Sheaf.Paper.IntegralRationalizationExact`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
- `Sheaf.Paper.CoefficientHeartCommonStratification` (the generic ordered-refinement
  theorem, rather than its restricted-coefficient wrapper, is relevant to the new step).
- `Sheaf.Paper.CartesianCoefficients` (needed inside the lattice transport step).
- `Sheaf.SixFunctors.ScalarSixPullback`.
- `Sheaf.Paper.CoefficientHeartFiltration` (available through CoefficientHeart and
  used by the separate filtration module).
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence` (the new comparison uses
  the module-sheaf coherence statement, not its derived enhancement).
- `Sheaf.Paper.ContinuousRingUniverseRealization`.

The written proof does not need `lem-sfb-integral-rationalization-exact`,
`sk-def-sfb-coefficient-change`, `sk-def-sfb-derived-categories`,
`det-prop-scalar-six-pullback`, or `lem-sfb-continuous-ring-universe-realization`
as dependencies of the resulting route: ordinary scalar extension commutes directly with the open and
closed factors, without flatness or derived rationalization. It also avoids the
specialized `det-lem-coefficient-heart-common-stratification` wrapper and the full
`lem-sfb-locally-closed-extension-coherence` derived result. Removed all three obsolete
top-level tool-use entries from the parent; no new approval is inserted. The generic
module coherence step remains below the new composition bridge. No existing module is
withdrawn; these dependency removals are local to this route, not claims that other
consumers or all targets cease to need those modules. The unit's lattice/generator
argument is preserved.

## Where the brief, the DAG or earlier work was wrong

The returned packet's change record described local attributes and a finished spectral
specialization that were absent from the accepted Lean file. Those claims are corrected
in the record itself at the full repository path. The landing tool expects the reviewer-fix filename
`R9-lattice-subquotient-proof-context.change.md`; the earlier fix used `.md` instead.
No Lean proof is changed in this repair; only excess blank lines and a helper comment
are cleaned up to refresh validation against the current published build.


The unused public BoundedConstructible import caused compilation to expire before any
local declaration emitted profiling output. It is removed only from this Sheaf module;
both direct consumers were read and already import it explicitly. No source-library
public import is changed. The change record documents the downstream check.

The stated lattice declaration is smaller-universe (`E : Type`) and uses the ordinary
continuous-map ring presentation; the assigned statement uses `E : Type u` and the
universe-sized continuous ring. Its lattice finite-free predicate also needs transport
to the coefficient-heart lisse predicate. The existing private proved
`lisse_iff_locallyFree` in `QcqsLisseStratifiedIntegralLattices` supplies that last
encoding comparison and should be reused through `import all`. Applying the lattice
theorem directly is not a typed proof.
The new ordered-lattice step records these actual transport obligations.

The generic common-stratification refinement proves containment of stratum images,
not a scheme morphism through an old stratum. Refinement must use fibre products with
the old strata; image containment alone fails to control nilpotents. This is stated
explicitly in the new proof plan.

The existing locally closed coherence theorem is for sectionwise ring-module sheaves,
whereas the assigned extension is the concrete internal `openShriek >> lowerStar`
through the scheme-theoretic closure. The new composition statement isolates the
required equivalence/factorization comparison instead of silently identifying them.

The public coefficient-heart filtration wrapper is unnecessarily specialized for this
argument. Its existing private open-prefix theorem already works for any commutative
condensed coefficient ring and any module, so no constructibility conversion is needed.
Ordinary scalar extension also makes the planned derived-exactness detour unnecessary.

Edge cases checked in the statement review: empty source, zero module/rank, empty
strata, repeated filtration terms, identity and purely open/closed immersions, and
nonreduced scheme strata. No assertion of strictness, global lattice, or unjustified
scheme factorization is added.

## New nodes

`lem-sfb-condensed-locally-closed-scalar-extension`: proved compatibility of ordinary
scalar extension with the actual open-then-closed functor, by complementary support
detection and the closed counit; no derived coefficient-change assertion is used.

`lem-sfb-ordered-spectral-lattices`: the lattice and ordering portion only; statement
and proof preserve the actual monomorphism's scalar adjoint, with universe transport
and fibre-product refinement explicitly required.

`lem-sfb-internal-locally-closed-extension-composition`: an objectwise underived
comparison for the specified internal closure-factorization extension, obtained from
normalized sectionwise module coherence and coefficient-module equivalences.

`lem-sfb-locally-closed-ordered-filtration`: proved transport of the existing general
open-prefix filtration through exact extension, preserving the represented subobjects
and identifying their successor cokernels via the composition bridge.

Blueprint duplicate searches included `ordered lattice`, `extension composition`,
`filtration extension`, and `composition closed`; the relevant existing filtration and
coherence declarations were read. Neither states the new conclusion in these internal
coefficient categories. Mathlib searches of all three required kinds are recorded from
the actual msearch log in every new node.

Proof-context record: `coord/changes/R9-lattice-subquotient-proof-context.md`.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
