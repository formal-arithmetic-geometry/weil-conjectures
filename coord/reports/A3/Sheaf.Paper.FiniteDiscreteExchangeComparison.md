## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_comparison`
by constructing the finite discrete coefficient realization, its fullness and triangulated
properties, the single complex compatibility, and the three step arrow comparison. Added
six supporting modules and their DAG nodes, together with the required import-change record.
The target theorem signature is unchanged.

## Proved and sorry left

Closed the original hole `finiteDiscreteExchange_comparison`.
The delivery leaves one named lower theorem as a deliberate decomposition:
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_coefficientRealization`
(node `lem-weil-pbc-finite-discrete-coefficient-realization`). Its proof is left as the whole
proof `:= by sorry`; it is the coefficient transport and adjunction-coherence part of the
argument. All other declarations added in this delivery compile without local `sorry`.
This closes one original hole and adds one lower hole: a decomposition with net zero
local holes, not a completed proof of the target import closure. Existing upstream
`sorryAx` dependencies, including comparison injective acyclicity, remain.

## No longer needed

The old parent proof dependencies no longer used directly are
`lem-weil-pbc-constant-internal-module-sheaf-equivalence`,
`lem-weil-pbc-finite-ring-constructible-derived-origin`, and
`prop-weil-pbc-site-comparison-finite-level`. The first remains a planned input to
`lem-weil-pbc-finite-discrete-coefficient-realization`; its module is privately imported there. The sheaf-origin theorem remains a planned
mathematical input to the lower hole; its recorded module cannot be imported with
this item's upstream API (see the second reading below).
The separate derived-origin lemma is replaced by the proved bounded triangulated
devissage. The source library's derived comparison supplies fullness.

Removed direct parent imports:
`Sheaf.Paper.ConstantInternalModuleSheafEquivalence`,
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`, and the redundant public
`WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`.
The last remains publicly available through retained imports. See
`coord/changes/FiniteDiscreteExchangeComparisonImports.md`.
No claim of whole-library module pruning is made: alternate import paths may retain
these modules, and the maintainer's pinned sorry ledger determines the actual count.

## Where the brief, the DAG or earlier work was wrong

The direct finite-ring derived-origin route was too fine for this module: bounded origin follows
from the proved underived single-complex interface, fullness, and bounded triangulated devissage.
The finite-level comparison conjunction alone does not encode the three actual exchange-step
coherence equations, so the proof uses an explicit three-step comparison record. The remaining
coefficient realization theorem is strictly below the parent: it supplies equivalences and the
three step comparisons, while the parent genuinely assembles the final arrow isomorphism.

## New nodes

`lem-weil-pbc-finite-discrete-condensed-ring-constant` — constant continuous functions equal the
sheafified constant finite ring (`Sheaf.Paper.FiniteDiscreteCondensedRing`).

`lem-weil-pbc-finite-discrete-scheme-ring-constant` — the monoidal constant ring comparison after
pullback to a scheme (`Sheaf.Paper.FiniteDiscreteSchemeRing`).

`lem-weil-pbc-finite-discrete-etale-realization-full` — fullness of bounded-below etale realization
(`Sheaf.Paper.FiniteDiscreteEtaleRealizationFull`).

`lem-weil-pbc-finite-discrete-single-realization` — compatibility for single complexes
(`Sheaf.Paper.FiniteDiscreteRealizationFunctor`).

`lem-weil-pbc-three-step-arrow-comparison` — composition of three commuting arrow squares
(`Sheaf.Paper.FiniteDiscreteRealizationFunctor`).

`lem-weil-pbc-finite-discrete-exchange-step-realization` — realization functors and exchange-step
comparison interface (`Sheaf.Paper.FiniteDiscreteExchangeRealization`).

`lem-weil-pbc-finite-discrete-coefficient-realization` — the residual coefficient transport
obligation (`Sheaf.Paper.FiniteDiscreteCoefficientExchange`).

## Second reading by A3

1. **Interfaces — pass.** Compared every delivered Lean path with the read-only
   repository. Only the item already exists; the other six modules are new.
   The existing theorem signature and all its section variables are byte for byte
   unchanged. The only public-import removal is redundant, with its change record.
   No existing definition or downstream module was changed.

2. **Proof and data — pass as a decomposition.** All seven modules compiled using
   `lcompile.py --all`; individual scratch copies also check the recorded declarations
   with `#print axioms`. The final delivery tool probes every declaration. There is
   exactly one local `sorry`, the entire proof of the named coefficient-realization
   theorem. No definition contains a hole or selects arbitrary data from an unproved
   existence statement. The realization takes a given equivalence as an argument;
   equivalences extracted from the residual theorem are used only inside proofs of
   propositions. The parent genuinely proves bounded essential-image devissage,
   constructibility transport, and arrow transport by naturality.

3. **Residual statement — pass.** The remaining theorem asserts underived constructible
   sheaf origin and comparison of the three specified exchange factors for a concrete
   derived realization. It assumes neither derived origin of the arbitrary input N
   nor the assembled arrow isomorphism of the parent. Thus it is a proper lower
   obligation, although substantial. Checked empty schemes, empty strata, zero modules,
   and the zero ring; no nonzero, proper, or Cartesian condition is silently required.
   Finite presentation gives a finite matrix; after simultaneously making its entries
   constant, the cokernel is a finite B-module. For the coefficient encodings one must
   use the sectionwise construction and its canonical ring normalization, rather than
   assume arbitrary supplied equivalences or ring isomorphisms are coherent. The
   existential conclusion permits this canonical choice. Repeated LeanFinder, Loogle,
   and grep searches with different terms; generic SheafOfModules APIs and the existing
   constant-coefficient exchange comparison do not prove this internal-module statement.
   The latter additionally assumes an IsPullback square, whereas this item only has
   CommSq. No quick closure of the residual theorem was found.

4. **Route and pruning — pass with corrected accounting.** Read the unit's `realized`
   statement and all three steps. This item is below those nodes; no prescribed unit
   step is bypassed. Used the existing `DerivedCategory.prop_of_bounded` and source
   derived comparison, rather than another derived-origin hole. Corrected
   `No longer needed` to enumerate all three old proof-dependency node ids and the
   actual removed imports. In particular the old dependency is derived origin, not
   sheaf origin. No whole-library pruning count is asserted.

5. **Nodes — pass with repaired dependency record.** Verified every new node's
   declaration and verbatim Lean statement, source, creation fields, chapter, unit,
   blueprint ancestry, and that proof_deps is the union of proof-step uses. The
   parent node records the bounded devissage and three-square assembly actually used.
   The residual node incorrectly treated the deep direct-image comparison as
   elementary: changed that step to cite `prop-weil-pbc-comparison-direct-image`
   explicitly. Its canonical mate normalization is still part of the remaining proof.

Changes by this reader: added the missing private import of
`Sheaf.Paper.ConstantInternalModuleSheafEquivalence` to the residual module, corrected
its DAG dependency classification, and repaired the report's dependency and net-hole
accounting. No proof body or statement was changed.

Import limitation reported for the maintainer: attempted to import both recorded
planned inputs `Sheaf.Paper.FiniteRingConstructibleSheafOrigin` and
`Sheaf.AlgebraicGeometry.ComparisonDirectImage` into the residual module. Lean rejected
the combined imports with
`import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs failed, environment
already contains 'AlgebraicGeometry.ProEtale.«term(_)_*[_]»' from
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
Removed those incompatible imports; retained the compatible encoding import. The
lower node keeps its mathematical source dependencies, and the original upstream
`WeilConjectures.SixFunctors.ProEtale.Comparison` API, available through the realization
fullness input, supplies the canonical direct-image comparison. A future proof of the
remaining hole must use compatible presentations or have the maintainer reconcile the
recorded module imports. This delivery changes no shared import API to bypass the conflict.
