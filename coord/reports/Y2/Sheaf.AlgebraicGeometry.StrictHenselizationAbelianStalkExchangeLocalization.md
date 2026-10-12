## What changed

Replaced the original theorem's sorry by a complete Lean proof from two strictly smaller
intermediate theorems. The proof constructs the induced map X₁ → X', proves its square
cartesian by pasting and cancellation, applies the canonical cube comparison maps, and
transports their commutativity to the residue-field closed stalk using naturality.
The original signature and all public imports are unchanged.

Three new modules expose actual comparison constructions:
- GeometricPointFieldExtension: precomposition of geometric points, with a complete proof
  that field enlargement induces an isomorphism of abelian stalks.
- AbelianExchangeCubeComparisons: actual derived source/target restriction composites and
  actual derived homology stalk comparisons; the generic commuting-cube equation is split off.
- StrictHenselizationExchangeCubeStalkIsos: invertibility of these two fixed restriction maps,
  without an exchange-compatibility assertion.

The generic cube statement needs only commuting squares, so it is independent of strict
henselizations, locality, qcqs, and torsion. The invertibility statement has no assertion
that exchange is invertible and no assertion that the exchange square commutes. Neither
is the original theorem under a new name. No data is chosen from an existence theorem
with unproved existence: every comparison map is explicitly constructed from the existing
functor maps, isomorphisms, and equality transports. `asIso` uses uniqueness of an inverse.

## Proved and sorry left

Closed: AlgebraicGeometry.Etale.exists_addEquiv_strictHenselization_abelian_stalkExchange
(1 of 1 original holes). This is a decomposition, not an unconditional proof of localization.
One hole closed and two added gives a delivery-local net of -1; the pinned closure ledger
and whole-library pruning figures remain the maintainer's measurements.

Also proved: AlgebraicGeometry.Scheme.isIso_pointSmallEtalePrecomp_sheafFiber, including
bijectivity on pointed lifts. Faithfully flat field-spectrum maps give injectivity;
étale lifting over the separably closed smaller field gives an open section, through
which the enlarged-field lift factors. The induced isomorphism of points gives the stalk iso.

Two holes added, each exactly `:= by sorry` in a public theorem:
- AlgebraicGeometry.Etale.exchangeCube_stalk_square,
  lem-weil-pbc-abelian-exchange-cube-comparisons.
- AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_stalkComparisons,
  lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos.

No sorry remains in the original module. The new definitions contain none.

## No longer needed

Removed the original proof imports:
- Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
- Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
- Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
- Sheaf.Paper.InverseImageStalkGerm
- Sheaf.Paper.StrictHenselizationFunctoriality

The first, second and fourth still occur in the intermediates' plans, so they are
not globally pruned. The functoriality module is no longer needed on this branch.
All old proof dependencies absent from the localization node's new `proof_deps`
are: def-weil-pbc-derived-inverse-image, lem-weil-pbc-derived-exchange-termwise,
lem-weil-pbc-inverse-image-stalk-germ, lem-weil-pbc-strict-henselization-functoriality,
lem-weil-pbc-strictly-henselian-sections-stalk, and
lem-weil-pbc-unrestricted-strict-henselization-stalk (six nodes; the cartesian-square
dependency remains). The termwise exchange route is replaced by horizontal
mate pasting: lem-weil-pbc-derived-exchange-termwise and its module
Sheaf.AlgebraicGeometry.DerivedExchangeTermwise are no longer needed on this branch.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original four proof steps did not expose a canonical comparison whose exchange
compatibility could be combined with the two isomorphisms: arbitrary choices of additive
equivalences do not suffice. The new maps fix this explicitly. The generic cube equation
can use the library's proved horizontal pasting law instead of introducing K-injective
resolutions and proving equality of pointed lifts again.

The local Stacks source file is absent from this clone. Read the corresponding online
Stacks texts for 03Q9, 03QO, 095T and 03PN; the source already named these texts. The
field-extension result is precisely the stalk-functor isomorphism in 03PN Remark 59.29.8.
LeanSearch was unavailable (HTTP 500), recorded as unavailable rather than no match;
LeanFinder, Loogle and source grep ran successfully, with their records in searches.jsonl.

Edge cases checked mathematically: zero sheaf, q = 0, empty total spaces, inseparable
extensions of separably closed fields, arbitrary nonstandard pullback models. The generic
cube maps do not require cartesianness. The strict-local statement retains qcqs for the
03Q9 application and the locality/residue equations for identifying the closed points.

## New nodes

lem-weil-pbc-geometric-point-field-extension: proved natural stalk isomorphism induced by
precomposition. Module Sheaf.AlgebraicGeometry.GeometricPointFieldExtension.

lem-weil-pbc-abelian-exchange-cube-comparisons: compatibility equation for the explicit
restriction composites in any commuting cube. Module
Sheaf.AlgebraicGeometry.AbelianExchangeCubeComparisons.

lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos: invertibility of these fixed
comparison maps for compatible strict-local bases. Module
Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos.

No statement changes and no change records.

## Second reading by Y2

1. Compared the delivered localization module with the repository version. The target
   declaration is byte-for-byte unchanged; only proof text and proof-only imports changed.
   Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py --all`. They compile without
   errors, and the only remaining `sorry`s are the two named public split theorems in the
   new comparison modules. No definitions contain `sorry`, and no forbidden declarations
   were introduced. Independent `#print axioms` checks on all eight declarations show
   only propext, Classical.choice, and Quot.sound for the constructions and the field
   extension proof; the localization and two split theorems additionally use sorryAx,
   as expected for this decomposition. Verdict: pass.
3. Read the two split-off statements and their nodes. The cube-square theorem asserts only
   compatibility, while the strict-local theorem asserts only invertibility of the two
   explicit comparison maps; neither restates the localization theorem. The field-extension
   theorem is fully proved. Verdict: pass; the decomposition is mathematically proper.
4. Checked the proof route against the available derived pasting, stalk, and strict-local
   declarations and searched the library and Mathlib for shorter existing results. The
   explicit comparison maps are used, and the old termwise-exchange route is pruned. Verdict:
   pass; no shorter applicable route was found.
5. Checked the node `proof`, `proof_deps`, `proof_origin`, and the `sk-thm-p1` realized route
   against the Lean declarations. The unit route remains represented by the localization
   theorem and its comparison steps. Verdict: pass.

Second-reading repairs: added proof-only imports for the named horizontal-pasting and
inverse-image-germ dependencies of the cube lemma; replaced the unused functoriality
import of the invertibility lemma by the field-extension module its plan actually uses;
completed the old-dependency pruning list. No signatures or definitions changed.
Independently checked zero coefficients, degree zero, empty total spaces, field
extensions without algebraicity, and arbitrary pullback models. Compatibility follows
from two horizontal pastings of the same outer square; invertibility follows from the
canonical restriction in [03Q9](https://stacks.math.columbia.edu/tag/03Q9) and exact closed
germs in [03QO](https://stacks.math.columbia.edu/tag/03QO). The proved field-enlargement
argument agrees with [03PN](https://stacks.math.columbia.edu/tag/03PN).
