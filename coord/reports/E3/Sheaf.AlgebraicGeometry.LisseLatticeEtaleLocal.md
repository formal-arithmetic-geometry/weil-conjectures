## What changed

Return repair (2026-10-16): removed the duplicated `finiteLocallyFree_restrict` proof from
`IntegralLatticeCoefficientTransport`, together with its unused `coefficientUnitIso` helper.
The normalization module now exposes its already-proved `finiteLocallyFree_restrict` theorem
with the same type and proof. Pair transport imports normalization privately and uses this
single declaration. Its DAG proof dependency now records that reuse. The seven returned modules remain new to the current shared repository except the original
item; no other group's module is adapted. See `coord/changes/E3-lisse-lattice-shared-finite-freeness.md`.

`Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal` now proves the original statement by obtaining
its lattice-class sheaf, applying the existing local-classicality/etale-section theorem, and
transporting the resulting lattice pairs from slice sites to the members' small sites. Its
signature, universes, and coefficient comparison are unchanged.

`Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization` is fully proved. The lift
algebra equivalence preserves minimal polynomials and the spectral norm; it therefore gives
compatible isometric ring equivalences on the rational and integral coefficients. Composition
of continuous functions gives the coefficient sheaf isomorphisms. Restriction of scalars
preserves finite local freeness, proved by transporting the local generators and their free
presentations. The integral/rational coefficient square commutes sectionwise.

`Sheaf.AlgebraicGeometry.LisseLatticeClassSheaf` is proved from this normalization, the existing
`integralLatticeSheaf_locallyConstant`, and the new presentation-transport theorem. The coset
sets in the existing classification are nonempty, including in rank zero. No extra hypotheses
are imposed on the scheme or the rank.

`Sheaf.AlgebraicGeometry.LisseLatticeSliceTransport` is fully proved. It constructs the
canonical equivalence between the slice and the member's small pro-etale site, checks covers,
and transports finite local free generators. Scalar extension commutes with this functor by
objectwise tensor isomorphisms, checked on pure tensors, and by the canonical comparison
commuting sheafification with an equivalence. The resulting coefficient map is precisely the
one in the original item, by definitional equality.

`Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport` is now proved as well. Sections
inject into families of embedded submodules by the exact restriction criterion at the
identity. Shrinking them gives a sheaf in the required universe. The universe-lift functor
preserves sheafification, so the constant-coset descriptions descend. An explicit slice-site
equivalence commutes with constant sheaves. Finite free trivializations therefore give local
constancy, and their nonempty constant values give local sections through the sheafification
unit. Surjectivity of the presentation supplies a lattice representative for every section.

`Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport` is fully proved. Its tensor
isomorphism sends s tensor m to eS.inv(s) tensor m and is natural by the pure-tensor formulas.
Restriction along the coefficient map commutes with module sheafification. The integral
module remains finite locally free on the original cover; cancellation of the two rational
coefficient restrictions completes its rationalization.

The six original coefficient/restriction definitions were moved verbatim into
`Sheaf.AlgebraicGeometry.LisseLatticeCoefficients` and publicly reexported by the item to break
the import cycle. Their bodies, names, universes, and visibility are unchanged. The change
record is `coord/changes/E3-lisse-lattice-coefficient-relocation.md`. The repair also exposes existing helpers in the unclaimed
`ProEtaleWeaklyEtaleLocalization` module, as described below. The original unit route is retained.

Additional duplicate repair: both presentation and slice transport copied four theorems
and three concrete slice constructions from `ProEtaleWeaklyEtaleLocalization`. The existing,
unclaimed module now exposes those seven declarations; both transports privately import
and reuse them. Their duplicate blocks are removed. The localization node records the exposed
names, and both transport nodes record that dependency. See
`coord/changes/E3-lisse-lattice-shared-slice-api.md`. Existing public signatures and all
construction/proof bodies in localization are unchanged.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.ProEtale.exists_lisse_lattice_etale_local`.

The repair also exposes the already-proved
`AlgebraicGeometry.ProEtale.finiteLocallyFree_restrict` for reuse, without changing its proof.

Proved without additional holes:
`AlgebraicGeometry.ProEtale.lisse_coefficient_normalization`,
`AlgebraicGeometry.ProEtale.exists_lisse_lattice_class_sheaf`,
`AlgebraicGeometry.ProEtale.lisse_lattice_of_slice`,
`AlgebraicGeometry.ProEtale.small_lattice_sheaf_of_coset_presentation`, and
`AlgebraicGeometry.ProEtale.integral_lattice_pair_of_coefficient_iso`.

No holes were added. None of the delivered Lean files contains `sorry`. All intermediate
obligations developed in the sandbox were proved in this session, including normalization,
shrinking and local constancy, coefficient transport of a pair, and slice transport.
The existing lattice-class and local-classicality results remain dependencies; their
upstream proof obligations are not changed by this delivery. The current repository has
already proved `isSheaf_latticeCoefficientPresheaf`. This closes one hole in the target
import closure with zero added holes; it is no longer a decomposition into unfinished obligations.

Validation: all eight sandbox modules compile together in import order. Empty covering index
sets and zero-rank free modules are permitted throughout. No representative or arbitrary data
is chosen in a definition from an unproved existence theorem; choices of representatives are
confined to theorem proofs. The coefficient definitions are byte-for-byte identical to the
original definitions (checked by the report-generation script).

## No longer needed

Removed the copied `weaklyEtale_slice`, `sliceTo`, `sliceFrom`, `sliceEquiv`,
`sliceFrom_cover`, `sliceFrom_cocont`, and `sliceDense` blocks from both transport modules.
The earlier provisional removal of the localization proof import is superseded: both modules
now import and reuse that module's concrete API. No complete module is pruned.

The pair-transport module no longer needs its duplicate private `finiteLocallyFree_restrict`
or its private `coefficientUnitIso` construction. Normalization retains the single finite
local freeness proof and its unit-isomorphism construction; no whole module is pruned.

Removed provisional `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree` proof imports
from the normalization, pair-transport, and slice-transport modules. Their proofs construct
the required unit-module identifications directly and use the existing generator-map API.

Removed the now-unused `Mathlib.CategoryTheory.Sites.CoverLifting` proof import from the
normalization module after simplifying its finite-freeness proof to keep the original cover.

Removed the redundant public coefficient-module import from the generic
presentation-transport module: its statement and proof use arbitrary coefficient sheaves.

Removed the item's direct proof import `Sheaf.Paper.LatticeSheafLocallyConstant`; it remains
needed by the class-sheaf and slice-transport proofs and is not globally pruned.

The item's seven direct public imports are now redundant through its public coefficient
module: `Sheaf.NumberTheory.Padics.CoefficientExtension`,
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, `Sheaf.CategoryTheory.RingedSiteModules`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`WeilConjectures.CategoryTheory.RingObjects.ContinuousMap`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`. They still support the
unchanged public interface and are not globally pruned.

No existing node or complete module is made unreachable by the proof.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated an identical private finite local freeness theorem in two
new modules. The earlier second reading missed this duplication. This repair exposes and
reuses the normalization theorem rather than proving the fact twice. The prior second-reading
section below describes the pre-repair delivery and requires a fresh independent check.

The informal mathematical route is correct. The extraction from a slice is not a direct
Lean application: the conclusion lives on a different small site and uses a specified
coefficient map and sheafified tensor product. The explicit transport proof supplies this.

The existing classification uses `E : Type u`, `WithAbs` coefficients, and sections in
`Type (u + 2)`. The item uses `E : Type`, spectral-norm coefficients, and its local-classicality
theorem requires sections in `Type (u + 1)`. The coefficient comparison, shrinking, local
constancy, and coefficient transport of representatives are now proved. The classification
module is held by F2; no unforced change to it was made.

## New nodes

No further node is added by the repair. The existing
`lem-weil-proetale-weakly-etale-localization` node gains the exposed helper names in its Lean
record. Both transport nodes record this reused dependency. The additional change record is
`coord/changes/E3-lisse-lattice-shared-slice-api.md`.

`def-weil-pbc-lisse-lattice-coefficients` records the relocation of the six original concrete
coefficient/restriction definitions, with no new choice or hole.

`lem-weil-pbc-lisse-lattice-coefficient-normalization` records the proved isometric coefficient
comparison and finite local freeness of the restricted module.

`lem-weil-pbc-lisse-lattice-class-sheaf` records the proved application of normalization and
the existing classification, followed by presentation transport.

`lem-weil-pbc-lisse-lattice-presentation-transport` records the proved shrinking and local
properties of the presentation, using transport of a single pair only at its final step.

`lem-weil-pbc-integral-lattice-coefficient-transport` records the proved transport of one
integral lattice pair along a commuting coefficient square, including rationalization.

`lem-weil-pbc-lisse-lattice-slice-transport` records the proved passage from a lattice pair on
the slice to a lattice on an etale cover member's small site, including scalar extension.

The item's node changes only `proof`, `proof_deps`, `proof_origin`, and `lean` (reattaching the
six moved definitions to the new coefficient node). The change records are
`coord/changes/E3-lisse-lattice-coefficient-relocation.md` and
`coord/changes/E3-lisse-lattice-shared-finite-freeness.md`.

## Earlier second reading (a previous round; superseded)

1. **Existing interfaces: pass.** I compared every delivered module with the read-only
repository. Only the original item existed there. A direct text comparison confirms that
`exists_lisse_lattice_etale_local`, through its final coefficient-action conclusion, has the
identical signature. A second text comparison confirms all six moved definitions, from
`lisseContinuousCommRingSheaf` through `lisseEtaleCoefficientIdentification`, are byte-for-byte
identical. The new coefficient module publicly reexports all seven former public imports, so
the original public interface remains available. The relocation has its change record and
requires no adaptation of another group's module.

2. **Compilation, axioms, and data: pass.** I compiled all seven files in import order with
`lcompile.py --all`; each compiled without warnings or errors (3.0--28.6 seconds per file).
I then compiled scratch probes printing axioms for all twelve public declarations. The six
coefficient definitions and the slice, presentation, and pair-transport theorems use only
`propext`, `Classical.choice`, and `Quot.sound`. Normalization, class-sheaf construction, and
the item additionally use `sorryAx` from existing open dependencies. A further probe of the
normalization helpers located its dependency in the existing
`isSheaf_latticeCoefficientPresheaf`, used to package the explicit continuous-function
presheaf as a sheaf; its norm and integer-ring calculations and finite-freeness transport
have only the three standard axioms. No delivered source has a hole or prohibited declaration.
The new data definitions construct ring equivalences, functors, and tensor maps explicitly.
Class representatives are chosen only in theorem proofs; the old coefficient integer ring
is characterized uniquely by absolute value at most one.

3. **Intermediate results and edge cases: pass.** There are five new proved intermediate
results and no split-off open statement. I checked the source's Proposition 6.8.4(6) in the
local Bhatt--Scholze text: its route is the coset-class sheaf, local classicality, and an etale
cover with sections. Normalization uses `minpoly.algEquiv_eq` and the valuation-ring membership
characterization to identify the two coefficient presentations. Pair transport uses the
commuting coefficient square in the balancing relation of `s tensor m ↦ eS.inv(s) tensor m`.
Presentation transport proves smallness by the exact restriction criterion at the identity,
then descends constant descriptions using fully faithful universe lift and sheafification.
Class-sheaf construction applies the existing classification to the normalized module and
uses the inhabited coset quotient. Slice transport constructs inverse site functors, preserves
covers, and compares the sheafified tensor products, retaining the specified identity
coefficient map. These are strict parts of the argument, rather than renamed copies of the
item. Finite bases may be empty, the identity coset exists for rank zero, and the covering
index sets may be empty; no proof chooses a point of X or assumes a positive rank.

I searched the project and Mathlib using restriction-of-scalars, shrinking, and pushforward
terminology, and ran additional LeanFinder, Loogle, and grep searches through `msearch.py`
(recorded in `searches.jsonl`). LeanFinder returned generic restriction/scalar and free-module
APIs already compatible with this proof; Loogle could not resolve the project-specific
finite-local-freeness name. No existing theorem supplies the full transport statements.

4. **Route, imports, and pruning: pass.** The item first obtains the small class sheaf, uses
clauses `.2.1` and `.2.2` of `proEtale_locallyClassical_etaleCover`, obtains a pair for each
section, and applies slice transport. This is the source's route. I read
`dag/units/sk-thm-properbasechange.json`: none of its realized statement or step nodes is
bypassed or modified. Each public import of a new proof module supports names or instances
in its statement; proof-specific imports are plain imports. The seven public imports moved
with the coefficient definitions retain the item's previous public interface. The old direct
proof dependency `lem-weil-pbc-lattice-sheaf-locally-constant` remains needed transitively by
class-sheaf construction, normalization, and slice transport; no complete module is pruned.
The earlier worker's provisional import removals are documented above; I made no further
Lean import change.

5. **Nodes: pass.** I matched each new node's hypotheses and conclusions to its Lean theorem,
including the distinct universes of F and F0, the commuting coefficient square, and the
sheafified rationalization. Every new node has its source, three recorded search kinds,
creation data, blueprint ancestry, and matching Lean record. For the existing item, a JSON
comparison confirms changes only in `proof`, `proof_deps`, `proof_origin`, and `lean`. The new
proof dependencies are class-sheaf construction, local classicality, and slice transport,
exactly those used by the final proof. The unit realization is unchanged.

Second-reading changes: added this review and clarified the list of existing open dependencies
in `## Proved and sorry left` after the axiom probes. No Lean code or DAG content needed repair.

## Second reading by E3

1. **Existing statements and definitions: pass.** I compared both existing modules with
   the current read-only repository. A direct substring comparison verifies that the item's
   full theorem signature and all six relocated definition/docstring blocks are byte for
   byte identical. Localization changes only seven private declarations to public ones and
   supplies their documentation; all bodies and existing public signatures are unchanged.
   The three change records declare the relocation and the shared APIs. No other module
   held by another group is edited.

2. **Proofs, compilation, axioms, and data: pass.** I independently compiled all eight
   modules in import order with `lcompile.py --all`: no warnings or errors, 2.8--25.5 seconds
   per file. A new scratch axiom probe checks the six coefficients, six public theorems,
   seven exposed slice helpers, and the existing coefficient sheaf-condition theorem.
   All use only `propext`, `Classical.choice`, and `Quot.sound`, except the class-sheaf
   theorem and the item, which retain `sorryAx` from upstream obligations. In particular,
   normalization now has no `sorryAx`: the coefficient sheaf-condition theorem has since
   been proved upstream. No delivered file contains a hole or a prohibited declaration.
   The shared finite-freeness proof and concrete slice constructions are reused. Data in
   definitions are constructed explicitly or transported by isomorphisms; representatives
   chosen from the class presentation occur only within theorem proofs. The existing
   valuation ring is determined by its membership characterization, not arbitrary existence.

3. **Intermediate statements and edge cases: pass.** There are no split-off open theorems.
   I read every new module and the local source text of Proposition 6.8.4(6). The intermediate
   theorems separate coefficient normalization, transport of one pair, shrinking and local
   constant presentations, construction of the class sheaf, and slice transport. Each is a
   proper part of the argument, not a renamed copy of the item. The tensor balancing equation
   uses the commuting coefficient square; smallness uses the presentation's exact restriction
   criterion at the identity. Empty finite bases and empty covers are admitted, and the coset
   quotient has the identity class even in rank zero. Additional searches with LeanFinder,
   Loogle, `msearch.py grep`, and direct project/Mathlib searches found generator-map,
   restriction-of-scalars, and pushforward APIs, but no existing theorem giving these full
   transports. The returned APIs are already the ingredients the proofs use.

4. **Route, imports, and pruning: pass.** The item's proof follows the source's lattice-class
   sheaf, local classicality, etale-local sections, and representative lattice route. I checked
   the unit's `realized` statement and three steps: none is bypassed or changed. Public
   imports support the statements, instances, or the preserved coefficient-module interface;
   proof-specific imports are plain imports. The old lattice-class dependency remains used
   through the new modules, so no complete module is pruned. I removed the stale report
   paragraph claiming slice transport no longer imports localization; both transport modules
   now reuse its API as required by the returned duplicate repair.

5. **DAG agreement: pass.** I compared the JSON records with the current repository: the
   existing item changes only `proof`, `proof_deps`, `proof_origin`, and `lean`; localization
   changes `lean` and removes the obsolete word "private" from its proof description. Every new record has the required fields, source, search records,
   blueprint ancestry, and Lean attachment. Recorded theorem statements match their Lean
   signatures after whitespace normalization. For every delivered node the union of proof
   steps' `uses` equals `proof_deps`. The new normalization dependency in pair transport
   records `finiteLocallyFree_restrict`; the two site transports record localization.

Second-reading changes: corrected the stale localization-import paragraph and the claim
that the coefficient sheaf-condition theorem remains open, and appended this independent
review. I also corrected two DAG proof descriptions: normalization transports local generators
directly without an extra double-restriction step, and the exposed localization functors
are no longer private. No Lean proof repair was needed. Closed one original hole, added zero holes;
no additional split-off obligations or complete modules pruned.
