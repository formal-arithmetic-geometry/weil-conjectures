## What changed

Replaced the sorry of AlgebraicGeometry.Etale.exists_etaleCE_supported_first_page_lifts
with a complete Lean assembly from supported raw resolutions, coherent construction on
prescribed resolutions, and boundedBelow_secondFiltration. The original signature and
public import are unchanged. Added private proof imports of CartanEilenbergAllLowerBounds,
EtaleCECoherentPrescribedResolutions and BoundedBelowSecondFiltration.

CartanEilenbergAllLowerBounds constructs the raw resolutions, including all horizontal
resolution properties, using the existing prescribed-end horseshoe and row identifications.
Its two private helpers and public theorem are proved. Zero boundary and homology objects
receive their single-degree-zero resolutions; exactness forces zero middle resolutions.
The choices are independent of a lower bound, so one bicomplex works for every lower bound,
including every bound for the zero complex. No exported data definition or arbitrary
witness chosen into a definition was added.

A declaration-scoped unused-variable linter option preserves the original map-family binder
v, whose result type intentionally does not depend on v. The existing heartbeat setting is
unchanged. The initial lower-bound conversion through isStrictlyGE_iff timed out; using
isZero_of_isStrictlyGE compiles promptly without changing any dependency definition.

## Proved and sorry left

Closed: AlgebraicGeometry.Etale.exists_etaleCE_supported_first_page_lifts
(lem-weil-pbc-ce-supported-first-page-lifts). It is a decomposition, not a sorry-free
proof of the complete target closure: one upper hole is closed and one lower hole added.

Also proved: CategoryTheory.exists_cartanEilenberg_resolution_all_lower_bounds
(lem-weil-pbc-ce-resolution-all-lower-bounds), together with the private helpers
CategoryTheory.supported_object_rows and CategoryTheory.supported_rows.

Added and left: AlgebraicGeometry.Etale.exists_etaleCE_coherent_prescribed_resolutions
(lem-weil-pbc-ce-coherent-prescribed-resolutions), in its own module, with its entire
proof exactly `by sorry`. This only constructs coherent pages and comparisons on
already supplied CE resolutions; it proves neither existence of those resolutions nor
support preservation nor the final filtration equations. These omitted parts are proved
in the delivery, so this is not a restatement of the original theorem. No sorry remains
in the item or the raw-resolution module.

## No longer needed

No existing import was removed: the original public EtaleCEStationaryPageNaturality import
is required by the unchanged statement. Every added import is used.

The item's direct planned uses of lem-sp-cartan-eilenberg-exists
(Sheaf.CategoryTheory.CartanEilenbergExists) and
lem-weil-pbc-ce-coherent-first-page-lifts
(Sheaf.Paper.EtaleCECoherentFirstPageLifts) are replaced. Their objectwise arbitrary
choices do not give the needed simultaneous support preservation. No shift, least
nonzero degree, or separate zero-complex branch is needed. The raw theorem also avoids
CartanEilenbergObjectResolutionRows and CartanEilenbergRowsExists as black boxes because
it strengthens their zero choices directly. Their boundary projection, horseshoe and
row-identification tools remain used. These are prunings of this proof's direct route,
not claims that those modules are globally unreachable through other targets.

## Where the brief, the DAG or earlier work was wrong

The planned coherent-first-page theorem chooses its own resolutions; its signature
does not allow replacing them by the supported resolutions of step 1. The new
prescribed-resolution lemma exposes precisely that missing interface, without changing
an existing theorem. The original least-nonzero-degree plan is valid but unnecessary:
the existing alternating row construction can use intrinsic zero-object choices.
The second reader updated the item's explanatory docstring to the implemented
intrinsic-zero-choice route; the DAG proof records that same route. The unit's realized list is empty and
no unit statement or proof step was bypassed.

Read the source material through Stacks Tags 015I, 015J, 015K and 012K; the local literature
files are absent on this machine. The new generic row proof follows the two exact rows
of 015I using the prescribed-end horseshoe already in the library. The new coherent
statement is checked at zero complexes, empty schemes, and empty diagonals: its hypotheses
and quotient constructions cover these cases without requiring a nonzero term.

A newer decomposition of EtaleCECoherentFirstPageLifts exposed quotient descent and
CE-totalization modules in the source tree. The new totalization module was unavailable
in the compiled baseline, so the final delivery uses only the available compiled modules
and the two delivered modules; it does not copy that uncompiled dependency.

## New nodes

lem-weil-pbc-ce-resolution-all-lower-bounds:
lean/Sheaf/CategoryTheory/CartanEilenbergAllLowerBounds.lean. Generic raw CE existence
with preservation of every input support bound; fully proved from the prescribed-end
horseshoe, boundary projection and canonical row identifications. It is deliberately
independent of schemes, sections, pages and comparison maps.

lem-weil-pbc-ce-coherent-prescribed-resolutions:
lean/Sheaf/Paper/EtaleCECoherentPrescribedResolutions.lean. Constructs presentations,
quotient-page realizations and augmented filtered first-page comparisons on prescribed
raw resolutions. This is the one remaining new hole. No statement or definition was
changed and no forced adaptations or change records are needed.

## Second reading by N1

1. Compared the delivered item with the repository using diff and checked the entire
   existing theorem signature byte for byte: identical. Only proof imports, a
   declaration-scoped linter option, the explanatory proof docstring and the proof changed.
   The other two modules are new. No existing definition, statement or public import changed;
   no forced adaptation or change record is needed. Verdict: pass.
2. Compiled all three modules in dependency order through lcompile.py, without errors or
   warnings. The only textual sorry is the whole proof of
   AlgebraicGeometry.Etale.exists_etaleCE_coherent_prescribed_resolutions. There are no
   exported data definitions, hollow definitions, forbidden declarations or attributes.
   All choices in the delivered proofs are theorem-local; no definition selects arbitrary
   data from an unproved existence assertion. A scratch import probe printed axioms of all
   three public theorems: only propext, Classical.choice, Quot.sound and sorryAx.
   The raw-resolution theorem itself has no sorryAx dependency.
   The automatic delivery probe additionally checks every new constant. Verdict: pass,
   conditional on the reported lower hole and existing imported holes.
3. Read the complete prescribed-resolution statement and its proof docstring against
   EtaleTermwiseHypercohomology, HypercohomologyFirstPage and augmented CE comparison.
   Its hypotheses supply exactly the CE input conditions, and its conclusion omits both
   raw-resolution existence and the support-to-filtration equalities proved here. This is
   a strict intermediate part, not a renaming of the item. Checked zero complexes,
   single-degree complexes (including negative degree), empty schemes and empty diagonals:
   zero choices and finite quotient constructions still apply; no nonzero witness is needed.
   Re-read Stacks Tags 015I, 015J, 015K and 012K. Independently searched using leanfinder
   (filtered-bicomplex quotient functoriality), loogle (SpectralSequence map), msearch grep
   (prescribed resolutions and quotient-page descent), and rg on lean/Sheaf. Mathlib hits
   give homology or already-existing spectral-sequence maps, not this construction.
   The existing quotient-page descent and coherent-first-page theorems choose their own
   resolutions and cannot retain the supplied I; neither closes this hole in a few minutes.
   Verdict: the one split-off statement is true, sourced, necessary and strictly partial.
4. Read the proof from the item downward. The support proof follows from intrinsic zero
   endpoint resolutions, exactness of the two horseshoe rows, and the already stated
   row identifications; the final assembly uses boundedBelow_secondFiltration directly.
   All three added item imports are used. The old proof_deps no longer used are exactly
   lem-sp-cartan-eilenberg-exists and lem-weil-pbc-ce-coherent-first-page-lifts; both are
   recorded under No longer needed. The original public statement import stays necessary.
   dag/units/sk-prop-h2.json has no realized statement or step nodes, so no fixed unit
   realization is bypassed. Verdict: pass, a one-upper/one-lower-hole decomposition,
   not a net reduction of holes or a claim of global module unreachability.
5. Checked all three node records alongside the Lean. The existing node changes only
   stage-3-owned proof fields; each new node has its source, searches, creation/blueprint
   metadata, chapter/unit and matching Lean declaration and verbatim signature. The union
   of each proof's uses is exactly proof_deps. The raw node describes the two proved
   private reductions; the coherent node records the remaining natural-language argument;
   the item node matches the actual assembly and support transfer. Verdict: pass.

Second-reading repairs: made Mathlib.CategoryTheory.Preadditive.Injective.Resolution
an ordinary proof import of CartanEilenbergAllLowerBounds, exposing only Injective.Basic
for Injective and EnoughInjectives in its public signature. Updated the item's proof
explanation from the unused least-degree/shift route to the actual intrinsic zero-object
construction. No theorem statement or proof term changed; no additional holes were added.
