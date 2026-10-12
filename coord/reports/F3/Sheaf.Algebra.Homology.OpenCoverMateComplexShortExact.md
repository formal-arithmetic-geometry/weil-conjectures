## What changed

Proved `SheafOfModules.open_cover_mate_complex_shortExact` from the strictly smaller
single-module-sheaf exactness theorem `open_cover_mate_module_shortExact` in the new
module `Sheaf.Algebra.Homology.OpenCoverMateModuleShortExact`.

The original module now explicitly constructs the natural nested mates and their
complex maps. Adjunction naturality, restriction-comparison naturality and the
triangle identities prove both counit compatibility identities. Their difference
lift satisfies the two required component formulas and has zero composite with
the counit sum. No hole is used for this construction or zero-composite proof.

The remaining theorem concerns only one module sheaf, with the maps fixed by the
mate formulas and the zero-composite proof supplied by the caller. Apply it to
each degree. Evaluation's biproduct comparison gives short-complex isomorphisms,
and `HomologicalComplex.shortExact_of_degreewise_shortExact` proves the result.

The original public imports, statement and docstring are preserved. Only proof
imports changed. No existing dependency was adapted.

## Proved and sorry left

Closed the original hole in
`SheafOfModules.open_cover_mate_complex_shortExact`
(node `lem-sc-open-cover-mate-complex-short-exact`). All its private helpers are
proved; its proof contains no `sorry`.

Added exactly one hole in
`SheafOfModules.open_cover_mate_module_shortExact`
(node `lem-sc-open-cover-mate-module-short-exact`). Its proof is exactly `by sorry`;
its docstring gives the source and complete argument. This is a decomposition,
not a net hole reduction: one original hole closed and one lower hole added.
The lower statement requires no cochain complex, constructs no complex maps,
and does not assert exactness for arbitrary morphisms.

Both delivered files compile through `lcompile.py`. Empty space, empty opens,
equal opens and the zero module are included: the same stalk cases apply and
there are no inside points for an empty open. No definition contains a hole,
and no arbitrary existence witness is selected as data in a definition.
The complex maps are constructed explicitly from units, comparisons and inverse
Hom equivalences.

## No longer needed

Removed the direct proof import `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`
from the original module. Exactness of the chosen functors is not needed to
construct the complex maps or prove their counit identities. The lower
single-sheaf exactness argument still uses the canonical extension adjunction
and stalk theory, so no global pruning of those mathematical nodes is claimed.

The old direct proof dependencies removed from the upper node are
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-sc-module-extension-by-zero-stalk-maps`, and
`lem-weil-pbc-module-stalk-exact`. They remain mathematical dependencies of the
new lower node; their modules are not globally pruned.

The original node now depends directly on the single-sheaf exactness node rather
than carrying all three of its lower dependencies directly. No fixed unit step
is bypassed (`dag/units/sk-thm-picard-duality.json` has empty realized lists).

Discarded both unlanded earlier-attempt split declarations and their stale nodes,
`new-open-cover-mate-components` and `new-open-cover-mate-exact`. They are replaced
by proved categorical construction/zero-composite glue and the strictly smaller
single-sheaf exactness step. They were sandbox artifacts, not base declarations.

## Where the brief, the DAG or earlier work was wrong

The earlier exactness node still recorded `h1 : True` and `h2 : True`, claiming
short exactness for arbitrary morphisms. This is false. Both previous sandbox
splits were removed. The current lower statement fixes the actual prescribed
maps, and the upper theorem proves their zero-composite relation without a hole.

The earlier timeout was not an obstruction. Explicit reduction of the mapped
complex objects resolves the type conversion. The resulting complex theorem
compiles comfortably within 60 seconds without any definition/signature change.

The module-level theorem was also fully proved locally using
`open_extension_mayer_vietoris_shortExact`, the extension stalk-map theorem and
`module_stalk_exact`, but the dry run correctly rejected its imports as cyclic:

`OpenCoverMateComplexShortExact → OpenCoverMateModuleShortExact →
ModuleExtensionByZeroStalkMaps → ModuleExtensionByZeroStalkInside →
ModuleExtensionByZeroStalkMorphism → ModuleRestrictionStalkLinear →
DerivedHomMayerVietoris → OpenHomTriangleRealization →
OpenCoverAdjunctionTriangle → OpenCoverMateComplexShortExact`.

The canonical Mayer--Vietoris, open-restriction and stalk-exactness modules also
import `DerivedHomMayerVietoris` for its basic `moduleRings` abbreviation. That
module now imports the upper result. The node plan overlooks this layering
problem. Importing these existing declarations would close the cycle, so they
are not imported in the delivered lower module. Moving the basic module-ring
interface to a lower module requires an interface refactor outside this item's
ownership; no unforced adaptation is delivered. The complete local proof is
retained for the reader in `scratchpad/ModuleProofWithCyclicImports.lean` in the
sandbox, excluded from delivery. The remaining named hole isolates exactly this
single-sheaf step and its source proof, rather than restating the complex theorem.

## New nodes

`lem-sc-open-cover-mate-module-short-exact` records the single-module-sheaf
short exactness step, with one named `sorry` and a complete source proof. Its Lean
statement is recorded verbatim, including the prescribed maps and supplied
zero-composite proof. Its source follows the original extension-by-zero/stalkwise
route. There are no change records and no forced adaptations.

## Second reading by F3

1. Compared the full delivered upper module with the repository using `diff` and
   the delivery declaration parser. Its existing public theorem signature and
   docstring are byte-for-byte unchanged; no existing definitions or public
   imports changed. The new helpers are private. Verdict: pass.
2. Compiled both delivered modules in import order with `lcompile.py`: no errors
   or warnings. Reviewed the explicit mate natural transformation, counit
   calculation, zero composite, and evaluation/biproduct transport. The only
   delivered hole is `SheafOfModules.open_cover_mate_module_shortExact`; no data
   definition uses a hole or an arbitrary existence witness. Scratch copies with
   `#print axioms` checked both public theorems and every private helper: the
   helpers use only `propext`, `Classical.choice`, `Quot.sound`; the two public
   theorems additionally use `sorryAx`, as expected from the named lower hole. Verdict:
   the upper proof is a valid reduction, with the lower exactness hole retained.
3. Read the lower signature, docstring and matching node, and checked stalk cases:
   both opens give the difference diagonal and addition; exactly one gives the
   identity with zero source; the cover excludes neither. Empty space, empty
   opens, coinciding opens and zero modules cause no exception. The displayed
   maps are fixed, and `hz` merely supplies the short-complex proof field. This
   is strictly smaller than constructing natural complex maps and proving complex
   exactness, not a renamed restatement. Independent leanfinder, loogle, grep and
   repository searches found the existing canonical Mayer--Vietoris and stalk
   results, but importing them here would close the verified dependency cycle.
   Closing the lower hole requires repairing that library layering or a separate
   stalk proof, beyond a few-minute review repair. Verdict: pass as decomposition.
4. Checked all imports: public imports support signatures/instances; the new
   lower theorem and degreewise exactness lemma are proof-only imports. The upper
   construction uses standard adjunction and biproduct identities. All three old
   proof dependencies are now listed explicitly above as removed direct edges,
   without claiming global pruning. The unit has empty `realized` lists and its
   route is preserved. Verdict: pass.
5. Compared the existing node's changed fields with the Lean proof: only `proof`,
   `proof_deps`, and `proof_origin` changed. The new node's Lean statement matches
   its theorem verbatim and its fields describe the single-sheaf source argument.
   No change records or forced adaptations are needed. Verdict: pass.

Changed only review documentation and the new lower theorem's source/proof
annotation: Tag 08BW is a derived Hom Mayer--Vietoris result, not a statement of
nested restriction maps. The directly relevant extension-by-zero adjunction and
stalk calculation is [Stacks Tag 00A7](https://stacks.math.columbia.edu/tag/00A7),
as used by [Tag 08BU](https://stacks.math.columbia.edu/tag/08BU). Corrected the new
node's source place accordingly, added the elementary kernel/surjectivity check
in its docstring, and recorded independent searches. Existing docstrings and
proofs were preserved. Net hole reduction remains zero: one upper hole closed,
one strictly lower hole added.
