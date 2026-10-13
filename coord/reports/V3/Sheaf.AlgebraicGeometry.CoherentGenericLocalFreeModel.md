## What changed

Completed `AlgebraicGeometry.Scheme.Modules.coherent_generic_local_free_model`
in `Sheaf.AlgebraicGeometry.CoherentGenericLocalFreeModel`, preserving its entire
signature, all public imports. The second reader updated the docstring to the implemented route. Added proof-only imports
and fully proved private helpers for affine section transport, basic-open localization,
coherence of a finite free closed pushforward, extension and shrinking of a coherent
stalk isomorphism, and the linear closed-pushforward stalk comparison.

The final proof constructs a vector-space structure on the actual stalk of F over
O_Z at its generic point: the closed-immersion stalk map is surjective with maximal
ideal kernel, which hkill annihilates. Mathlib's quotient module action and ring
quotient equivalence construct the action, and an identity semilinear map proves
finite generation over the field. A finite basis identifies this stalk with the
finite free source stalk. The closed-pushforward comparison gives an ambient stalk
isomorphism. Proved finite-free pushforward coherence permits extension and shrinking
on X. Nested restrictions are converted to an ambient open and the coproduct is
reindexed by Fin r.

All data is constructed from the actual quotient action, canonical stalk comparison,
and finite basis. Inverses come from bijections and are uniquely determined.
No arbitrary object is chosen from a sorried mere-existence declaration.
Only this module and its existing node (proof, proof_deps, proof_origin) are delivered.
No public interfaces, targets, definitions, or other modules change; no new nodes.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.coherent_generic_local_free_model`
(node `lem-pc-c3-coherent-generic-local-free-model`).
Added 0 holes; split off 0 statements. No sorry remains in any delivered file.
All private helpers are proved, including `isCoherent_closedImmersion_finiteFree`,
`coherent_stalk_iso_near`, and `closed_pushforward_stalk_iso`.
This is a completed proof from existing declarations, not a new decomposition.

Compilation passes without warnings. The theorem still depends transitively on
`sorryAx` through existing coherent stalk-extension/local-isomorphism/locality
infrastructure; it is not claimed axiom-clean throughout its import closure.
The quotient action, finite stalk and finite free coordinate lemmas, and canonical
closed-pushforward comparison use only the standard three axioms.
Rank zero and the empty coproduct are included by the finite-basis construction.
No ambient support hypothesis is used; integrality supplies the generic point.

## No longer needed

Removed from the node's proof dependencies and bypassed in the proof:

- `lem-weil-pbc-coherent-generic-point-closed-descent`, module
  `Sheaf.AlgebraicGeometry.CoherentGenericPointClosedDescent`: the quotient-field
  action on F's stalk replaces descent of its annihilated subsheaf.
- `lem-weil-pbc-coherent-integral-generic-free-neighbourhood`, module
  `Sheaf.AlgebraicGeometry.CoherentIntegralGenericFreeNeighbourhood`: build the
  finite basis on F's stalk directly, then extend the ambient stalk isomorphism.
- `lem-weil-pbc-finite-pushforward-coherent`, module
  `Sheaf.AlgebraicGeometry.FinitePushforwardCoherent`: prove the required special
  case (finite free sheaf along a closed immersion) locally in this module from
  the source-library affine localization and finite-presentation API.

These modules were not imported by the original item. The final delivered module
imports none of them. All original public imports are retained. Redundant explicit
proof imports of `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` were removed
from the working proof because the required source API is publicly available through
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.
The open-complement transport X minus i(Z minus V) and separate descent-inclusion
shrink are also unnecessary. These are local pruning claims; other import closures
may still reach the bypassed modules.

## Where the brief, the DAG or earlier work was wrong

The planned descent and finite-pushforward lemmas cannot be imported here. The
required dry-run cycle check caught this concrete cycle:
CoherentGenericLocalFreeModel -> CoherentGenericPointClosedDescent ->
ClosedImmersionPushforwardAnnihilated -> AffinePushforwardBaseChange ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism ->
FiniteFreeComplex -> FinitePresentationIntegralFiltration ->
FinitePresentationSupportReductionFiltration -> CoherentIntegralFiltrationIrreducibleSupport ->
CoherentGenericFilteredExtension -> CoherentGenericFilteredSource ->
CoherentGenericLocalFreeModel.
`tools/import_direction.py may` also rejects `FinitePushforwardCoherent` and
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion` for reaching this item.
The final route avoids those dependencies instead of changing other agents' modules.
The apparent earlier local success used the compiled snapshot, which did not expose
this source-level cycle; the dry-run check correctly refused it.

The direct quotient-field/basis route is mathematically valid: the closed-immersion
stalk map onto the field has exactly the ambient maximal ideal as kernel. The affine
pushforward helper proves its needed special case from lower source API without
cohomology or the global coherent-filtration theorem. The docstring and updated node now both record the implemented route.

The unit `sk-thm-picard-coherence` has no statement or step nodes in its `realized`
record. The unit statement and route are unchanged. Its text was read from the unit
JSON; the referenced literature/blueprint file is absent from this checkout.
The actual source used was [Stacks Project Tag 01YE](https://stacks.math.columbia.edu/tag/01YE),
read online. No mathematical statement was weakened or disputed.

## Second reading by V3

1. **Interfaces: PASS.** Compared every delivered module and node with the repository
   using diff. There is one delivered module. The existing theorem signature is
   byte for byte unchanged; all original public imports, visibility and definitions
   are unchanged. Added helpers are private. No change record or adaptation is needed.
2. **Proof and axioms: PASS.** Independently compiled the delivered module with
   lcompile.py (12.1 seconds, no warnings). A fresh scratch copy printed axioms of
   all six private helpers and the theorem. Only propext, Classical.choice and
   Quot.sound occur, except inherited sorryAx in coherent_stalk_iso_near and the
   main theorem. No delivered sorry or prohibited declaration/attribute occurs.
   The quotient action is a construction on the actual stalk, and its inverse ring
   equivalence and the pushforward inverse are determined by bijections. The finite
   basis and the finite-free stalk equivalence use proved declarations. No arbitrary
   data is taken from a sorried existence statement.
3. **Split statements and edge cases: PASS.** No statements were split off and no
   holes were added. Read every helper: the affine coherence proof works for an empty
   finite index set and even an empty source; the main proof includes rank zero.
   Integrality guarantees a nonempty Z and a field at its generic point. The
   surjective local stalk map has maximal-ideal kernel, so hkill supplies precisely
   the quotient action required, without a support or global annihilation assumption.
4. **Route, search and pruning: PASS after documentation correction.** Read the
   argument from the theorem down through affine coherence and stalk extension.
   Independent Loogle search `Module.Finite, Function.Surjective` confirmed the
   direct finite-generation transport. LeanFinder search for extending an isomorphism
   between coherent stalks returned global stalkwise-isomorphism criteria, not a
   shorter local extension theorem. Searched the Sheaf and upstream sources with
   stalk/iso and closed/free terminology; the finite-locally-free neighbourhood
   theorem has stronger hypotheses and does not apply to this closed pushforward.
   Every proof import supplies used declarations; proof-only additions use plain
   import. The three unused original proof dependencies are all listed above.
   The unit JSON has empty realized statement and step lists, and this local tool
   does not replace its coherence-of-higher-images route. Read Stacks Tags
   [01YE](https://stacks.math.columbia.edu/tag/01YE),
   [01Y4](https://stacks.math.columbia.edu/tag/01Y4) and
   [01Y6](https://stacks.math.columbia.edu/tag/01Y6) against the proof.
5. **DAG agreement: PASS after correction.** Checked the proof steps, dependency
   union and origin against the Lean and each cited node's Lean record. Removed
   lem-weil-pbc-quasi-coherent-finite-type-affine from the working node: the proof
   uses proved upstream affine finiteness/presentation declarations directly, not
   that Sheaf theorem. No new nodes exist. All node fields outside proof,
   proof_deps and proof_origin are unchanged.

Second reading changed the main theorem's docstring to describe the implemented
quotient-field and ambient-extension argument, corrected the unused affine DAG
citation, and added this review. The Lean proof itself required no repair.
The corrected working DAG citation was not an original proof dependency or an
import, so its removal prunes no additional module. Closed 1 hole, added 0 holes;
this remains a proof of the existing statement, with the inherited open axioms
reported above.
