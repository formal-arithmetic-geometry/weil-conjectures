## What changed

Proved `isGRing_quotient` in `Sheaf.RingTheory.QuotientGRing` with its signature unchanged.
Added the proof-only import `Mathlib.RingTheory.RingHom.Surjective`.
Second reading removed the redundant tentative quotient-Noetherian import.
The original two proof imports are both used: `LocalCompletionQuotient` and
`RegularBaseChange`. Added three fully proved private helpers for geometric regularity
under algebra equivalence, regular maps under algebra equivalence, and regular completion
under a surjection of Noetherian local rings. No public definition or statement changed.

The localized quotient map is proved surjective by Mathlib
`RingHom.surjective_localRingHom_of_surjective` (simplified in second reading).
The completion equivalence is constructed from the existing completion theorem, the kernel
quotient equivalence, and Mathlib's tensor-quotient equivalence. Its compatibility with the
completion map is checked on every lift, rather than assumed. Flatness, Noetherianity,
and regularity after each required field extension are explicitly transported.
Updated the item's node proof, proof dependencies, and proof origin to this argument.
The unit's own realized statement and steps are unaffected.

Read the Stacks sources online because the local literature source is absent:
[07PP](https://stacks.math.columbia.edu/tag/07PP),
[00MA](https://stacks.math.columbia.edu/tag/00MA), and
[07C1](https://stacks.math.columbia.edu/tag/07C1).
Searches: LeanFinder found only generic quotient-ring declarations; Loogle returned an
unknown-identifier error for `Ideal.Quotient`; logged Mathlib grep and repository searches
found no existing proof of this G-ring quotient theorem. Used the existing plan instead.

## Proved and sorry left

Closed one hole: `isGRing_quotient` (node `lem-weil-pbc-g-ring-quotient`).
No `sorry` remains in the delivered module, and no holes were added or split off.
All three private helpers are completely proved.
The proof still depends on the existing named theorems
`AdicCompletion.exists_local_completion_quotient`
(node `lem-weil-pbc-local-completion-quotient`) and `RingHom.regular_base_change`
(node `lem-weil-pbc-regular-base-change`), whose existing holes are not modified.
Thus this closes the item's direct hole; it does not claim the transitive proof is axiom-free yet.

## No longer needed

No original imports were removed, and no Sheaf dependency modules are pruned.
Second reading removed `Mathlib.RingTheory.Ideal.Quotient.Noetherian`: the quotient
Noetherian instance is already available through the original imports.
Removed these direct DAG proof dependencies:

- `lem-weil-pbc-finite-type-algebra-noetherian`: use the quotient Noetherian instance directly.
- `lem-weil-pbc-flat-local-ring-maps`: only ordinary localization Noetherian/local instances
  are needed, not flatness of induced maps.
- `lem-weil-pbc-localization-at-prime-of-quotient`: use Mathlib localized
  surjectivity and the kernel of that map, without identifying it with the extended ideal I.

The tensor-quotient node remains needed, as does the local-completion-quotient node.
A redundant tentative import of `Mathlib.RingTheory.Noetherian.Basic` was removed before
final compilation; it is already imported by the quotient Noetherian module.
These are removals of direct dependencies of this item, not claims that no other target
branch uses the three nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool failure found. The planned identification of the localized
kernel with I times the localization is unnecessary: the generic completion theorem accepts
the kernel itself. General finite-type Noetherianity and flat localized maps are also
unnecessary here. The existing declaration docstring records the original mathematically
valid plan; the node now records the precise Lean implementation.
Edge cases require no extra assumptions: I=0 is allowed, while I=top and the zero ring have
no prime ideals, so the universally quantified completion condition is vacuous.

## Second reading by B3

1. Interface: compared the sole delivered Lean module with the repository using `diff`.
   The signature of `isGRing_quotient`, its docstring, universes, public imports and all
   existing definitions are byte-for-byte unchanged. No change record is needed. The
   node's statement and statement dependencies are unchanged. Verdict: pass.
2. Proof: compiled the delivered module locally without errors or warnings. There is no
   `sorry`, axiom, unsafe declaration, opaque declaration or foreign implementation in it,
   and no new definition. A scratch copy with `#print axioms` for all four declarations
   showed only `propext`, `Classical.choice`, `Quot.sound` for the first two private helpers,
   and those plus `sorryAx` for the completion helper and the public theorem. The latter
   use the existing open `exists_local_completion_quotient` and `regular_base_change`.
   The completion theorem determines theta coordinatewise: each theta-k is determined
   by the surjective quotient map and its commuting equation, evaluations determine theta,
   and the final equation determines e on the surjective quotient map. Thus no arbitrary
   undetermined data is selected from an open existence theorem. Verdict: pass.
3. Splits and small cases: no new holes or public statements were split off. Read all
   three private proved helpers: tensor congruence transports every required purely
   inseparable extension; flat composition and fibre tensor congruence transport regular
   maps; the surjective completion helper checks the B-algebra commuting equation on
   every lift before transporting regularity. Identity surjections and zero kernel are
   admitted. I=0 is allowed; I=top and the zero ring have no prime to check. Searches in
   Mathlib, the upstream library and lean/Sheaf found no existing G-ring quotient proof
   or geometric-regularity equivalence helper. Verdict: pass.
4. Route and pruning: searched with the alternate terms `localRingHom` and surjectivity
   using launcher msearch grep and direct rg. Found the exact Mathlib theorem
   `RingHom.surjective_localRingHom_of_surjective`, and replaced the manual fraction
   lifting with it. Removed the redundant quotient-Noetherian proof import after a
   scratch compile without it succeeded; added only the proof import for the surjectivity
   theorem. Both original Sheaf proof imports remain used. Compared old and new
   proof_deps: all three removed nodes are listed under No longer needed. Read
   dag/units/sk-thm-p1.json: neither this auxiliary node nor any removed dependency
   realizes a unit statement or step, and the unit route is preserved. Verdict: pass.
5. Nodes: compared the node diff and read the retained dependencies, including the
   Mathlib tensor-quotient leaf. Only proof, proof_deps and proof_origin change. The union
   of step uses equals proof_deps and the steps follow the actual fraction-free Lean
   proof, kernel quotient, completion comparison and regularity transport. No new node
   requires validation. Verdict: pass.

Changed in second reading: simplified localized surjectivity to its exact Mathlib theorem,
removed one redundant proof import, and updated the node and report to the final proof.
No mathematical fault, statement change or extra hole was found.
