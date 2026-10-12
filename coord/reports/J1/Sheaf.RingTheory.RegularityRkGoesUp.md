## What changed

Proved `RingHom.regularity_rk_goes_up` in
`lean/Sheaf/RingTheory/RegularityRkGoesUp.lean`, without changing its signature or public imports.
Added the proof-only import `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` and removed the
proof-only import `Sheaf.RingTheory.FibreRingNoetherian`.

The proof follows Stacks [033A](https://stacks.math.columbia.edu/tag/033A): localize at a
prime of height at most k, bound the contracted prime's height using the flat height
formula, use (R_k) for the base and fibre, identify the closed fibre, and apply
`IsRegularLocalRing.of_flat_of_regular_closedFiber`. The fibre-height bound uses the
quotient dimension inequality, avoiding the dimension-form conversion of the height formula.
The equality transport of localizations and the equality of extended ideals are proved in Lean.
Updated the node's proof and proof dependencies to describe this implementation.

Searches: LeanFinder for flat ascent of Serre (R_k) returned regular-sequence ascent and
flatness results, but no direct theorem. Loogle found
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`. The grep search confirmed that
lemma; repository searches found no other ascent proof. The Mathlib fibre and regular-local
APIs were read at their declarations.

## Proved and sorry left

Closed the one original sorry: `RingHom.regularity_rk_goes_up`
(node `lem-weil-pbc-regularity-rk-goes-up`). No sorry remains in the delivered module.
No new declarations with sorry, and no new nodes, were introduced.

The proof depends on the existing open declaration
`IsRegularLocalRing.of_flat_of_regular_closedFiber`
(node `lem-weil-pbc-flat-over-regular-with-regular-fibre`), as intended by stage 3.
Local compilation passes with no errors or warnings.

## No longer needed

Removed import `Sheaf.RingTheory.FibreRingNoetherian`, module of
`lem-weil-pbc-fibre-ring-noetherian`. Its theorem `Ideal.isNoetherianRing_fiber`
is not needed: `hfibres p` already supplies precisely that instance.
Removed that node from this item's `proof_deps` and step 4's `uses`.
All other planned dependency nodes remain used, through the stated theorem or Mathlib APIs.
The unit's realized statement and steps are unaffected; this item is not itself one of them.

## Where the brief, the DAG or earlier work was wrong

The initial module lacked a proof import for the Mathlib flat-height formula.
The planned use of a separate fibre-Noetherianity theorem was redundant with `hfibres`.
No mathematical statement, target signature, or unit route was changed.
The cited local Stacks source file is absent on this machine; the statement and proof of
Tag 033A were checked on the Stacks website. The fibre-local-ring identification was checked
against the existing node and the actual Mathlib `Ideal.Fiber.algEquivAux₂` signature.

## Second reading by J1

1. PASS: compared the delivered module with the repository version using `diff`.
   The existing theorem signature is byte for byte identical; no definitions, public imports,
   or other visible declarations changed. No change record is needed.
2. PASS: local compilation completed without errors or warnings (2.8 seconds).
   A scratch copy with `#print axioms RingHom.regularity_rk_goes_up` compiled and reported
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter comes from
   the existing open regular-local ascent theorem, not a sorry in this delivery.
   Scanned the delivered Lean for sorry, axiom, unsafe, opaque, implemented_by, extern,
   explicit sorryAx, and kernel-check bypasses: none occurs. There are no hollow definitions.
3. PASS: no statements or nodes were split off, so there are no new statements to validate
   or duplicate-search. Checked the actual Mathlib fibre equivalence and height-formula
   signatures, including the contraction equality and ideal transport. For k = 0 the height
   bounds still give height zero; for a zero target ring there is no prime to check.
4. PASS: searched the upstream/library files for other Serre regularity ascent proofs and
   the Mathlib ideal files for alternative height bounds; found no direct replacement.
   The argument follows the local regularity route of
   [Stacks Tag 033A](https://stacks.math.columbia.edu/tag/033A), read independently.
   The public imports supply IsSerreR, Flat, and Fiber in the signature; both plain imports
   supply results used in the proof. The old proof dependency omitted from the new proof is
   exactly `lem-weil-pbc-fibre-ring-noetherian`, already listed under No longer needed.
   Read `dag/units/sk-thm-p1.json`: this item and the pruned node are not realized unit steps,
   and the unit route is preserved. The original docstring describes the original dimension
   formula route; the updated node and report accurately describe the implemented bounds.
5. PASS: compared the old and delivered node JSON. Only proof, proof_deps, and proof_origin
   changed; statement and lean signature metadata are unchanged. Read every retained
   dependency's Lean/Mathlib record and matched it to the proof. The union of the proof
   steps' uses equals proof_deps, including the existing open closed-fibre ascent theorem.

Second reading changed only this report, adding the independent checks and verdicts.
The proof and node update required no repair. No new sorry was introduced.
