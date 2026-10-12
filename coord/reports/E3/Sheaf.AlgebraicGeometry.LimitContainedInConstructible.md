## What changed

Proved `AlgebraicGeometry.exists_eventually_range_subset_of_isConstructible` with its signature unchanged in `Sheaf.AlgebraicGeometry.LimitContainedInConstructible`. Two fully proved private helpers transport the constructible-image lemma to an arbitrary affine scheme and descend disjointness via empty pullbacks. The main proof represents the complement chart by chart, applies the empty-pullback argument directly over the original stage, and combines the resulting stages using a finite directed upper bound.

Removed the proof import `Sheaf.AlgebraicGeometry.LimitAffineTransition`. Kept the statement imports and the existing proof import `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`, which supplies the base-change limit construction. Updated the existing node's proof, proof_deps and proof_origin to this route. No definitions or existing theorem signatures changed.

## Proved and sorry left

Proved the sole original sorry: `AlgebraicGeometry.exists_eventually_range_subset_of_isConstructible` (node `lem-weil-pbc-limit-contained-in-constructible`). Both private helpers are completely proved. No sorry remains in the module and none is added elsewhere. The proof uses Mathlib and the already proved source-library base-change theorem, rather than any sorry-bearing Sheaf declaration.

Local single-file compilation succeeds without warnings. The delivery dry run also performs the server compile and declaration axiom probe.

## No longer needed

Removed import and direct dependency: `Sheaf.AlgebraicGeometry.LimitAffineTransition`, node `lem-weil-pbc-limit-affine-transition` (including its existence-core and affine-comparison helpers on this route). The hypothesis already supplies an actual limiting cone; no existence theorem is necessary.

Removed direct proof dependencies `lem-weil-pbc-limit-cone-affine-projections-opens` (Mathlib's affine projections / opens-cone results) and `pqf-def-affine-morphism`: no inverse system of restricted opens is constructed. Affineness is used through the transition instance and affine-permanence lemmas. The affine-morphism notion still occurs in the unchanged statement.

Removed direct proof dependency `lem-weil-pbc-fibre-product-points`: the proved Mathlib pullback image formula, represented by existing node `lem-weil-pbc-base-change-image`, supplies the needed point-lifting consequence. This formula internally uses fibre-product points, so this is a replacement of the direct dependency, not a claim that the underlying Mathlib result is globally unnecessary.

All remaining original proof dependencies stay. No assertion is made that any of these nodes is unreachable from every other project target.

## Where the brief, the DAG or earlier work was wrong

The original plan's limit-existence import was unnecessary because the statement already provides `c` and `hc`. Its restricted-open-system construction can also be avoided: composing each affine representative W_a → U_a with U_a → T_i allows applying the empty-pullback argument over T_i directly. The proof needs only compactness of the fixed target stage, not quasi-separatedness, but all original hypotheses are preserved.

Edge cases checked in the argument: an empty target has an empty finite cover, handled by including i in the finite set of bounds; an empty constructible complement is represented by the zero ring via 00F8; arbitrary preorders are handled by uniqueness of morphisms, without antisymmetry; no nonemptiness of schemes is assumed. The item is not among the unit record's realized statement or proof-step nodes, and the revised proof retains the same source argument below the unit level. No new nodes or unresolved statements.

## Second reading by E3

1. **Unchanged visible statements: PASS.** Compared the delivered module with the
   repository by `diff`, and separately compared the existing theorem's entire signature
   byte for byte. `AlgebraicGeometry.exists_eventually_range_subset_of_isConstructible`
   keeps all original hypotheses and its eventual-image conclusion. No definition is
   changed; the two added helpers are private, fully proved theorems. The existing node
   changes only `proof`, `proof_deps`, and `proof_origin`. No change record is necessary.
2. **Proof and trust: PASS.** Local single-file compilation succeeds without errors or
   warnings. A scratch copy with `#print axioms` for the main theorem and both private
   helpers reports exactly `propext`, `Classical.choice`, and `Quot.sound` for each.
   There is no `sorry`, axiom declaration, unsafe/opaque declaration, external
   implementation, or hollow definition. All Lean lines meet the 100-character limit.
3. **Split statements and edge cases: PASS (none split off).** There are no new holes or
   public intermediate statements. Read both helper proofs: base change preserves the
   supplied limit, quasi-compactness of W makes the stage pullbacks quasi-compact,
   and nonemptiness of every stage contradicts emptiness of that limit. The affine
   helper transports the exact image equality through the canonical spectrum
   isomorphism, without a finite-type hypothesis. Empty schemes, E empty, E universal,
   and an empty finite cover are valid; insertion of i provides a bound even for an
   empty cover. Morphism uniqueness handles preorders without antisymmetry.
4. **Route and pruning: PASS.** Read Mathlib's `Scheme.nonempty_of_isLimit` and
   `PrimeSpectrum.exists_range_eq_of_isConstructible`, and the source library's
   `baseChangeDiagram`, `isLimitBaseChangeCone`, and affine-transition instance.
   Checked Stacks Tags 05F4 and 05F3 at
   https://stacks.math.columbia.edu/tag/05F4 and
   https://stacks.math.columbia.edu/tag/05F3 (the local literature text is absent).
   The chartwise representatives composed to the original stage implement the same
   empty-pullback argument without constructing restricted-open diagrams. A fresh
   Mathlib search for `05F4|constructible.*[Ll]imit|[Ll]imit.*constructible` and searches
   in both library roots found no direct replacement. Remaining public imports supply
   the statement's affine morphisms, limits, preorder category, and constructibility;
   the source-library import is correctly proof-only. The report lists all four old
   proof dependencies removed; the new pullback-image dependency supplies exactly the
   point-lifting consequence used. Checked `dag/units/sk-thm-p1.json`: this node is
   neither a realized statement nor a realized step, and no unit-level route is bypassed.
5. **DAG agreement: PASS.** Read the updated five proof steps and each changed dependency.
   Their `uses` union equals `proof_deps`: constructible complement representatives,
   empty limit pullbacks, preservation of the limit and affine/quasi-compact stages,
   pullback image formula, then finite directed bounds and factorization. The node's
   source and `proof_origin` describe this actual route. No new node requires validation.

Second reading changed only this report, adding the independent checks above. The
Lean proof and node record needed no repair. Holes closed: the one original main
 theorem; holes added: none; this is a proof, not a decomposition.
