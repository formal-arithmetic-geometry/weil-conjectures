## What changed

Completed the proof of
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_affine_base_change_comparison`
without changing its signature, universes, visibility, or existing docstring.
Added the proof-only import
`Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineSourceCoordinates`.
The remaining source-coordinate construction has its own theorem, module, and node.

The target coordinates are constructed in the assigned module by the proved private helpers
`cotangentEquiv` and `targetCoordinates`. The cartesian cone identifies the immersion ideal
with the affine extension of the upstairs ideal. The multiplication algebra isomorphism
`B ⊗[A] A ≃ₐ[B] B` transports the cotangent quotient, and the existing affine conormal
sections theorem supplies its normalized section coordinate. The inverse cotangent maps
are checked on ideal representatives.

The comparison proof uses the existing conormal functoriality theorem, naturality of the
pushforward composition/congruence isomorphism, naturality under restriction, scalar
linearity, surjectivity of ideal-to-cotangent classes, and tensor induction. It genuinely
proves commutation for every section; the new obligation asserts only source coordinates
and contains neither `c`, a target coordinate, nor a conormal-map commutation equation.
The DAG copy records this implemented route. All elaboration options are scoped to
individual declarations. Only the sandbox contains the delivery sources.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_affine_base_change_comparison`
(node `lem-weil-pbc-closed-immersion-conormal-affine-base-change-comparison`).
The assigned module has no remaining `sorry`.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_affine_source_coordinates`
(node `lem-weil-pbc-closed-immersion-conormal-affine-source-coordinates`), in
`Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineSourceCoordinates`.
Its whole proof is `:= by sorry`; its docstring and node give the source and complete
argument. This is a decomposition: one hole closed and one strictly smaller hole added,
not a claim of a net reduction in holes or of an axiom-free final comparison.
The target coordinate construction, generator comparison, and induction are complete Lean.

Local single-file compilation, including compilation of the sibling module in import order,
passed without warnings. Revalidated the inherited proof against the current compiled library.
The initial delivery dry run detected the declaration-scoped instance attribute as an
interface command change; replaced it with two proof-local `RingHomInvPair` instances.
The resulting interface comparison reports no changes to existing declarations or commands. The new source statement was checked mathematically at J=0,
J=A, and on empty affine charts: its modules and generator formulas reduce to zero in
the degenerate cases. No flatness hypothesis is used or added. These are edge-case
checks of the statement, not claims that the source-coordinate theorem has been proved.

## No longer needed

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` and
`Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal` from the assigned module.
`Sheaf.AlgebraicGeometry.AffineConormalSections` remains used by the target construction.
Added only the source-coordinate module and the narrower, proved
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine` proof imports.
The new source module imports only what its statement needs.

The implemented route and the remaining source argument no longer require these nodes:
`lem-weil-pbc-open-preimage-fibre-product`,
`lem-weil-pbc-cartesian-square-pasting`, and
`lem-weil-pbc-quotient-base-change-closed-immersion-ideal`
(module `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal`).
The closed-immersion chart rings follow instead from surjectivity and the first
isomorphism theorem; their ideal is computed directly by the existing affine ideal-comap
formula. This prunes these dependencies from this argument, not necessarily from every
other target's closure.

`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-tensor-over-quotient-ring`, and the affine-cover criterion are now needed
only in the smaller source-coordinate node's plan; they are not claimed mathematically
unnecessary. The original unit statement and every realized unit step are retained.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no interface correction or forced adaptation was needed.
The previous affine geometric quotient-base-change route is longer than necessary:
Mathlib's cartesian-cone isomorphism and kernel invariance, followed by the existing
sorry-free `ideal_comap_appLE`, give the exact ideal equality directly.

The remaining difficulty is assembling the source affine pullback equivalence with the
quotient scalar cancellations while retaining its successive-unit normalization.
That is isolated precisely in the new node, rather than hidden inside the final proof.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, source grep,
and imported-blueprint searches were completed. The Stacks sources were read online
at Tags 0473, 01JU, and 01R3 because the recorded local TeX paths are absent on this
machine. No project process files were edited. The first dry run also required a second-reading
section, which is intentionally reserved for the independent second worker; the launcher
explicitly permits that single pending check in a worker dry run.

## New nodes

`lem-weil-pbc-closed-immersion-conormal-affine-source-coordinates`, module
`Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineSourceCoordinates`, declaration
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_affine_source_coordinates`:
the normalized additive equivalence between sections of the iterated pullback and
`B ⊗[A] J.Cotangent`, with its inverse formula on scalar multiples of ideal-unit
sections. It is strictly the source-coordinate part of the original argument.
Its proof uses the existing affine conormal/pullback sections and tensor-over-quotient
nodes, and the closed affine ideal-comap implementation. Its chapter and unit match
the assigned node, and its blueprint ancestry includes that node. No change record
is needed: no existing statement, definition, or public import was changed.


## Second reading by V4

Independent second reader, 2026-10-13; did not write the delivered proofs.

1. Interface: PASS. Read the full diff against the repository module. The original
   theorem signature is byte-for-byte identical, including universes, hypotheses,
   canonical-map equation, and conclusion. Its docstring and public imports are
   unchanged. The only existing-node changes are proof, proof_deps, proof_origin.
   No existing definition, statement, or visibility changes; no change record needed.
2. Proof and axioms: PASS as a decomposition. Compiled both files in import order
   with lcompile.py, cleanly. Read cotangentEquiv, targetCoordinates, hclasses,
   naturality equations, and tensor induction. The sole delivered sorry is the whole
   proof of the named public source-coordinate theorem. No prohibited declarations
   or hollow definitions. A scratch copy with #print axioms shows only propext,
   Classical.choice and Quot.sound for cotangentEquiv, and these plus sorryAx for
   targetCoordinates, the source theorem, and the comparison. The target-coordinate
   helper still depends on the upstream affine-conormal existence obligation.
   Equivalences from unproved statements are used locally in theorem proofs, not
   to define arbitrary data; their normalizations also determine them uniquely.
3. Split statement: PASS. Checked its complete docstring and node argument against
   Stacks Tags [0473](https://stacks.math.columbia.edu/tag/0473),
   [01JU](https://stacks.math.columbia.edu/tag/01JU), and
   [01R3](https://stacks.math.columbia.edu/tag/01R3), and the actual affine conormal
   and pullback section declarations. The source is
   (B/JB) tensor_(A/J) (J/J^2) = B tensor_A (J/J^2): JB kills the latter by
   balancing, so cancelling quotient scalars needs no flatness. The inverse formula
   follows the successive-unit formulas and restriction. It determines an additive
   equivalence uniquely because ideal representatives surject onto J.Cotangent,
   ideal sections represent every ideal element, and pure tensors additively generate.
   Checked J=0, J=A, empty affine charts (all zero), identity base change, and the
   nonflat example A=Z, J=(2), B=Z/2: source Z/2, target cotangent zero. Thus this
   source obligation does not disguise the comparison or assume its invertibility.
   Independent LeanFinder search on pullback of ideal modulo its square, Loogle
   TensorProduct/Ideal.Cotangent, Mathlib quotient-tensor grep, and repository searches
   for coordinates, sections, equivalences and quotient cancellation found only the
   component affine-section results and algebra-level maps, no duplicate theorem.
   Closing the remaining sheaf/quotient assembly is not a few-minute proof repair.
4. Route and pruning: PASS. The target cotangent transport is a real construction;
   the conormal map is checked on generators and extended by tensor induction.
   All proof-only imports are plain imports. The new module's public imports serve
   its statement. No shorter exact library declaration found. No longer needed lists
   the six removed old direct proof dependencies: three genuinely unnecessary nodes
   (open-preimage pullback, pasting, quotient-base-change ideal), and the affine-cover,
   affine-pullback and quotient-tensor nodes retained under the smaller source node.
   Read sk-thm-p1.json realized: no unit statement or realized step is removed or
   bypassed. No claim of net hole reduction or whole-library pruning is made.
5. DAG: PASS. Compared old/new nodes and Lean. The new node has matching chapter,
   unit, ancestry, source, searches, created and lean fields, and its stored Lean
   statement is byte-identical to the new declaration. Each proof_deps is the union
   of the step uses. The comparison node records the actual source-coordinate call,
   cotangent transport, affine-conormal normalization and functoriality/induction route.

Changes by the second reader: appended this independent review; no Lean proof,
statement, import, definition, or DAG correction was necessary. Removed the scratch
axiom probe after checking it. One original hole closed and one smaller hole added
remain exactly as reported above: decomposition, net zero direct holes.
