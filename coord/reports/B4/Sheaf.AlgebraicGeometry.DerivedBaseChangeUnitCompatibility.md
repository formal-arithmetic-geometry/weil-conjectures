## What changed

Replaced the whole-proof sorry of
`AlgebraicGeometry.derivedBaseChange_unit_compatibility` with the pinned-adjunction
argument, using the private proved categorical helper `exchange_unit_of_counit`.
The statement, universes, definitions and public imports of the existing module
are unchanged. Added two independent intermediate modules:
`Sheaf.AlgebraicGeometry.HomotopyPullbackSquareLocalization` and
`Sheaf.AlgebraicGeometry.HomotopyBaseChangeCounit`. The first constructs the real
canonical homotopy pullback square and states its compatibility with localization;
the second states the ordinary homotopy exchange's counit transpose.

The earlier attempt's final conversion unfolded large resolution definitions.
The proof now builds the same natural transformation componentwise with the
object-level equality transport, proving its naturality from the original
composite. It explicitly uses the supplied derived-category family for the
local scheme-module instances. The final goal is changed to the pinned mate's
component expression before applying the categorical result. No definition or
existing signature changes, and no extra module or hole is introduced.

## Proved and sorry left

Closed: `AlgebraicGeometry.derivedBaseChange_unit_compatibility` (1 original hole).
Added: `AlgebraicGeometry.homotopyPullbackSquare_localization`
(node `lem-pc-homotopy-pullback-square-localization`) and
`AlgebraicGeometry.moduleHomotopyBaseChange_counit`
(node `lem-pc-homotopy-base-change-counit`). These are the only two sorry proofs
left in the delivery. This is a decomposition, with one upper hole closed and
two lower holes added; it is not a proof free of sorry dependencies.

The localization statement has arbitrary M, K and a and contains no direct-image
unit or derived adjunction. The ordinary counit statement contains no derived
categories. Neither is the original compatibility under another name. Their
combination uses derived counit compatibility obtained from the existing pinned
Hom equivalence, naturality of the derived square and Hom equivalence, and actual
adjunction identities. Edge cases checked: zero complexes, identity squares and
empty schemes require no exclusions; all steps are natural transformation laws.

## No longer needed

Removed the redundant private import of
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`: the same declarations are
already supplied by the existing public import of `SchemeDerivedBaseChangeMap`.
No planned proof-dependency node or module is pruned: all three original
proof dependencies remain necessary. No geometry, acyclic resolution or Cech
comparison is imported for this identity.

## Where the brief, the DAG or earlier work was wrong

The original one-step node plan suppresses two distinct bridge identities: the
pullback-only localization square and descent of the ordinary counit formula to
homotopy categories. The existing dependency declarations supply the canonical
comparisons and adjunctions, but do not state these identities. They are now
independent items. No statement correction or forced adaptation is required.
The unit route is preserved.

The preflight signature reader interprets a top-level pipeline `|>` inside a
statement as the start of an equation-style proof. This misread the two local
adjunction abbreviations in the new ordinary theorem as a partial sorry proof.
The new statement now uses direct method application for those abbreviations;
its mathematical type is identical. No checking tool was changed or bypassed.

## New nodes

`lem-pc-homotopy-pullback-square-localization` records the left-derived counit
factorization of the pullback square; its module also contains the fully
constructed `moduleHomotopyPullbackSquare`. Its proof is the composite counit
step of the original argument, expanded using the defining lift factorization
and counit naturality (Stacks 0D5S and 0DVC).

`lem-pc-homotopy-base-change-counit` records the ordinary counit identification
from the original argument. Its proof expands conjugate comparisons and triangle
identities on modules and descends degreewise through the homotopy quotient
(Stacks 08HY). Both statements were checked against the existing modules and
searched with Lean Finder, Loogle and grep; LeanSearch was unavailable.

Change record: `coord/changes/B4-homotopy-base-change-bridges.md`.

## Second reading by B4

1. Compared the delivered item module with the repository version: the public
   declaration and definitions are unchanged; only the proof and its private
   import differ. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py`; the only remaining
   `sorry`s are the two named bridge theorems, each with a matching node and
   source docstring. No forbidden declarations or hollow definitions occur.
   Verdict: pass.
3. Read both new statements against their constructions and checked zero,
   identity, and empty-scheme cases. They are strictly smaller bridge
   identities, with no extra hypotheses beyond the source route. Verdict: pass.
4. Checked the proof route and imports: the original proof dependencies remain,
   `DerivedPullbackComposition` is redundant, and the unit route through the
   pinned derived square is preserved. Verdict: pass.
5. Compared the DAG proof and proof dependencies with the Lean proof and
   verified both new node records and the open change record. Verdict: pass.

Changed only this second-reading report section; no Lean declarations or node
statements were changed during review.
