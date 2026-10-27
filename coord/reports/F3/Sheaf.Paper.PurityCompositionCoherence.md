## What changed

Relocated the 38 existing canonical comparison declarations, with identical
signatures and bodies, to Sheaf.Paper.PurityCompositionComparisons. The item
publicly re-exports them. The unclaimed module
Sheaf.Paper.CompositionModelOrientationDefinitions changes only the import of
those definitions, avoiding the otherwise unavoidable cycle when the item uses
Sheaf.Paper.CompositionModelOrientationDescent. No WeilConjectures file changes.
The change record is
coord/changes/F3-purity-composition-comparison-extraction.md.

Implemented the parent assembly in Lean. It transports the intrinsic finite-Tor
domain through the realization counit, takes lhs=rhs from composition_tensor_mate,
takes sigma;o_fg=V;mu from composition_model_orientation_descent, derives
mu.inv;V.inv;sigma=o_fg.inv by cancellation, tensors and substitutes that identity,
then realizes and cancels the specified exceptional compositor. The parent uses
the actual canonical maps, not arbitrary isomorphisms.

Two new interface lemmas state the coordinate work missing between the existing
operations. The single-map presentation compares smoothPurityTheta to the
standing tensor mate. The iterated expansion computes only the first three arrows
with the separate inverse orientations; it does not assert coherence with the
composite orientation or use the tensor-mate composition identity. Each is a
strict part of the source's argument. Their modules have one public named hole
each, with sources, full proof sketches and DAG nodes. The parent proof is complete
relative to those interfaces and the stated dependencies.

Validation: lcompile.py compiled the four support modules in the full packet;
the final single-file compile of PurityCompositionCoherence passed cleanly in
14.3 seconds. The combined import graph and DAG references were checked for
cycles, all new node signatures match the Lean declarations verbatim, and the
existing theorem signature and all relocated declaration text were compared
against the read-only source. No original theorem binder changed.

## Proved and sorry left

Closed the original hole
WeilConjectures.PurityFiniteSetting.smoothPurityCompositionCoherence
(thm-pur-composition-coherence): 1 of 1 original holes. Its signature is unchanged.
The item's module has zero remaining holes; the extracted comparison module and
the adapted orientation-definition module also have zero holes.

Added two holes:

- WeilConjectures.PurityFiniteSetting.composition_single_mate_presentation
  (lem-pur-composition-single-mate-presentation).
- WeilConjectures.PurityFiniteSetting.composition_iterated_mate_expansion
  (lem-pur-composition-iterated-mate-expansion).

This is a decomposition: one upper hole closed, two strictly smaller interface
holes added, net -1, not a claim of a complete proof without new dependencies.
The pre-existing composition_tensor_mate and the dependencies of orientation
descent are used as stated, without modifying their proofs.

## No longer needed

The import Sheaf.Paper.PurityCompositionCoherence is removed from
CompositionModelOrientationDefinitions and replaced with
Sheaf.Paper.PurityCompositionComparisons. Its six existing downstream modules do
not use smoothPurityCompositionCoherence; the one external theorem user,
FiniteReductionOfPurity, already imports the theorem module directly. Only that
unused theorem re-export is lost from the orientation-definition module.

No module is withdrawn or globally pruned. All original public imports remain
available through the comparison-data extraction. The original private imports
move with the proofs that use them; none of their mathematics is removed.

The parent no longer cites lem-pur-composition-compatible-dnc-charts directly:
its chart and DNC argument is already assembled by the existing
lem-pur-composition-model-orientation-descent. The chart module remains a needed
transitive dependency. The parent's old direct proof dependencies
 def-pur-smooth-purity-map, def-coefficient-twists-detailed and
 def-pur-co-smoothness are used through the two coordinate interfaces and the
comparison definitions rather than re-proved in the parent. No unit-level route
is bypassed: tensor mates, the compatible DNC charts and orientation descent all
remain in the actual proof closure.

## Where the brief, the DAG or earlier work was wrong

The existing orientation-descent interface imported the theorem's module for
its comparison definitions. Consequently importing the stated proof dependency
from the item would create a Lean import cycle, even though the mathematical DAG
is not circular. The comparison extraction fixes this without changing any map.
The source-library boundary is preserved.

The mathematical assembly requires explicit bridges between the intrinsic,
exact-pullback presentation and the standing left-derived tensor-mate presentation.
The previous DAG prose did not supply declarations for these bridges. The two
new nodes record precisely that work. Edge checks: rank zero uses the same unit
constraints, empty X uses the existing orientation-descent conclusion, and no
absolute separatedness assumption or extra domain hypothesis is added.

## New nodes

lem-pur-composition-single-mate-presentation, in
Sheaf.Paper.CompositionSingleMatePresentation, fixes the canonical source change
and gives the formula for one purity map in standing mate/unit coordinates.
It uses no composition theorem.

lem-pur-composition-iterated-mate-expansion, in
Sheaf.Paper.CompositionIteratedMateExpansion, expands the iterated route using the
source's eight comparison factors and naturality, leaving the two orientations
separate. The parent must still apply both the tensor-mate equality and the global
orientation identity. The change record is
coord/changes/F3-purity-composition-comparison-extraction.md.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
