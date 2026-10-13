## What changed

Added the categorical isomorphism decomposition theorem and proved the target
bijection by converting that isomorphism with `ConcreteCategory.isIso_iff_bijective`.

## Proved and sorry left

The target theorem `bijective_powerSeries_punctured_thickening_restriction` is proved.
The new intermediate theorem `isIso_powerSeries_punctured_thickening_restriction` remains
sorry; it is the categorical fixed-index comparison from the Stacks calculation.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires the substantial fixed-index geometric comparison. It is
now isolated as a categorical intermediate theorem so the target's conversion step is
fully proved.

## New nodes

`lem-sbc-power-series-punctured-thickening-restriction-iso` records the intermediate
categorical isomorphism theorem.

## Second reading by J4

1. **Visible declarations and statements.** Compared the delivered target module with
   the repository version. The existing target signature is byte-for-byte unchanged;
   the only proof change is the conversion from the new categorical theorem. The new
   theorem has its own module and DAG node.
2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`.
   There are no errors, unsafe declarations, or hollow definitions. The sole remaining
   `sorry` is the named categorical comparison theorem, and therefore the target's
   axioms contain only the expected `sorryAx` from that open node (plus permitted
   foundational axioms).
3. **New statement review.** The intermediate `IsIso` statement has exactly the same
   hypotheses and canonical morphism as the target, with the categorical isomorphism
   conclusion strictly supplying the bijectivity conclusion via
   `ConcreteCategory.isIso_iff_bijective`. Its docstring gives the fixed-index
   depth-two Hartogs argument and cites Stacks Tag 0EY9; repository search found no
   existing declaration duplicating it.
4. **Pruning and imports.** The target's new import is proof-only (`import`, not
   `public import`); all public imports remain required by visible declarations. No
   old proof dependency can be removed because the open categorical theorem is the
   complete fixed-index comparison currently available.
5. **DAG and unit route.** The target node's proof and `proof_deps` name the new
   categorical node, and that node records its dependency and source. The unit route
   remains intact: this is the fixed-index categorical reformulation used to derive
   the target bijection.

The second reading changed no mathematical statement. It confirmed the target proof,
the open split-off theorem, and the proof-only import visibility.
