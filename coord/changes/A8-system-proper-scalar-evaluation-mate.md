# System proper scalar evaluation mate proof

The item theorem now uses the public `SemilinearSections.evaluation_mate`
calculation, with local evaluation records built from the existing normalized
pullback and direct-image comparisons.  The proof imports the split
compatibility module and changes the item interface by adding that private
proof import and a local linter option for the instance bindings.

The new compatibility declaration is a strictly smaller component equation
needed by the mate theorem and remains explicitly documented as a split-off
stage-3 statement.
