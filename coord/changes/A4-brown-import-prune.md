# Brown hypotheses import pruning

Removed the direct public import `Mathlib.CategoryTheory.Idempotents.Basic` from
`Sheaf.SixFunctorsBasics.BrownHypotheses`. The module still compiles because all
names used by its declarations are supplied by the remaining public imports, and
static import-prune analysis finds no downstream module that relied on this module
to re-export a declaration from the removed import. No declaration signature,
definition, instance, attribute, or theorem statement changed.

The assigned `brownHypotheses` theorem remains the explicitly disputed
arbitrary-field assertion with its existing named `sorry`; the import change does
not claim to prove that assertion.
