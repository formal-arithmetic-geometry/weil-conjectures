## What changed
`Polynomial.completeLocalGenericFibre` now combines the existing proved completion
and fibre Noetherianity theorems with one remaining regularity component. Its
signature and definitions are unchanged. The first worker's core module and
duplicate Noetherian helper/node were removed. The regularity theorem now occupies
its own module `Sheaf.RingTheory.PolynomialCompleteLocalGenericFibreRegularPart`.
All added imports are private except the new module's signature dependencies.

## Proved and sorry left
Closed the original syntactic hole `Polynomial.completeLocalGenericFibre` by a
reduction, with one new hole:
`Polynomial.completeLocalGenericFibre_regularPart`, node
`lem-weil-pbc-polynomial-complete-local-generic-fibre-regular-part`.
The Noetherian obligation is proved from `AdicCompletion.isNoetherianRing` and
`Ideal.isNoetherianRing_fiber`; no Noetherian helper or new hole remains.
This is a decomposition with net zero holes closed in the import closure, not a
fully proved generic-fibre theorem. The main theorem still depends on `sorryAx`.

## No longer needed
The old direct proof dependencies
`lem-weil-pbc-complete-local-domain-finite-over-regular`,
`lem-weil-pbc-finite-algebra-is-integral`, `pqf-def-quasifinite`,
`lem-weil-pbc-formal-fibre-quasi-finite-ascent`,
`lem-weil-pbc-regular-ring-smooth-ascent`,
`lem-weil-pbc-regular-local-localization`,
`lem-weil-pbc-completion-regular-local`,
`def-weil-pbc-finite-purely-inseparable-extension`,
`lem-weil-pbc-helper-g-ring-char-p`, and `def-weil-pbc-g-ring` are replaced in
its `proof_deps` by the two proved Noetherian results and the regularity component.
The adic-completion Noetherian dependency is retained.

Removed direct imports from the main module:
`Mathlib.FieldTheory.PurelyInseparable.Basic`,
`Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
`Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular`,
`Sheaf.RingTheory.CompletionRegularLocal`,
`Sheaf.RingTheory.FormalFibreQuasiFiniteAscent`,
`Sheaf.RingTheory.PowerSeriesPolynomialFormalFiber`,
`Sheaf.RingTheory.RegularLocalLocalization`, and
`Sheaf.RingTheory.RegularRingSmoothAscent`.
The six algebraic proof-plan imports are retained in the regularity component.
`GRing` publicly provides pure inseparability. No existing module is claimed to
be globally pruned: the regularity route retains its dependencies transitively.

## Where the brief, the DAG or earlier work was wrong
The first worker called the main result proved despite two replacement holes,
and searched only the proposed helper names. A broader search found the existing
proved Noetherian-fibre theorem. Its duplicate helper was removed. The original
node had not been updated to the implemented decomposition; it now is.
The new regularity docstring previously gave only a summary, so I expanded its
finite-subring reduction and characteristic cases against Stacks 07PV.

## New nodes
`lem-weil-pbc-polynomial-complete-local-generic-fibre-regular-part` records only
the regularity component, with a self-contained statement, complete source proof,
searches, matching Lean declaration and proof dependencies. There are no statement
or definition changes and no change records.

## Second reading by K3
1. Compared the existing module against the repository with `diff`: its signature
and original declaration docstring remain byte-for-byte unchanged. No definition,
target, hypothesis or conclusion changed. Verdict: pass.
2. Compiled both modules through `lcompile.py`; no errors or warnings. Scratch
axiom probes show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`
from the single named regularity theorem. No forbidden declarations or data
choices occur. Verdict: pass, as a decomposition only.
3. The remaining statement is the regularity part, omitting the separately proved
Noetherian obligation; it does not introduce a new geometric-regularity assertion
under another name. It follows Stacks 07PV at the zero prime. For a field A this
reduces to the regular polynomial completion fibre, and the trivial extension
recovers ordinary regularity. The zero fibre also poses no extra assumption.
Broader leanfinder/loogle/grep and local searches found the Noetherian duplication
but no exact regularity result. Verdict: pass as an open component, not a proof.
4. The Noetherian part uses the existing shorter route. The regularity proof plan
retains the finite-subring, regular-completion and power-series steps. The item
is not in `sk-thm-p1.json`'s `realized` lists; those lists are unchanged. Imports
needed by the remaining plan are retained in its module. Verdict: pass.
5. Updated the original node's proof/dependencies/origin to the actual Lean
reduction and the new node's module, statement dependencies, proof and searches.
No other DAG fields of the existing node are changed. Verdict: pass.

Second reading removed the duplicate Noetherian helper and core module, proved
that component directly from existing theorems, expanded the remaining docstring,
corrected the nodes and progress accounting, and pruned direct proof imports.
