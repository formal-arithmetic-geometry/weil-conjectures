## What changed

Proved `AlgebraicGeometry.Scheme.spec_algClosed_etale_sheaf_constant_counit` in
`Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstantCounit`, with its signature unchanged.
Three private, proved helpers establish terminality of the identity etale object,
locality of the site, and detection of sheaf isomorphisms by terminal evaluation.
The local-site theorem makes the constant-sheaf functor fully faithful; the right
triangle identity makes the terminal counit component invertible; identity-point
conservativity then makes the counit invertible.

Added proof-only imports `Mathlib.CategoryTheory.Sites.LocalSite`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`, and
`Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstantStalk`.
Updated the existing counit node's proof, dependencies and proof origin to this route.
The unit `sk-thm-iff` has only the PBC/IA equivalence as its realized statement and
step; this change is below that unit and preserves its route.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.spec_algClosed_etale_sheaf_constant_counit` (the
module's sole original sorry). The three new private helpers are also fully proved.
There are no sorries left in the module and no new unproved statements or nodes.
The existing identity-stalk theorem used by the proof is already proved.
Local compilation is clean. The delivery dry run also checks the axiom probe and
compiles on the server; its result is recorded by the final READY response.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural`
- `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`

The counit proof no longer needs the nodes
`lem-weil-pbc-constant-sheaf-set-sections-connected-natural` or
`lem-weil-pbc-etale-fibre-discrete-separable-points`, or their corresponding modules.
It needs neither the coproduct decomposition of etale schemes into singleton
components nor the product-of-sections and connected constant-section comparisons.
`def-weil-pbc-etale-sheaf-of-sets` is also removed from `proof_deps`: it remains
a statement dependency rather than a proof step. This reports pruning from this item, without claiming other target paths
no longer reach those modules.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The old geometric product plan can be replaced
by existing categorical locality and conservative-point tools. The universe lift is
necessary: the coefficient sets are in `Type (u + 1)`, whereas Mathlib's original
small-etale points take values in `Type u`. The source library supplies the proved
universe-lifted conservativity theorem and the fibre comparison isomorphism.

The repository does not contain the cited Stacks source file on this machine.
Read the official pages https://stacks.math.columbia.edu/tag/03P5 and
https://stacks.math.columbia.edu/tag/0A3H: they supply related constant-sheaf and
connected-pullback facts, rather than the exact counit theorem. The new proof origin
is explicitly agent-written from the already-proved Lean interfaces, with no new
sorry requiring a literature proof. The existing declaration docstring is preserved.


## Second reading by R1

1. PASS: compared the sole delivered module with the repository using `diff`.
   The existing theorem signature and docstring are byte for byte unchanged;
   no existing definition or public import is changed. Only its proof, proof-only
   imports, and three private proved helpers are added. There are no change records
   or additional delivered modules.
2. PASS: local compilation succeeds without warnings. A scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.spec_algClosed_etale_sheaf_constant_counit`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The module contains
   no sorry or forbidden declaration/attribute. The private definition constructs
   terminality from a proved Mathlib theorem and contains no postponed data.
3. PASS: no statements are split off, and no new nodes or unproved declarations
   are introduced. Read the already-proved identity-stalk theorem and the lifted
   conservative-family theorem. The local-site argument uses an actual marked
   lift to split a covering arrow; the terminal evaluation argument uses naturality
   and cancellation of isomorphisms, valid also for empty coefficient sets.
4. PASS: searched the existing algebraic-geometry library for identity terminality,
   local-site and counit results, and inspected Mathlib LocalSite. Replaced the
   hand-built terminality proof with `MorphismProperty.Over.mkIdTerminal @Etale S`.
   The remaining imports serve the signature, required sheafification instance,
   locality, lifted conservativity, and identity-stalk comparison. Compared old
   and new proof dependencies: the two geometric lemmas and the sheaf-of-sets
   definition are all accounted for in No longer needed. Read `sk-thm-iff.json`:
   this item realizes no unit-level statement or step, so its shorter proof
   preserves the unit route.
5. PASS: the existing node changes only proof, proof_deps and proof_origin.
   Each step matches the Lean proof; proof_deps is exactly the union of uses.
   The statement, statement dependencies, Lean signature, chapter and unit stay
   unchanged. The conservativity node is a Mathlib leaf, with the universe lift
   correctly explained in the proof record.

Changed the private terminality helper to use Mathlib directly and explicitly
listed the removed definition node in the pruning report. No mathematical fault
was found in the remaining proof.
