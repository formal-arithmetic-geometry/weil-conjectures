## What changed

Replaced the sorry in `AlgebraicGeometry.finite_structure_unit_lift_existence` by a complete
Lean reduction to one supporting-quotient theorem and the existing full-faithfulness clause
of `AlgebraicGeometry.grothendieck_existence`. The statement and its public imports remain
identical. Added proof imports for the supporting quotient, Grothendieck existence, closed
immersions, and comparison transport.

Added `Sheaf.Paper.FiniteStructureUnitQuotientSystem`, which states only the construction of
a coherent properly supported Q, a map q from the structure sheaf, and compatible reduced
factorizations with their scalar formula. It assumes neither adic completeness nor a
multiplication on G, and does not assert a lifted map or any unit law. Its proof is the
single new named sorry. Its docstring describes the actual construction Q = O_X/J using
the scheme-theoretic support, the quotient factorization, transition calculation and
adjunction formula. No data definition chooses an arbitrary witness of an unproved
existence statement: witnesses occur only inside the proof of the original existence theorem.

Three private helpers are fully proved: adjoint precomposition, injectivity of the adjoint,
and transfer of compatible families between natural comparisons. The latter uses the
existing comparison-transport theorem, since Grothendieck existence's comparison uses an
unconstrained chosen composition isomorphism while the item's comparison is pinned to the
canonical adjunction. The original signatures are not changed to reconcile these interfaces.

The main proof lifts Q to G, composes with q, and proves the scalar formula by naturality.
It constructs L = rho.inv followed by identity tensor eta followed by mu; symmetry
identifies this endomorphism with left multiplication by eta(1).
Multiplicativity and the scalar formula at 1 imply a_n composed with L equals a_n.
Adjunction injectivity and cancellation of psi_n then give j_n^*L = identity. Uniqueness in
full faithfulness proves L = identity, and evaluation gives the left-unit law. This avoids
an additional lemma about generators of the tensor pullback. The original commutativity hypothesis is used to identify right and left multiplication.

Sources read: official Stacks pages [09ZT](https://stacks.math.columbia.edu/tag/09ZT),
[0CYS](https://stacks.math.columbia.edu/tag/0CYS), and
[088F](https://stacks.math.columbia.edu/tag/088F). The local clone contains literature indexes
but not coherent.tex; the official sources supply the cited argument. Mathlib searches were
run through msearch.py: Lean Finder returned affine section and tilde lemmas, Loogle returned
unitHomEquiv and unit-section lemmas, and grep returned unrelated quotient/unit results.
LeanSearch returned Internal Server Error, recorded as unavailable. Local rg found the
proved comparison-transport theorem and tensor-section/unitor formulas, but no supporting
quotient factorization with this compatibility and scalar formula.

Validation: both delivered modules compile through lcompile.py. The required deliver3.py
--no-push dry run passes compilation and preflight except for the independent second
reading, which is reserved for the second reader. Nothing was pushed.

## Proved and sorry left

Closed the item's one hole, `AlgebraicGeometry.finite_structure_unit_lift_existence`
(node `lem-weil-pbc-finite-structure-unit-lift-existence`), by decomposition.

Added one hole: `AlgebraicGeometry.finite_structure_unit_quotient_system`
(node `lem-weil-pbc-finite-structure-unit-quotient-system`), in its own new module.
Its entire proof is exactly `by sorry`. No sorry remains in the item or in a private helper,
and there are no new definitions or axioms. One hole closed and one added: this is a
decomposition, not a net reduction in holes.

The combination proves the completion lift, the scalar formula of the lifted map, the
completed endomorphism identity, and the left-unit law in Lean. The new hole supplies only
the earlier quotient-system step, rather than the original theorem under another name.
Existing imported declarations may still depend on their own recorded holes.

Edge cases checked mathematically: G = 0 uses its empty scheme-theoretic support and Q = 0;
an empty X has unique section maps; I = 0 gives constant reductions and the same quotient
factorization. The new quotient step requires no completeness and also permits I = top,
when all reductions are empty. The main proof uses full faithfulness globally on G to G;
it never assumes joint injectivity of reduction on sections of an arbitrary open away from
V(I), a statement that would be false.

## No longer needed

No existing imports were removed and no globally required module or node is claimed pruned.
The supporting-subscheme, coherent-cokernel/image, coherence-on-Noetherian-schemes, and affine
base-change dependencies are moved from the item's direct proof dependencies into the new
quotient-system node, where they remain necessary. Their modules are not globally pruned:
`Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase`,
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`,
`Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`, and
`Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange`.

The remaining old direct dependencies `def-pc-tensor-pullback-composition-iso` and
`def-pc-module-pullback` are no longer direct steps of the item: the former occurs in
the quotient-system step and the latter in the adjunction and completion infrastructure.
Neither module is globally pruned.

No separate tensor-pullback pure-generator argument, pullback tensor comparison, or
multiplication/associativity lifting theorem is needed for the left-unit step. None of these
was an explicit import of the item, so this does not claim a removed module. Public imports
of the existing item are retained to preserve its interface. The new module uses only four
public imports required by its statement.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or source error was found. The original plan did not mention the
comparison mismatch between its pinned comparison and Grothendieck existence's chosen one;
the existing `compatible_family_comparison_equiv` closes that gap without adaptation.

The DAG's proposed check on pure generators is unnecessary: equality of the adjoints on all
opens proves equality of their sheaf morphisms, and the adjunction Hom equivalence reflects
it to the reduced maps. Full faithfulness then detects the global endomorphism identity.
This is a simplification below the unit level. `sk-thm-p1` and all its realized steps remain
unchanged, and the algebraization route through supporting quotient and full faithfulness
is kept.

## New nodes

`lem-weil-pbc-finite-structure-unit-quotient-system` is the reduced quotient factorization
step from Tag 09ZT, expanded by the proper-support and affine base-change results. It belongs
to sec-proper-base-change / sk-thm-p1 and points to the finite-etale lifting blueprint
ancestor. Its recorded Lean signature is verbatim. The item's copied node records the
actual quotient-system, comparison-transfer, completion-lift and adjunction-injectivity
argument. No interface change record or forced adaptation is needed.

## Second reading by R1

1. Compared the delivered item module with the repository version. The original theorem
   signature is byte-for-byte unchanged; only proof-only imports, private helpers, and the
   proof body changed. The added quotient-system module and node are the only new artifacts.
   Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all` and checked the source for
   forbidden declarations. The target theorem has no `sorry`; the sole remaining `sorry` is
   the named split theorem `finite_structure_unit_quotient_system`, with its docstring and
   matching node. In-place `#print axioms` checks of both public theorems returned only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Verdict: pass.

3. Read the split statement and checked edge cases (zero module, empty scheme, zero and top
   ideals). It omits completeness, multiplication, and the lifted unit, so it is strictly
   simpler than the target and is not a restatement. Searches recorded in `searches.jsonl`
   found no existing declaration with this statement. Independent searches used annihilator
   and factorization terminology in grep, Loogle, and Lean Finder; none supplied the system
   theorem. Local library inspection found only supporting ingredients. The construction
   cannot be closed by a short application of an existing theorem. Checked Stacks
   [09ZT](https://stacks.math.columbia.edu/tag/09ZT) and
   [0CYS](https://stacks.math.columbia.edu/tag/0CYS) against the quotient argument. Verdict: pass.

4. Traced the proof from the quotient-system result through comparison transport,
   Grothendieck full faithfulness, adjunction injectivity, and the multiplicativity argument.
   The pinned comparison is transported to the comparison required by Grothendieck
   existence, and the unit route through the supporting quotient and full faithfulness is
   retained. Verdict: pass.

5. Checked the changed node proof, proof dependencies, proof origin, and the new node's
   metadata against the Lean proof and unit `sk-thm-p1`. Dependencies used by the proof are
   recorded, and no removed import or unreachable node is claimed. Corrected the tensor
   section step to cite `lem-weil-pbc-module-tensor-symmetric-monoidal`, whose source
   explicitly records the upstream TensorSection formulas, rather than the generic
   tensor-product definition node. Verdict: pass after this metadata repair.

Changes: corrected the tensor-section proof dependency in the existing node, completed the
list of old direct dependencies no longer used, and recorded this review and axiom checks.
No Lean proof, statement, definition, or import required repair.
