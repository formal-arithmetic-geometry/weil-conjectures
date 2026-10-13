## What changed

Proved `AlgebraicGeometry.Scheme.surjective_restrictAdjunction_unit_stalk_of_depth_two`
with its signature unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineFiniteQuotientDepth` and Mathlib
associated-prime localization import. The second reading removed redundant
finiteness and regular-element imports and narrowed the new module’s public
localization import to `Mathlib.Algebra.Module.LocalizedModule.AtPrime`. Updated
its node to the actual affine finite-hull and quotient argument.

The private, fully proved `subsingleton_of_positive_local_depth` works for arbitrary
modules over a Noetherian ring, provided their prime localizations are finite and
have positive depth. It uses existence and localization of associated primes,
Nakayama, and the regular-sequence definition of depth. The main proof constructs
`range(a) ⊔ span {s}`, proves it finite, proves its quotient vanishes, extracts a
section preimage, and applies naturality of germs. Thus the remaining theorem is
strictly the positive-depth calculation for finite intermediate quotients, not
a renamed stalk-surjectivity assertion.

Read Stacks Tags [0AV8](https://stacks.math.columbia.edu/tag/0AV8),
[0AVN](https://stacks.math.columbia.edu/tag/0AVN), and
[0E9I](https://stacks.math.columbia.edu/tag/0E9I). The local copy of Stacks source
is absent on this machine, so these primary source pages were read directly.
The unit `sk-prop-input-spreading` route is preserved.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.surjective_restrictAdjunction_unit_stalk_of_depth_two`
(node `lem-sbc-depth-two-restriction-boundary-surjective`). No sorry remains in
the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.depth_one_affine_finite_quotient_of_depth_two`
(node `lem-sbc-depth-two-affine-finite-quotient-depth`). Its proof is exactly
`by sorry`. This is a decomposition: one upper hole closed, one lower hole added,
net zero holes. No data definitions or axioms were added.

Both delivered modules compile locally together without errors or warnings.
Edge cases checked against the statement: zero quotient has infinite depth;
empty V has no prime ideals; U empty makes P zero; U equal to L makes every
intermediate quotient zero. No nonzero-module hypothesis is imposed on the new
statement. The private criterion separately handles nonzero localizations by
association before applying Nakayama.

## No longer needed

No original import or proof dependency was pruned (the original node had no
proof dependencies). Removed the first worker’s redundant proof imports
`Mathlib.RingTheory.Finiteness.Basic` and
`Mathlib.RingTheory.Regular.IsSMulRegular`; their declarations are already
available through the retained imports. Replaced the new module’s broad public
`Mathlib.RingTheory.Ideal.AssociatedPrime.Localization` import by the type-level
`Mathlib.Algebra.Module.LocalizedModule.AtPrime` import. No project module pruned. The local-to-stalk step uses germ
naturality rather than a new sheaf localization comparison theorem.

## Where the brief, the DAG or earlier work was wrong

The node's three proof steps had no stated proof dependencies despite using
substantial affine sheaf and depth theory. The finite-intermediate-quotient
calculation is therefore now explicitly a new item. The completed part of the
argument is Lean code rather than a restatement of that calculation.

The new node's uses of `pqf-lem-pushforward-qcoh`,
`lem-weil-pbc-associated-prime-submodule`,
`lem-weil-pbc-nonzerodivisor-if-maximal-not-associated`, and
`lem-weil-pbc-depth-in-ses` are generic tool lemmas from other units; they explain
the remaining calculation, not a replacement of the spreading unit's route.
The maintainer may record the corresponding tool uses. Their source arguments
and signatures were read. No existing statement or definition changed.

## New nodes

`lem-sbc-depth-two-affine-finite-quotient-depth` states that every finite submodule
of the affine restriction direct-image module containing the unit's range has
quotient with finite prime localizations of depth at least one. Its module is
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineFiniteQuotientDepth`. The docstring
records the affine setup, associated-prime exclusion, depth lemma, zero cases,
and finite localization. Whole-blueprint search for "finite intermediate quotient
depth" found no duplicate. Mathlib searches are recorded in searches.jsonl:
LeanFinder and Loogle returned related stalk and associated-prime results, grep
returned generic associated-prime lemmas, and LeanSearch returned HTTP 500.
No change record is needed because existing interfaces are unchanged.

## Second reading by J4

1. Compared both delivered modules with the repository. The quotient-depth module
   is new. The existing surjectivity theorem’s signature and docstring are byte
   for byte unchanged; no existing definition, instance or statement changed.
   The existing node changes only its proof, proof dependencies and proof origin.
   Verdict: pass; no change record needed.
2. Compiled both files locally in import order through lcompile.py. Read the
   entire finite-hull, quotient-vanishing and germ-naturality proof. An explicit
   scratch-copy `#print axioms` showed the private helper uses exactly propext,
   Classical.choice and Quot.sound; the main and new theorem additionally use
   sorryAx. Exactly one public named theorem retains `by sorry`, as reported.
   No forbidden declaration or hollow definition occurs. Verdict: pass as a
   decomposition, not a completed axiom-free proof of the item.
3. Checked the new statement against Stacks 0AV8, 0AVN, 00LX and 0E9I directly.
   Over U the quotient is zero; at boundary primes the finite middle module has
   positive depth by associated-prime exclusion. The quotient depth inequality
   applies when all three local modules are nonzero; zero source, zero middle
   and zero quotient are separately covered. Empty U, U = L, empty V and zero N
   cause no exception. The finiteness witness is a proof of a canonical module’s
   property, not arbitrary mathematical data chosen from existence. The helper
   leaves only the affine comparison and quotient-depth calculation; the original
   stalk-surjectivity assertion is not restated. Fresh LeanFinder, Loogle and grep
   searches, plus rg over the project, found ingredients but no duplicate. Existing
   depth-zero helpers found by rg are private and do not give this criterion.
   Verdict: the split is true, needed and strictly a part of the argument.
4. Reviewed the proof from the target down and the unit’s realized field and
   depth-extension step. The finite-quotient route follows 0AV8 within the same
   spreading unit; no realized unit node is bypassed (its realized lists are
   currently empty). No original proof dependency or project module can be
   pruned. The remaining split requires substantial affine sheaf localization
   comparisons, so it cannot be responsibly closed in a brief repair pass.
   Verdict: pass after import cleanup.
5. Checked both node records against Lean, including the new declaration’s
   verbatim statement, source, docstring proof, creation, blueprint chain, unit,
   chapter and three search kinds. Existing proof_deps now names exactly the
   quotient-depth theorem used. The new node’s proof_deps match its remaining
   mathematical plan; their upstream statements and the depth SES inequality
   were inspected. Verdict: pass.

Changes: narrowed the new module’s public import to the module that defines
LocalizedModule.AtPrime, removed two redundant proof imports, and expanded the
new docstring and node proof to state explicitly the affine stalk comparisons
that transport the depth hypothesis. Recorded fresh searches on the new node.
No declaration signature changed and no further hole was added or closed.
