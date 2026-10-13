## What changed

Replaced the sole sorry in `Algebra.exists_popescu_coefficient_induction` with a finite
prefix induction. The theorem's signature and existing public imports are unchanged.
The induction constructs each B-algebra structure by composition, transports the A-map,
updates only the current factor and coefficient row, and proves that the earlier quotient
ideals and kernel conclusions remain unchanged. It then transports the final algebra to
the required universe, chooses coefficient lifts, and proves that factor lifts are units
using locality. The zero-parameter case is the induction base, without excluded cases.

Added four modules, each with one public theorem:

- `PopescuCoefficientStart`: proved the initial B/k structures, localization smoothness,
  injective polynomial-presentation descent to an A-map, and universe lift.
- `EssentiallySmoothSmallLocalModel`: proved the smaller carrier and smooth-model transport
  using Mathlib's `FiniteType.small`, fraction surjectivity, `Shrink`, and localization
  equivalences.
- `ArtinianCoefficientEnlargement`: extracted and proved the generic Artinian part of 07FI
  from the existing separable-residue and transcendental-localization declarations, together
  with the explicit Frobenius/nilpotence argument. No chart or geometric-regularity hypothesis
  is needed once the flat local Artinian map has been supplied.
- `PopescuCoefficientStep`: stated the strictly single-parameter successor step, retaining the
  previous factors as input and producing one new factor, one coefficient row, and an
  essentially smooth coefficient extension. This is the remaining hole.

All edits are in the sandbox. No existing statement or definition was changed, and no
adaptations of another group's modules are included. The item uses a declaration-local
unused-variable linter setting because its preserved signature contains `hreg` and `hspan`,
which the generic successor argument does not require.

## Proved and sorry left

Closed: `Algebra.exists_popescu_coefficient_induction`, node
`lem-weil-pbc-popescu-coefficient-induction` (1 of 1 original holes).

Added and proved: `Algebra.exists_popescu_coefficient_start`,
`Algebra.exists_essentiallySmooth_small_local_model`, and
`Algebra.exists_artinian_coefficient_enlargement`. These proofs may retain the existing
transitive holes of their imported project dependencies; they add no direct sorry.

Added and left exactly `:= by sorry`: `Algebra.exists_popescu_coefficient_step`, node
`lem-weil-pbc-popescu-coefficient-step`, in `PopescuCoefficientStep.lean`.

There are no sorries left in the item's own module or in the other three added modules.
This delivery closes one upper hole and adds one strictly smaller successor-step hole:
it is a decomposition (direct net holes closed minus added = 0), with the finite induction,
initial presentation descent, unit lifting, and universe transport actually proved in Lean.
The sole new hole is a source-backed one-parameter argument, not the original theorem under
another name: it has no A or polynomial chart, constructs no finite tuple of factors, and
makes no small-model conclusion.

Edge cases checked in the argument: d=0 has no successor steps; s=0 is a zero-ideal coefficient
family and the correction calculation still gives the required zero power relation; n=N
makes the correction ideal m^(n-N) equal to the whole ring, and multiplication by u_i^N
still kills its residue; n>0 ensures the quotient is nontrivial and local. The generic
Artinian enlargement also covers x=0. The small-model theorem allows arbitrary padding
universe w.

## No longer needed

Removed the item's proof imports `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`,
`Sheaf.RingTheory.RegularSequencePowers`, and `Sheaf.AlgebraicGeometry.Ogoma`.
The latter two remain dependencies of the single-parameter successor item, so their modules
are relocated dependencies, not globally pruned work.

The specialized node `lem-weil-pbc-popescu-enlarge-solution-modulo` and module
`Sheaf.RingTheory.PopescuEnlargeSolutionModulo` are no longer used by this argument: the
proved generic `ArtinianCoefficientEnlargement` suffices. In particular, this argument no
longer needs the chart-dependent `PopescuSolutionModulo` route through that import.
These modules may still have other importers; no claim of whole-library unreachability is
made. Removed from the parent's direct proof-dependency list the flat-local and faithful
ideal-contraction nodes (now used by the proved initial setup and successor), the presentation,
singular-ideal and localization definition nodes (used in the typed specializations), the
specialized enlargement node (replaced), regular-sequence-powers and Ogoma (used by the
successor), localization-base-change (the proved setup uses the quotient-localization
instance directly), and the essentially-smooth definition node (used in the support proofs).
The composition node remains a direct dependency.

No blueprint unit statement or realized step was bypassed or removed. No public import of
the item was removed. The second reading also removed the unused public PopescuResolution
import of the new start module and narrowed the new enlargement module's residue-field
import to proof visibility; the small-model node no longer lists prime localization.

## Where the brief, the DAG or earlier work was wrong

The initial setup does not require the chart's flatness or maximal-ideal extension equation
once D0 and its commuting flat local map are supplied; these hypotheses stay unchanged in
the original theorem and are not repeated in the new initial-setup theorem. Likewise,
geometric regularity and the parameter spanning assertion are unnecessary for the rescaling
argument once the initial solution, parameter residue lifts and regular sequence are given.

The original 07FI declaration requires a polynomial chart and its hypotheses, whereas the
single-parameter induction only needs its generic local Artinian argument. Rather than cite
that declaration for a statement it does not give, `ArtinianCoefficientEnlargement` makes
that generic argument explicit and proves it from the actual reusable declarations.

`literature/stacks-project/smoothing.tex` is not materialized in this read-only clone.
The cited source was read directly at https://stacks.math.columbia.edu/tag/07FJ and
https://stacks.math.columbia.edu/tag/07FI; no source was reconstructed from memory.
The blueprint ancestor script reports None because earlier `created.item` fields use module
names. The new nodes retain the already recorded ancestor
`thm-weil-pbc-finite-etale-lifting` and its explicit via chain from the item's node.
Blueprint searches across all chapters found no statement duplicating the new results.
LeanSearch returned Internal Server Error for each query; the new nodes record unavailable,
with actual LeanFinder, Loogle, and grep searches retained.

## New nodes

`lem-weil-pbc-popescu-coefficient-start` records the proved initial coefficient setup and
A-map descent (07FJ steps 9 and 25). Its statement does not assert any parameter rescaling.

`lem-weil-pbc-essentially-smooth-small-local-model` records the proved universe transport
for an arbitrary local Artinian essentially smooth algebra. Both the coefficient carrier
and its smooth model are shrunk; no unsupported large smooth-model witness remains.

`lem-weil-pbc-artinian-coefficient-enlargement` records the proved generic Artinian power
capture argument of 07FI. The output extension and factorization are existence conclusions;
no definition chooses arbitrary data from a sorry-backed existence result.

`lem-weil-pbc-popescu-coefficient-step` records the remaining one-parameter correction,
denominator-clearing, and Ogoma adjustment argument of 07FJ ad (13). It imports the actual
stated ingredients, including the new proved generic enlargement. Its docstring gives the
full correction and denominator formulas and explains preservation of coefficient residues.

No change record is necessary: all existing signatures, definitions and public imports are
unchanged. The parent's node copy updates only proof, proof_deps and proof_origin.

## Second reading by K4

1. Compared the delivered induction module with the repository using diff and checked the
   entire existing theorem signature byte for byte with a string comparison: identical.
   The only existing node changes are proof, proof_deps and proof_origin. No existing
   definition, target, public import or other group's module changed. Verdict: pass.
2. Read all five modules, including the initial presentation descent, finite-prefix
   invariant, scalar towers, small-carrier transport and Frobenius argument. There is
   exactly one direct sorry, the named public exists_popescu_coefficient_step; there are
   no hollow definitions or forbidden declarations. Local compilation and axiom checks
   are recorded below. Verdict: pass.
3. Read the successor statement and its complete docstring against Stacks 07FJ ad (13),
   https://stacks.math.columbia.edu/tag/07FJ, and the generic enlargement argument in 07FI,
   https://stacks.math.columbia.edu/tag/07FI. Checked i=0, empty coefficient families,
   n=N, positive exponents, and absence of successor steps for d=0. In particular the
   correction vanishes because u_i^N lies in m^N and c'_j lies in m^(n-N); this works
   when n=N as well. The denominator formula and both coefficient memberships persist
   through the two power adjustments. Field characteristic p>0 forces p prime; the
   Noetherian positive-power target quotient is Artinian, as the enlargement needs.
   The step omits the polynomial chart, A-map, whole-family construction and small-model
   conclusion: it is strictly part of the original argument, not a renamed theorem.
   Independent LeanFinder, Loogle and grep queries (in searches.jsonl), and rg of the
   project under annihilator, square, rescaling and coefficient terminology, found no
   direct replacement. Existing regular-sequence powers and Ogoma are the right
   ingredients; the generic support proofs already use Mathlib for the other parts.
   Closing this substantial remaining step is beyond a short review repair. Verdict: pass.
4. Checked the induction from the target downward, including preservation of earlier
   quotient ideals by prefix_span_update and preservation of ranges by the commuting
   maps. The report accounts for all ten old direct dependencies removed or relocated,
   retains composition, and distinguishes direct pruning from global unreachability.
   Read dag/units/sk-thm-p1.json realized: no unit statement or realized step is bypassed
   by these changes below the unit. Verdict: pass.
5. Checked every new Lean signature against its node's verbatim lean.statement, and
   every proof_deps list against the union of its proof-step uses. Checked the parent's
   route against the finite induction actually written. New nodes have source,
   blueprint ancestry, search evidence, creation and Lean records. The small-model
   proof uses arbitrary localization, so its prime-localization dependency was spurious
   and is now removed. Verdict: pass after this repair.

Second-reading changes: replaced the unused public PopescuResolution import in
PopescuCoefficientStart by the precise public MvPolynomial.Basic signature import;
made ArtinianCoefficientEnlargement's ResidueField.Basic import private to the proof,
with public LocalRing.Defs for its signature; removed the spurious prime-localization
proof dependency from the small-model node. No statement or proof body changed.
The hole accounting remains one original hole closed and one successor hole added
(a decomposition, direct net zero); three additional public support theorems are proved.

Validation: lcompile.py --all compiled all five delivered modules without errors or warnings.
A scratch module with #print axioms for all five public theorems compiled. The initial
setup, small model and generic enlargement use only propext, Classical.choice and
Quot.sound. The successor and induction additionally use sorryAx, exactly as expected
from the sole remaining successor hole. No other axiom was printed.
