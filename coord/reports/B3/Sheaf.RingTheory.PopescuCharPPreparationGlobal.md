## What changed

Replaced the sole sorry in `Sheaf.RingTheory.PopescuCharPPreparationGlobal` by a
complete tensor-product assembly proof. Every existing declaration signature and
all public imports are unchanged. The proof sets
`d = (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank`,
obtains a universal standardizer `B` and improved `C₀`, obtains a compatible
parameter/coefficient solution on `B`, and constructs `C = R ⊗[k[x]] C₀`.
It defines β by tensor inclusion and defines γ and a by `AlgHom.liftEquiv`.
It verifies γβ = α and the quotient factorization on tensor generators, applies
the universal standardizer's singular-ideal and strict-standard conclusions,
and carries over the independently constructed ideal containments and kernel
conditions. Finite presentation is supplied by Mathlib's base-change instance.

Added two modules, each containing one public construction theorem with its whole
proof left as sorry, and corresponding nodes. The new statements are independent:
the first has no geometric-regularity hypothesis, prime, localization, characteristic
or Artinian solution; the second has no improved C₀, β₀, ρ, tensor algebra C or map
a:C→E. Both use the explicit standardizer presentation
`A[x_i,z_ij]/(x_i^(2N)-sum_j z_ij a_j)`. The parent constructs the missing tensor
algebra and maps, rather than applying a renamed version of itself.

The existing global-preparation node now records exactly this assembly route.
The unit `sk-thm-p1` and its realized statement/steps are unchanged. This is a
below-unit decomposition of the same 07FJ construction.

Validation: all three modules compile with the launcher, with no compiler
warnings (6.1 s, 2.8 s and 12.9 s for the complete set). The first worker's dry run was blocked by a missing `refuse_missing` tool import.
The second reader's dry run passes that step with the current tools; no delivery
tool was changed or bypassed. The initial second-reader preflight requested the
second-reading section, added below. The declaration reader reports no existing signature changes and no
sorry in the parent. Edge-case review covered d=0, the empty generator family,
zero padding, N=1 and c=1, trivial source rings, and unequal universes u,v,w.
For d=0 the coefficient solution uses n=N>0, m_L=0 and the appended zero
parameter, so the eighth-power ideal remains zero and the power bounds hold.
The strengthened universal standardizer conclusion is valid for arbitrary R:
smoothness on the singular generators' opens survives arbitrary base change,
and strict standardness likewise survives arbitrary base change.

## Proved and sorry left

Closed the original hole in `Algebra.exists_popescu_char_p_preparation_global`
(node `lem-weil-pbc-popescu-char-p-preparation-global`). Its proof is complete
from the two construction theorems below and Mathlib tensor-product lemmas.
There is no remaining sorry in the assigned module.

Added exactly two holes:

- `Algebra.exists_popescu_universal_standardizer`, node
  `lem-weil-pbc-popescu-universal-standardizer`, in
  `Sheaf.RingTheory.PopescuUniversalStandardizer`.
- `Algebra.exists_popescu_parameter_solution`, node
  `lem-weil-pbc-popescu-parameter-solution`, in
  `Sheaf.RingTheory.PopescuParameterSolution`.

This is a decomposition: one upper hole closed and two strictly distinct
construction holes added (net -1 before any pruning). It is not a proof of the
entire construction from sorry-free dependencies. No definitions, axioms, private
sorries or anonymous sorries were added. The existing docstring and signature
of the parent are unchanged.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.Ogoma`
- `Sheaf.RingTheory.EssentiallySmoothBaseChange`
- `Sheaf.RingTheory.EssentiallySmoothComp`
- `Sheaf.RingTheory.ImprovePresentation`
- `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`
- `Sheaf.RingTheory.PopescuSolutionModulo`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`
- `Sheaf.RingTheory.RegularRingSmoothAscent`
- `Sheaf.RingTheory.RegularSequencePolynomialVariables`
- `Sheaf.RingTheory.RegularSequencePowers`
- `Sheaf.RingTheory.SingularIdeal`
- `Sheaf.RingTheory.SingularIdealLocalizationSmooth`
- `Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower`
- `Sheaf.RingTheory.StrictlyStandardBaseChange`

`Sheaf.RingTheory.SingularIdeal` was a redundant direct import: the existing public
import of `PopescuResolution` already exposes the same definitions. The other
removed modules belong to the construction steps now represented by the two new
nodes; their mathematical content remains needed in those nodes' proof plans.
They are no longer direct dependencies of the tensor assembly. No claim is made
that all these modules leave the targets' transitive mathematical proof closure.
The source-module proof-dependency edges displaced by this decomposition are:

- `def-weil-pbc-essentially-smooth-ring-map`
- `def-weil-pbc-finitely-presented-algebra`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-popescu-resolution`
- `def-weil-pbc-regular-sequence`
- `def-weil-pbc-singular-ideal`
- `def-weil-pbc-strictly-standard-element`
- `def-weil-regular-scheme`
- `lem-weil-pbc-essentially-smooth-base-change`
- `lem-weil-pbc-essentially-smooth-composition`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `lem-weil-pbc-field-regular-ring`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-finite-type-noetherian-finite-presentation`
- `lem-weil-pbc-flat-height-formula`
- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-improve-presentation`
- `lem-weil-pbc-localization-base-change`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-ogoma`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-popescu-enlarge-solution-modulo`
- `lem-weil-pbc-popescu-solution-modulo`
- `lem-weil-pbc-regular-local-generators-regular-sequence`
- `lem-weil-pbc-regular-ring-smooth-ascent`
- `lem-weil-pbc-regular-sequence-polynomial-variables`
- `lem-weil-pbc-regular-sequence-powers`
- `lem-weil-pbc-singular-ideal-localization-smooth`
- `lem-weil-pbc-smooth-free-differentials-strictly-standard-power`
- `lem-weil-pbc-smooth-ring-map-base-change-composition`
- `lem-weil-pbc-smooth-ring-map-local-on-cover`
- `lem-weil-pbc-smooth-ring-map-principal-localization`
- `lem-weil-pbc-strictly-standard-base-change`

Every one that supplies a construction step is retained in at least one new
node's proof dependencies. The finite-presentation base-change node remains a
direct parent proof dependency. The tensor base-change universal-property node
is now explicitly recorded, matching `AlgHom.liftEquiv`, its tensor-generator
formula and tensor-map extensionality used by the Lean proof. No unit statement
or unit proof step is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement or definition correction was needed. The original node contains the
right construction plan, but there is no declaration packaging its coordinated
standardizer and coefficient-solution steps. Separate existing lemmas alone do
not supply the resulting maps without those construction steps. The two new
statements package those distinct steps without relocating the entire parent
statement under another name.

The original correction n=N+d(8c), rather than the source's n=N+dc, is retained:
it ensures the required pigeonhole power bound for eighth powers. No minimality
hypothesis on q is introduced. The locally checked Stacks source was the obtained
copy at `/home/ubuntu/work-bp/sheaf/literature/stacks-project/smoothing.tex`;
the repository's literature text is absent on this worker machine. Searches found
no matching implementation in Mathlib or the source library. LeanSearch was
unavailable (Internal Server Error); this is recorded without a no-match verdict,
with the successful LeanFinder and source-grep searches also recorded.

## New nodes

`lem-weil-pbc-popescu-universal-standardizer` states the universal polynomial
standardizer construction and the improved presentation's base-change properties.
It isolates the geometric part (07CE, 07EZ and 07CC) and carries its full proof in
words. Its carrier data are existential in a theorem, not chosen in a definition.

`lem-weil-pbc-popescu-parameter-solution` states the arithmetic part: choose
parameters, denominator rescalings and Artinian coefficients compatible with
that explicit polynomial presentation, and construct maps on B itself. It
isolates 07FH, 07FI and Ogoma plus ideal bounds and polynomial evaluation. It
cannot yield the parent's improved tensor factorization by itself; the parent
constructs and verifies that factorization using the first theorem's retraction.

Both nodes have self-contained statements, exact Lean signatures, Stacks sources,
numbered proof steps with existing dependencies, all three search kinds, and the
same chapter/unit and blueprint ancestry as the assigned node. No change record
is required because no existing public interface changes.


## Second reading by B3

1. Interface preservation: PASS. Read the complete diff against the repository.
   The existing theorem signature and docstring are byte-for-byte unchanged;
   only its proof and private proof imports differ. There are no existing
   definitions changed, no added hypotheses, and no weakened conclusions.
   The two additional modules introduce only the documented public theorems.
2. Kernel and holes: PASS. Compiled all three modules through `lcompile.py --all`
   (7.0 s, 4.6 s, 16.4 s), without errors or warnings. A separate scratch module
   printed axioms of all three declarations: exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The parent has no direct sorry; the two construction
   theorems each have exactly one whole named proof left as sorry. No forbidden
   declaration or hollow definition occurs. The delivery tool's whole-environment
   probe initially timed out on the parent; the explicit declaration checks above
   completed in 9.0 s. This decomposition is not a sorry-free proof.
3. Split statements: PASS. Read the source's 07FJ construction and its justifications,
   and the existing improvement, standard-power, singular-ideal, solution-modulo,
   and enlargement declarations. The geometric statement gives the universal
   standardizer; the arithmetic statement gives maps on its actual presentation.
   Neither restates the tensor factorization of the parent. Both have complete
   construction proofs in their docstrings and matching nodes. Checked d=0,
   empty generator families, zero padding, c=1, N=1, the zero A algebra, and
   independent universes. For arbitrary base changes, smooth principal opens and
   strict standardness persist; no Noetherian assumption on the new base is needed.
   For d=0 the local maximal ideal is zero, n=N remains positive, and appending
   zero preserves J and both kernel conditions. Separate LeanFinder searches for
   the universal quotient/retract and compatible polynomial/Artinian parameters
   returned related standard-smooth results, not these constructions. Loogle
   did not know the project's strict-standard predicate; source grep found no
   alternate implementation. These searches do not supply a shorter proof, and
   neither remaining construction is a few-minute consequence of one declaration.
4. Route and pruning: PASS. Read the tensor assembly from the top downward.
   The coefficient identities prove gamma beta = alpha; tensor extensionality
   proves the quotient diagram. Every remaining private import is used, and
   public imports support signatures. Compared old and new proof-dependency
   lists: every displaced node is listed under No longer needed. The unit
   sk-thm-p1 and all its realized statement/step nodes remain unchanged.
   The report correctly calls this a decomposition with one hole closed and
   two added, not net proof progress or a claim of transitive pruning.
5. Node agreement: PASS. All three recorded Lean signatures match the declaration
   reader after the required whitespace normalization. Each proof_deps list is
   exactly the union of its proof-step uses. The parent node differs only in
   stage-3-owned fields. New nodes have sources, full construction plans,
   three search kinds (including the accurately recorded unavailable service),
   status, creation, blueprint ancestry, chapter, unit and Lean records.

Changes by the second reader: updated the obsolete tool-failure status in this
report and added this independent review and axiom evidence. No Lean proof,
statement, definition, import or node needed repair.
