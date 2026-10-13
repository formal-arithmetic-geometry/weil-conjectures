## What changed

The signature of `FieldTheory.triangularFieldModel_localized_normal_form` is unchanged.
Its proof constructs the canonical coefficient map from `Localization.Away h` to the
triangular quotient using the relation `hT-1`, and defines the bounded-monomial
reconstruction as an explicit sum of k-linear maps. Bijectivity supplies its inverse
coordinate equivalence. The proof then descends evaluation to the quotient, proves
that evaluation composed with the coefficient map equals `phi` by localization
extensionality, and applies evaluation to the reconstruction identity.

One proof-only import was added: `Sheaf.FieldTheory.TriangularFieldModelReconstructionBijective`.
That new module states only the structural bijectivity result, without an ambient
extension field, evaluation map, variable assignments, or compatibility formula.
It carries a source and complete proof in words. The two node records reflect this route.

## Proved and sorry left

Closed the item's sole hole, `FieldTheory.triangularFieldModel_localized_normal_form`,
from the new structural lemma. This is a decomposition, not a net hole reduction.

Added one hole: `FieldTheory.triangularFieldModel_reconstruction_bijective`, node
`lem-weil-pbc-triangular-field-model-reconstruction-bijective`.
No `sorry` remains in the item's module. There is no holed definition or arbitrary
witness chosen as definition data: the localization map and synthesis map are explicit,
and the inverse linear equivalence is determined uniquely by synthesis bijectivity.

## No longer needed

All original public imports of the item are retained: removing them changes
its exported import interface and the delivery tool requires an interface change
record. The second reader tested their removal but restored them after that
preflight diagnostic. Removed redundant imports
`Mathlib.RingTheory.Ideal.Quotient.Operations` and
`Mathlib.RingTheory.Localization.Algebra` from the new module.
No lower planned node or Sheaf module is pruned. The structural lemma retains
`lem-weil-pbc-localization-away-polynomial-quotient`, `lem-weil-pbc-monic-quotient-free`,
and `lem-weil-pbc-tower-product-basis`. These are Mathlib leaves; their argument still
needs the glue identifying the simultaneous quotient with successive monic quotients.
The old direct proof dependencies `lem-weil-pbc-localization-away-polynomial-quotient`,
`lem-weil-pbc-monic-quotient-free`, `lem-weil-pbc-tower-product-basis`, and
`def-weil-pbc-free-module` are no longer direct uses of the item; they remain
indirect dependencies through reconstruction bijectivity, so none is pruned from
the argument. The evaluation step does not require an additional node or hole. No new field-theory
independence hypothesis or algebraicity hypothesis is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the supplied statement or unit route was found.
The existing plan correctly distinguishes coefficients over the localized base from
coefficients over k. The `hyt` assumption is redundant in the evaluation calculation:
the relation `hT-1` and localization extensionality force the inverse value.
The signature is retained exactly.

The new structural statement was checked on the edge cases: for `m=0`, reconstruction
is the coefficient isomorphism on a singleton coordinate space; if an `e i` is zero,
monicity makes that relation equal to one and both sides are zero; for `h=0`, `hT-1=-1`
and both localization and quotient are zero. Repeated roots and inseparability never
enter monic division. The unit's realized statement and steps are unchanged.

## New nodes

`lem-weil-pbc-triangular-field-model-reconstruction-bijective` isolates the synthesis
bijection from steps 1 and 2 of the original node, following Stacks Tags 07BV and 08JZ
(read online). LeanFinder found only single-variable power bases, Loogle found
`Module.Basis.smulTower`, and Mathlib/source/project grep found no simultaneous
triangular reconstruction theorem. LeanSearch was unavailable (Internal Server Error).
No change record or forced adaptation is needed.

## Second reading by K1

1. Compared the complete item module with the repository using diff, and compared
   its theorem signature byte for byte with a script: identical. All field,
   monicity, degree, coordinate, vanishing and phi-compatibility hypotheses and
   the linear-equivalence/evaluation conclusion are unchanged. No definition or
   other existing declaration is changed, and no change record is required.
2. Read the explicit f, psi, L, nf and ev constructions. The relation hT-1
   proves hu; hzero kills the entire ideal span; hyx and hphi give equality of
   ev.comp psi with phi by localization extensionality; hyb identifies the
   monomials. Applying ev to L(nf([q]))=[q] gives exactly the sum claimed.
   The only choice is the inverse of a bijective specified map, uniquely
   determined by that map; no arbitrary existence witness supplies data.
   Both modules compile locally. Explicit scratch #print axioms checks show
   only propext, Classical.choice, Quot.sound and sorryAx. The sole remaining
   sorry is the reported reconstruction theorem; no forbidden declarations or
   holed definitions occur.
3. Read Stacks Tags [07BV](https://stacks.math.columbia.edu/tag/07BV) and
   [08JZ](https://stacks.math.columbia.edu/tag/08JZ). The first supplies the
   triangular monic quotient route, the second the hT-1 localization
   presentation. The new lemma is the structural normal-form part of this
   argument, generalized to arbitrary monic relations; it contains no ambient
   field evaluation or compatibility conclusion. Successive monic division
   proves it without independence or separability. Checked m=0 (singleton
   coefficient), a zero degree (p_i=1, zero quotient and empty exponent set),
   h=0 (zero localization and quotient), and degree-one/repeated-root
   relations (division still unique). Strengthened its docstring with the
   variable-wise inverse maps for the successive quotient identification and
   the inductive uniqueness argument. Independent msearch queries used
   "basis for quotient of multivariate polynomials by a triangular sequence
   of monic relations" (LeanFinder), "IsAdjoinRootMonic.basis" (Loogle), and
   "quotient.*basis|basis.*quotient" (grep); rg also checked the project's
   triangular field theory modules. Only single-variable bases and tower
   ingredients were found. The remaining structural glue is substantial and
   cannot be closed in a few minutes. This is a genuine partial reduction,
   closing one upper hole and adding one strictly structural hole, net zero.
4. Read the original proof plan and its localization, monic-quotient and
   tower-basis leaf records. No shorter existing reconstruction theorem was
   found. The real evaluation proof retains the needed structural step.
   Removed redundant Mathlib imports from the new module; the new proof-only
   Sheaf import is plain import. The No longer needed section now lists all
   old direct proof dependencies transferred to the structural lemma.
   dag/units/sk-thm-p1.json realized is untouched: this auxiliary node is
   below its statement and steps, and no unit step or cited unit is bypassed.
5. Compared node JSON with the repository: the existing node changes only
   proof, proof_deps and proof_origin. Its three steps match the coefficient
   lift, inversion of reconstruction and evaluation calculation in Lean.
   The new node's statement matches its exact Lean signature, with source,
   complete proof route, proof dependencies, origin, searches, split status,
   creation and blueprint ancestry, chapter/unit and Lean record. Its
   dependency list is the union of its steps' uses. No cycle is introduced.

Second reading changed the new module’s redundant imports, expanded the new theorem's
natural-language proof, and made the dependency/pruning report explicit.
No signature, theorem conclusion, or unit route changed.

Dry-run repair: restored the item's original public imports after preflight
required a change record for their removal. The existing exported interface is
therefore identical; only the new module's redundant imports were pruned.
