## What changed

Proved RingTensorCohomology.baseLocalization_comparison_aux without changing its
statement or existing public imports. Added two proof-only imports:
Sheaf.Algebra.Homology.BaseLocalizationOrdinaryComparison and
Sheaf.Algebra.Homology.BaseTensorLocalizationHomologyNaturality.
Both new modules are completely proved. The first constructs the ordinary
localization chain map and proves its counit comparison square. The second
proves the ordinary tensor-to-D chain square by tensor induction and transports
it through exact restriction/forgetful homology. It reuses the already-proved
private forgetHomologyMap and forgetHomologyIso_comp API with a proof-only
`import all Sheaf.Algebra.Homology.SemilinearScalarExtensionHomologySquare`.
No existing definition, theorem signature, public visibility or other module changes.

The auxiliary combines these two results with both localized_eq fields and the
extension/restriction unit formula. The original node now records this actual route.
Source checked: Stacks perfect.tex, Tag 0DJ8,
lemma-single-complex-base-change-condition, including its affine localization
identity; more-algebra.tex, Tag 06Y6, lemma-derived-base-change and its proof.
The source files were obtained in the sandbox scratchpad because this checkout
contains the literature lists but not these TeX files. Blueprint unit
sk-thm-picard-semicon has no realized nodes here; its route was preserved.

## Proved and sorry left

Closed the sole original hole:
RingTensorCohomology.baseLocalization_comparison_aux
(node lem-pc-base-localization-comparison-aux).

Also proved, with no holes:
RingTensorCohomology.exists_baseLocalization_ordinaryComparison
(node lem-pc-base-localization-ordinary-comparison), and
RingTensorCohomology.baseTensorLocalization_homology_naturality
(node lem-pc-base-tensor-localization-homology-naturality).

Holes closed: 1. Holes added: 0. No sorry remains in any delivered module.
This is a proof, not a decomposition into further unproved statements.
All three modules compiled individually within the 60-second file limit.
Compilation and axiom checks are performed again by the delivery dry run.
The proofs use arbitrary supplied models, not existence/choice of a model.
The only existence witness constructed is the explicit ordinary chain map.

Edge cases: no comparison invertibility or flatness of D is used. Zero modules,
zero complexes and zero D follow from the same additive identities. If S contains
zero, the ordinary localization isomorphism still constructs the unique maps.
The ordinary square does not require the D scalar towers; the homology transport
requires only the two B-to-D towers and does not require Rp to localize R.

## No longer needed

No existing public import was removed. The new ordinary-square module omits the
redundant direct RingTensorCohomology import; BaseLocalizationMap exposes its
restrict/extend definitions. The new homology-naturality module needs only the
model publicly, plus the proof-only semilinear homology helper import.

Removed lem-pc-base-localization-comparison from the auxiliary node's proof_deps.
Its module Sheaf.Algebra.Homology.BaseLocalizationComparison imports this auxiliary,
so it cannot be imported back here. That parent remains needed by the targets;
no globally unreachable module is claimed pruned. Neither BaseLocalizationIso nor
BaseLocalizationNaturality nor any additional K-flat resolution theorem is imported
for this proof.

## Where the brief, the DAG or earlier work was wrong

The auxiliary node's sole planned proof dependency was its parent comparison,
which already uses the auxiliary. It was a backwards proof dependency, not an
available proof lemma. Its textual plan is correct, and is now implemented via
the ordinary universal-counit square and ordinary coefficient homology naturality.
The original auxiliary docstring and signature were preserved. The unused
section-variable linter is suppressed only for this theorem because its original
A-to-D hypotheses are deliberately retained; transparency options are also local
to its proof.

LeanSearch returned an Internal Server Error; it is recorded as unavailable.
LeanFinder, Loogle, Mathlib source grep and full project searches were used.
The generic exact-homology helper API already existed and is reused rather than
restated or reproved. No statement was disputed and no forced adaptation is needed.

## New nodes

lem-pc-base-localization-ordinary-comparison, in
Sheaf.Algebra.Homology.BaseLocalizationOrdinaryComparison: the ordinary B-linear
comparison square and its explicitly constructed chain map, before tensoring to D.
It is proved completely; it introduces no hole or new definition.

lem-pc-base-tensor-localization-homology-naturality, in
Sheaf.Algebra.Homology.BaseTensorLocalizationHomologyNaturality: the ordinary
coefficient-chain square transported to homology through the two restriction
isomorphisms. It is proved completely and uses no derived counit or comparison.
No change record is needed because existing interfaces are unchanged.

## Second reading by Y3

1. Compared the delivered auxiliary module with the repository version. The
   theorem signature, hypotheses, conclusion, and existing public imports are
   byte-for-byte unchanged; only the proof and proof-only imports changed.
   Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py`; no errors, warnings,
   `sorry`, forbidden declarations, or hollow definitions remain. The proofs use
   only the permitted axioms. Verdict: pass.
3. Checked the two split-off declarations against repository and Mathlib searches.
   Their statements are independent intermediate squares, strictly simpler than
   the target, true in zero and degenerate cases, and each has a matching node
   and source docstring. Verdict: pass.
4. Checked the route from the target downward. The circular parent dependency was
   removed; the ordinary counit square and homology naturality are the shortest
   available route, and no unused public imports were removed. Verdict: pass.
5. Compared each node's proof, proof dependencies, origin, and Lean declaration
   with the actual proofs. The unit route and realized declarations are retained;
   the auxiliary node now records both intermediate nodes. Verdict: pass.

I changed only this report section; no Lean statements or definitions were changed
 during second reading.
