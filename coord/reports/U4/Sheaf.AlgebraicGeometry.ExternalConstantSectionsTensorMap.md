## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.Modules.exists_external_constant_sections_tensor_map`
with an explicit reduction to balanced section equivalences. Its existing signature is byte-for-byte
unchanged. Added the proof-only import `Sheaf.AlgebraicGeometry.PicardConstantTensorBalancedSections`
and its new intermediate module. The proof composes each equivalence with
`externalSectionsComponent`, proves structure-ring linearity by tensor induction, and assembles the
components using restriction compatibility. No definition or existing public signature changed.

## Proved and sorry left

Closed the original body hole of
`AlgebraicGeometry.Scheme.Modules.exists_external_constant_sections_tensor_map`
(node `lem-sc-external-constant-sections-tensor-map`). Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_picard_constant_tensor_balanced_sections`
(node `lem-sc-picard-constant-tensor-balanced-sections`). This is a decomposition: one hole closed,
one added, net zero holes in this delivery. The original theorem still depends on `sorryAx` through
the new lemma and upstream imports; it is not an axiom-free completed proof.
There are no other new holes, and no data definitions in the delivery.

## No longer needed

No import or module was removed. The old proof dependency
`lem-sc-picard-constant-sections-tensor-basis` is replaced in the item's `proof_deps` by
`lem-sc-picard-constant-tensor-balanced-sections`: the proof uses the tensor coefficient definition
from that module, but not its basis theorem. The new node still depends on that coefficient
construction. The other old dependencies, `lem-sc-external-sections-components` and
`def-sc-field-linear-module-cohomology-operations`, remain used. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first report called the target proved without distinguishing a decomposition from an
axiom-free proof. Its sandbox omitted the changed item node, and the new node's `lean.statement`
contained only the theorem name, not the signature. These are repaired. The balanced-section
argument must identify the chosen presheaf left adjoint with pointwise scalar extension by a Hom
universal property; this is not a definitional unfolding. The new lemma's docstring and node now
include that identification. The compiler also required an explanatory comment for the increased
heartbeat budget, now supplied. The first delivery dry run rejected module-level scope commands;
the added elaboration options were localized to the theorem and its tensor terms use qualified
`TensorProduct.tmul`, leaving the original module-level commands unchanged.

## New nodes

`lem-sc-picard-constant-tensor-balanced-sections`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-constant-tensor-balanced-sections.json`, states the
additive section equivalences with exactly the scalar and restriction identities used by the
reduction. It makes no reference to X, F, the external section map, or the comparison of bijectivity,
so it is a strictly lower algebraic step rather than a renamed restatement. No change record is
needed: no existing statement or definition changed.

## Second reading by U4

1. Compared the delivered item module with the repository using `diff`, and separately checked the
   entire existing theorem signature byte-for-byte. Verdict: unchanged field, universe, scheme,
   structure morphism and module parameters; unchanged presheaf morphism and bijectivity iff.
   The only new public declaration is the separate algebraic lemma. No existing definition changed.
2. Read the complete reduction. `Hom.app_smul` and `tmulSection_smul` establish second-factor
   structure-ring linearity on pure tensors; tensor induction extends it. The naturality equation
   is exactly `externalSectionsComponent_naturality` after the balanced restriction equation.
   `AddEquiv.bijective.of_comp_iff` proves the iff. Both modules compile locally. The only new
   `sorry` is the named, documented intermediate theorem. No forbidden declaration, inline data
   hole, or arbitrary witness-based data definition occurs. Choosing e inside an existential proof
   does not define data for downstream users. Axiom probes are recorded below.
3. Read the new statement and all its clauses against its docstring. It is true for arbitrary G,
   including non-quasi-coherent G: the tensor is a presheaf tensor, not a sheafified tensor whose
   sections might differ. On V = empty the modules are zero; for M = 0 or G = 0 both sides are zero.
   For M = k it reduces to the unit action on G(V). The inverse formula and balance prove the
   scalar identity, while the ring restriction and G restriction prove the displayed naturality.
   The docstring now includes the Hom equivalence identifying the abstract pullback, followed by
   mutually inverse tensor maps. Read Mathlib's Presheaf/Pullback and TensorProduct/Tower, searched
   lean/Sheaf with constant/tensor/balanced terminology, and independently ran LeanFinder, Loogle,
   grep and LeanSearch. LeanSearch returned Internal Server Error; Loogle did not resolve the
   cancellation identifier, while local grep found `AlgebraTensorModule.cancelBaseChange` and
   `Adjunction.leftAdjointUniq`. These are ingredients, not the needed natural presheaf comparison;
   formalizing that identification is not a short closing repair. No duplicate exact lemma found.
4. Read the item node's original route and `dag/units/sk-prop-av-cube.json`. Its `realized.statement`
   and single `realized.steps` entry are empty; no realized step is removed. The reduction follows
   the planned balanced-map/external-component construction and avoids the unused basis theorem.
   All original imports are used in signatures; the new import is proof-only. No module pruned.
5. Updated the item's proof, proof dependencies and origin to name the actual balanced lemma,
   external component naturality and scalar/tensor operations. The new node now records the full
   Lean signature, the two compatibility clauses, source, construction proof, searches, creation,
   chapter, unit and blueprint ancestry. Read Stacks Tag 0BED at
   https://stacks.math.columbia.edu/tag/0BED: it supplies the degree-zero tensor coefficient context,
   not a quoted general presheaf theorem. The expanded algebraic proof is explicitly agent-written
   and uses no geometric hypotheses from its Kunneth isomorphism assertion.

Second reading changed the heartbeat explanation, localized proof elaboration options and
qualified tensor terms, the intermediate proof docstring, both node records, and this report. The working Lean reduction and all existing signatures were retained.

Axiom probes: both `exists_external_constant_sections_tensor_map` and
`exists_picard_constant_tensor_balanced_sections` report exactly `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`. The scratch probe was removed before delivery.
