## What changed

Proved `AlgebraicGeometry.coherentFormalModule_annihilated_double_cokernel` with
its signature unchanged. The proof passes the cokernel bound through surjective
inverse-limit projections to every level, then checks ideal multiplication on
the affine cover. It actually establishes the scalar bound t before using
K^(2t) ≤ K^t for the stated conclusion.

Four private helpers are fully proved: `projection_surjective`, `product_qc`,
`formal_projection_surjective`, and `product_zero_on_affine_cover`.
Proof imports added: Mathlib's filtered-final and concrete-limit modules,
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`, and the
source-library `AffineHom` and `QuasicoherentCokernel` modules. Updated the item's
DAG proof, proof dependencies, and proof origin to match this argument.

The public List.TFAE import is pruned; the sole direct importer already imports
it publicly itself. Change record:
`coord/changes/coherent-formal-double-cokernel-imports.md`.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.coherentFormalModule_annihilated_double_cokernel`
(node `lem-weil-pbc-formal-systems-annihilated-by-power-cokernel`).
There are no sorries left in the delivered module and no new holes or nodes.
The proof uses the already stated affine ideal-product and tensor-sections
lemmas; any unproved dependencies remain their existing items, not new holes.
This is a proof from existing declarations, not a decomposition.

Validation: the complete module compiles without warnings via lcompile.py.
Checked empty cover/empty scheme, zero modules and morphisms, I=0 and I=O_X,
and K=0 and K=O_X: projection surjectivity, quotient lifting, and local
morphism detection apply unchanged, without choosing arbitrary objects from
unproved existence statements. The original importer is checked separately
against the sandbox overlay. The delivery dry run performs the axiom probe
and mechanical preflight; no push is requested.

## No longer needed

Removed imports (relative to the assigned module):

- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`
  (`lem-weil-pbc-coherent-formal-modules-affine`).
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`
  (`lem-weil-pbc-coherent-formal-modules-abelian`).
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`
  (`lem-weil-pbc-coherent-formal-modules-local-exactness`).
- `Sheaf.RingTheory.AdicCompletionNoetherian`
  (`lem-weil-pbc-adic-completion-noetherian`).
- `Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal`
  (`lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal`), the original sole proof dependency.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`: redundant direct
  import, publicly re-exported by the retained proof import QuasicoherentCokernel.
  Its kernel-closure declaration is still used and its node remains a proof dependency.
- `Mathlib.Data.List.TFAE`: unnecessary for this statement or proof.

The first five nodes/modules are unnecessary for this cokernel component;
this does not claim they are globally unreachable or unnecessary for the
sibling kernel component. The affine-completion, formal-category abelianness,
local-exactness and scalar quasi-inverse reductions are all avoided here.
The unit's own statement and realized steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG's proposed reduction-modulo-an-ideal route is longer than necessary
for the cokernel half. Surjective projection of G's affine section system is
enough: cokernel annihilation descends directly. The kernel hypothesis remains
in the unchanged signature but is not needed by this proof. No mathematical
statement was disputed or weakened.

Searches: leanfinder for coherent formal cokernel annihilation, loogle for
Module.annihilator, and msearch grep plus source rg for sequential projection
surjectivity and ideal-product vanishing. The useful Mathlib result was
Concrete.surjective_π_app_zero_of_surjective_map, extended to arbitrary n by
an initial shifted diagram. Source checked: Stacks Remark 0888, implication
(3) => (1), https://stacks.math.columbia.edu/tag/0888. The existing docstring
is preserved; the proof body and DAG record explain the shorter route.

## Second reading by D4

1. Interface: PASS. Read the whole repository/sandbox diff. The existing theorem's
   signature and docstring are byte-for-byte unchanged; no definition is changed.
   The only public-import removal is List.TFAE, recorded in the change record.
   The sole direct importer already publicly imports it. Compiled that importer's
   unchanged repository source together with the delivered module in scratchpad,
   in import order, against actual sandbox compiled outputs: both passed.
2. Proof: PASS. Independently compiled the delivered module without warnings.
   Added `#print axioms` in a scratch copy for projection_surjective, product_qc,
   formal_projection_surjective, product_zero_on_affine_cover, and the public
   theorem. Every result lists exactly propext, Classical.choice, Quot.sound;
   none uses sorryAx. No sorry, forbidden trust construct, or new definition
   occurs. The witnesses obtained from surjectivity are used in proofs only.
   In particular the formal-system quotient isomorphism is existing object data,
   not a new arbitrary object constructed from an unproved existence theorem.
3. Split statements: PASS, none added or left. The four private helpers are proved.
   Checked the shifted tower at n=0, quotient lifting for zero modules, scalar
   powers for K=0 and K=O_X, and empty-cover local detection. The argument needs
   only the cokernel half of h; retaining the kernel half and ht preserves the
   contract. No smaller case is silently excluded.
4. Route and pruning: PASS. Independently searched with msearch grep for
   surjective limits/ideal-product zero and rg over both Lean roots. The existing
   tower_limit_projection_surjective is for Functor.ofOpSequence, whereas this
   proof directly shifts an arbitrary diagram and uses the shorter Mathlib
   concrete-limit lemma. The similar product-closure helpers elsewhere are
   private, so cannot replace product_qc. All added imports serve proofs and are
   plain imports. Every removed import is listed above; the sole old proof_dep,
   kernel-cokernel-annihilated-mod-ideal, is included. Read sk-thm-p1.json:
   none of its realized statement/step nodes is removed or bypassed; the change
   is below that unit's prescribed route.
5. Nodes: PASS. The node differs only in proof, proof_deps, and proof_origin.
   Its unchanged lean.statement matches the existing theorem. Checked the six
   proof dependencies against their declarations and the actual uses: coherence
   to quasi-coherence, ideal powers, tensor sections, kernel/cokernel closure,
   and affine cokernel sections. The proof_deps list is exactly the union of
   the step uses. No new node is required for an open statement, since none exists.

Second reading changed only this report. No Lean proof, signature, import, node,
or change-record repair was necessary. Independently verified one original hole
closed, zero holes added, and no dependency on sorryAx in the completed theorem.
