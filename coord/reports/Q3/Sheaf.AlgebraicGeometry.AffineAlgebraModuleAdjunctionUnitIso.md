## What changed

Replaced the sorry in AlgebraicGeometry.affine_algebra_module_adjunction_unit_iso with
an explicit adjunction construction and transport of its unit. The private helper
adjunction_of_unit_formula proves both naturality laws and identifies the constructed unit.
Added the proof import Sheaf.AlgebraicGeometry.AffineModuleTensorHomBijective.
The existing public imports, theorem signature and docstring are unchanged.

The remaining tensor Hom-bijection calculation is stated in its own module, for arbitrary
scheme morphisms and all module sheaves. It asserts no isomorphism and assumes no
quasi-coherence or affineness. The main proof separately uses affine_module_correspondence
to obtain invertibility of β and explicitly transports it to the canonical unit.
This is a decomposition, not a claim of a net hole reduction.

## Proved and sorry left

Closed: AlgebraicGeometry.affine_algebra_module_adjunction_unit_iso
(new-affine-algebra-module-unit-iso), 1 of 1 original holes.
Added and left: AlgebraicGeometry.Scheme.Modules.affine_module_tensor_hom_bijective
(lem-sc-affine-module-tensor-hom-bijective), 1 hole, in the new module.
No other holes are left in the delivered files. The categorical helper is proved.
Net holes closed minus added: 0. Both modules compile locally without warnings.

## No longer needed

None of the original imports, nodes or modules is pruned: the affine module correspondence
is still needed for its tensor witnesses and for invertibility of β. The new Hom lemma
requires only the two comparison-unit formulas; no pushout proof, bε identity,
quasi-coherence preservation, α, equivalence of full subcategories, or functor map
formulas is needed in its argument. Those clauses remain in the existing correspondence;
this delivery does not remove their modules from that separately used theorem.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt left an anonymous evaluation sorry and did not compile:
its local adjunction core was an opaque have, and its rewrites did not unfold the
composed functor maps. Its full concrete tensor calculation remained unfinished.
The delivery replaces that anonymous gap by a sourced public statement and a matching node;
all naturality, unit identification, affine invertibility and uniqueness transport in
the item's module are actual Lean proofs.

Checked the new statement on zero rings, zero modules, empty opens and empty schemes:
its proof is a composition of universal Hom bijections and unit identities with no
nonemptiness assumptions. It is strictly the universal-property step of the argument,
independent of the affine quasi-coherent isomorphism step.

Read Stacks Tags 01SB, 0AVW, 008A and 008Y online; the referenced local .tex files are
absent on this machine. Blueprint search for tensor adjunction found no matching node.
The ancestor script printed None, but reading the existing from.node chain gives
lem-sc-finite-duality; the new record follows that chain. LeanSearch was unavailable
(HTTP Internal Server Error); LeanFinder, Loogle and grep searches ran and are logged.
The unit's realized lists are empty, and the original affine correspondence route is retained.

## New nodes

lem-sc-affine-module-tensor-hom-bijective: the specified β-induced Hom map is bijective
for the two scalar extensions on all module sheaves. Its source is the tensor elucidation
of Stacks 01SB, together with the component Hom adjunctions in Tags 008A and 008Y.
The docstring and node give the section calculation including equality transports and
cancellation of κ. No existing interface changes and no forced adaptations are required.

## Second reading by Q3

1. **Visible changes and statements.** Compared both delivered modules with `sheaf-dag`; the existing target signature and docstring are unchanged byte for byte. The only added import is proof-only, and the new public theorem has a separate node and statement.

2. **Proof and axioms.** Compiled both modules with `lcompile.py`; the target theorem has no `sorry`, while the new theorem is the sole named split-off `sorry`. No forbidden declarations or hollow definitions occur. The explicit adjunction helper constructs its naturality laws and unit formula, and the target proof transports invertibility through the unique-adjunction comparison.

3. **Split-off statement.** `affine_module_tensor_hom_bijective` is a genuine intermediate universal-property claim, strictly below the target and independent of affineness and quasi-coherence. Its docstring gives the section calculation and cites Tags 01SB, 008A, and 008Y; the node records the same statement, source, proof steps, and dependencies. Its zero, empty, and trivial cases are covered because the claim is purely a composition of Hom bijections.

4. **Pruning and route.** The affine correspondence remains imported and supplies the required tensor witnesses and invertibility of β. The added tensor lemma uses the comparison-unit formulas and does not introduce unused imports. The unit record has no realized route for this unrelated Picard-duality sketch, so no unit realization was removed or bypassed.

5. **DAG agreement.** The target node proof and `proof_deps` now name the correspondence and the split-off Hom-bijection node; the new node's Lean record names its theorem and module. The delivery is a decomposition with one original hole closed and one strictly simpler hole left.

I changed only this second-reading report section; no Lean statements or proofs were altered during review.
