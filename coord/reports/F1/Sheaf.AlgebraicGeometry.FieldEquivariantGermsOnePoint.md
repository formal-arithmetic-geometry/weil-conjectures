## What changed

Proved `AlgebraicGeometry.Scheme.onePoint_selected_lift_section` in
`Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePoint`, preserving its signature.
Added the proved private helper `onePoint_field_model` to identify the selected
one-point scheme with a finite separable intermediate field of Ks.

Added proof-only imports of
`Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants`,
`Sheaf.AlgebraicGeometry.GeometricPointMorphismStalkBijection`, and
`Mathlib.FieldTheory.AlgebraicClosure`. No public import or existing signature changed.
Updated the selected-lift node's proof and proof dependencies to match the Lean proof.

The proof constructs the relative algebraic closure A of K inside Omega, compares
its stalk to the Omega-stalk, and applies the existing invariant-section theorem
at A. It proves compatibility with rho on arbitrary germ representatives. Covariance
of f makes its selected value invariant under the finite subfield's fixing subgroup;
the invariant-section theorem gives a section which is pulled back to X.

## Proved and sorry left

Closed the sole remaining hole:
`AlgebraicGeometry.Scheme.onePoint_selected_lift_section`
(node `lem-exc-field-equivariant-germs-one-point-selected-lift`).
The private helper `onePoint_field_model` is also proved without sorry.

There are no sorries left in the item's module and no new holes or modules.
The already proved propagation and full one-point reconstruction remain unchanged.
This is a proof from existing stated dependencies, not a decomposition introducing
new obligations. The imported `fieldSections_stalkInvariants` and
`geometricPointMorphism_stalk_bijection` still contain their existing sorries;
this delivery closes neither of those dependencies.

## No longer needed

None: no imports, nodes, or modules were removed. The finite-field reconstruction
route is retained. Its geometric identification is proved directly from Mathlib,
without adding an import of `EtaleFibreDiscreteSeparablePoints`.

## Where the brief, the DAG or earlier work was wrong

The selected-lift node's previous single-step plan omitted the algebraicity mismatch:
`fieldSections_stalkInvariants` assumes `Algebra.IsAlgebraic K Omega`, but this item
does not. The proof resolves it by constructing `algebraicClosure K Omega` and using
`geometricPointMorphism_stalk_bijection`. The added dependency is a generic stalk
comparison tool from another unit, not a replacement of this unit's route.
The unit record `sk-prop-h2` has no realized statement or steps bypassed here.

Sources read: Stacks Tags 04JM, 03QW, and 04FN, on their official web pages because
the referenced local TeX file is absent on this machine. Searches were performed
through msearch (LeanFinder, Loogle, grep) and rg in the library and Mathlib.
The proof covers imperfect K and transcendental Omega; it uses no algebraicity
assumption on Omega. For separably closed K the fixing subgroup and invariance
argument specialize correctly; empty schemes are excluded by the existing
Nonempty hypothesis, and no multi-component gluing is asserted.

## Second reading by F1

1. Compared the delivered module with the repository version. Existing declaration
signatures, including `onePoint_selected_lift_section` and the propagation and
reconstruction theorems, are unchanged byte for byte; only proof imports, a private
helper, and proof bodies differ. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds with no errors. Searched the
file for forbidden constructs and found no `axiom`, `unsafe`, `opaque`, `extern`,
`implemented_by`, or `sorry`; the private helper and the selected-lift theorem are
fully proved. Verdict: pass.

3. The delivery adds no split-off statements or nodes. The existing selected-lift
node remains the exact target statement, and its DAG proof and dependencies match the
imports and declarations used by the proof. Verdict: pass.

4. The proof follows the unit route: it uses the invariant-section theorem after
constructing the relative algebraic closure and the stalk bijection, then models the
selected one-point scheme by a finite separable intermediate field and pulls back the
section. No obsolete import or proof dependency was found. Verdict: pass.

5. Reviewed the node metadata and unit linkage. The node's `proof`, `proof_deps`, and
`proof_origin` describe the implemented route, and the unit's realized route is kept.
Verdict: pass.

Changed after this reading: added this second-reading record only; no Lean source or
DAG changes were needed.
