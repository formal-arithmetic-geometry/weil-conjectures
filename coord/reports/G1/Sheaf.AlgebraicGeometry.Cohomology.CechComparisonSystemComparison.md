## What changed

Proved `exists_cechComparisonSystem_comparison` by defining the canonical degree-zero
morphism and zero morphisms in positive degrees. No imports were added or changed.
The copied DAG node now records this direct proof and has no proof dependencies.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Modules.exists_cechComparisonSystem_comparison`.
Added zero holes; zero statements split off. No `sorry` remains in the delivered module.

## No longer needed

Removed the old proof dependency `lem-sc-injective-cech-augmentation-quasi-iso`
(module `Sheaf.CategoryTheory.InjectiveCechAugmentationQuasiIso`) from this node.
It was not directly imported by this module; no imports were removed. That module
remains used elsewhere, including by `CechComparisonSystemExistence`, so no module
is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The planned injective-resolution argument is unnecessary because the statement imposes
only degree-zero normalization and no naturality, quasi-isomorphism, or connecting-law
conditions. Zero morphisms satisfy all positive degrees.


The sibling `cechComparisonSystem_comparison_connecting` is stated for an arbitrary
family of natural transformations, without normalization or a hypothesis tying it
to the augmented construction. Its docstring argument only applies to the constructed
family. This is a separate statement-review concern: the family delivered here is
not claimed to satisfy that law. No sibling statement or proof was changed.

## Second reading by G1

1. Compared the delivered Lean module with the repository using `diff`. The sole
   existing theorem signature is byte-for-byte unchanged; no definitions, visibility,
   hypotheses, or conclusions changed, and there are no change records.
2. Compiled the module locally through `lcompile.py`, with no errors or warnings.
   Scanned the complete file: no `sorry`, axiom, unsafe, opaque, implemented_by,
   or extern declarations and no data chosen from an unproved existence theorem.
   A scratch-copy `#print axioms` check showed only `propext`, `Classical.choice`,
   and `Quot.sound`.
3. There are no split-off statements or new nodes to review. The witness is explicit:
   canonical degree-zero map and zero maps at successors. These are natural
   transformations, as required. Empty covers (which force an empty scheme) and
   positive degrees impose no extra obligations in this signature.
4. The direct construction is the shortest route for this signature. The one import
   supplies the functors, canonical isomorphisms, and local instances used by the
   statement. No proof-only public import was added. The report now distinguishes
   a retired DAG dependency from a globally pruned module. Checked
   `dag/units/sk-thm-picard-rr.json`: neither this node nor the retired dependency
   realizes a statement or step there, so the unit route is preserved.
5. Checked the delivered node against the Lean: its proof describes the explicit
   witness, its empty `proof_deps` agrees with the elementary construction, and its
   `proof_origin` identifies the direct argument. The decoded Lean statement and
   every other node field agree with the repository. There are no new nodes.

Changed the inaccurate proof docstring to describe the actual construction, restored
literal Unicode in the node JSON, made the closed/added-hole counts explicit, and
corrected the pruning claim. The working proof was left unchanged. Recorded the
separate connecting-law statement concern above for the maintainer.
