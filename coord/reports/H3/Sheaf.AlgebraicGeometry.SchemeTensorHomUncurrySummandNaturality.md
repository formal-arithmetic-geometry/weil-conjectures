## What changed

Proved `AlgebraicGeometry.schemeTensorHomUncurry_summand_naturality` without changing its
statement or imports. The outer coproduct inclusion is evaluated with
`schemeTensorHomUncurry_component`. Proved private helpers implement braiding and
inverse tensor-Hom naturality, the fixed-source Hom projection equation, and their
composition. The final proof specializes this calculation to the inner tensor
inclusion and the resolution augmentation. Keeping the projection calculation abstract
avoids repeatedly unfolding its existence specification. All private helpers are proved.

The proof follows the existing node plan and its three existing dependencies. No new public
statement or definition is introduced. A scoped heartbeat setting permits the concrete
instance comparisons; compilation remains within the prescribed wall-clock limit.

## Proved and sorry left

Closed the single hole in `AlgebraicGeometry.schemeTensorHomUncurry_summand_naturality`
(node `lem-pc-scheme-uncurry-summand-naturality`). No holes remain in the item and no
holes were added. This is a proof, not a decomposition. It uses the already stated
Hom-complex projection specification and tensor-Hom APIs; their transitive assumptions
remain the responsibility of their existing nodes.

## No longer needed

None. Both original public imports are retained, and the original three proof-dependency
nodes remain used: `lem-pc-tensor-hom-uncurry-differential`,
`lem-sc-hom-complex-projections`, and `lem-pc-sheaf-modules-tensor-closed`.
No node or module is pruned, and no proof-only import was added.

## Where the brief, the DAG or earlier work was wrong

None. The statement requires no boundedness hypothesis. The computation uses only
`p + q = n` and `n + r = k`; it remains valid for zero objects and the empty scheme.
The existing component-naturality theorem specializes to maps between resolution
objects, so it cannot directly move the augmentation `F → I(F)` from an arbitrary
Hom complex. Its proved generic naturality calculation nevertheless supplies the
short route, reproduced as private helpers and specialized to this statement.

## Second reading by H3

1. Compared the complete delivered module against the repository with `diff -u`,
   and independently compared the public theorem signature as literal text. It is
   byte-for-byte unchanged. The only additions are five private proved helpers,
   scoped elaboration options, and the proof replacing the original `sorry`.
   No definitions, other modules, public imports, or hypotheses changed. Pass.
2. Compiled the delivered file with `lcompile.py`: clean, 51.6 seconds. Scanned the
   source for forbidden declarations and holes: none. A separate scratch copy
   prints axioms for all five helpers and the public theorem; the result is
   only `propext`, `Classical.choice`, and `Quot.sound` for each declaration
   (scratch compile: clean, 54.2 seconds). All local choices are of existing structural instances or of
   the existing Hom projection family; no new object is selected from an
   unproved arbitrary existence statement. Pass.
3. No split-off statements or holes were introduced. Read every private helper:
   `uncurry_natural` uses injectivity of the tensor-Hom equivalence and its three
   naturality laws; `uncurry_pre_post` specializes it twice;
   `evaluation_projection` reassociates and substitutes the projection equation;
   `postcomp_projection` specializes the existing projection naturality at the
   identity; `hom_evaluation` combines these calculations. Identity and zero maps
   cause no division, cancellation, or nonzero assumptions. Pass.
4. Read `CanonicalTensorHomUncurryDifferential`, `HomComplexProjections`, the
   tensor-closed API, and `CanonicalTensorHomUncurryComponentNaturality`. The last
   public theorem concerns maps between resolution objects and does not directly
   apply to the arbitrary augmentation here; its generic helper is private.
   Searched the library with `rg` and Mathlib through `msearch.py` using
   `uncurry.*naturality|homObjMap.*comp`. Existing naturality APIs are already used;
   no directly applicable shorter public theorem was found. Both public imports
   are needed by the unchanged signature (the chosen projections and the chain
   uncurrying map). No original proof dependency is unused. The unit record
   `sk-thm-picard-duality.json` has empty realized entries; this proof changes no
   unit statement or step and follows the existing node route. Pass.
5. Read `lem-pc-scheme-uncurry-summand-naturality.json` and the declarations of all
   three proof dependencies. Its step describes exactly the implemented outer
   component restriction, projection naturality, coefficient naturality, and
   source naturality. `proof_deps` remains correct; `proof_origin` cites the same
   calculation and requires no route correction. No new nodes are needed. Pass.

Changes by the second reader: clarified “no new statement” to “no new public
statement” in the report, since five private helpers were added by the first
worker; added this independent review. The Lean proof required no repair.
