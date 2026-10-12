## What changed

Repaired the landing refusal for duplicate statements. Removed the private declarations
`AlgebraicGeometry.Scheme.Modules.quotient_iso_of_eq`, `mapped_quotient_iso`, and
`subobject_filtration_of_closure`. Added the proof-only import
`import all Sheaf.CategoryTheory.FiniteFiltrationRefinement` and applied its existing
`CategoryTheory.subobject_filtration_of_closure` directly. The `all` modifier exposes
that module's private helpers to this proof without exporting them to importers.
No existing signature or visibility changed; no other module was adapted.
Change record: `coord/changes/coherentIntegralFiltration_of_shortExact.md`.

The proof converts the two coherent integral filtrations to an isomorphism-invariant
object property's filtration closure, applies its proved extension closure, reuses
subobject-chain realization, and proves coherence of all chain terms by induction.
Updated the target node's proof route and dependencies to record this reuse.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.coherentIntegralFiltration_of_shortExact`
(node `lem-weil-pbc-coherent-integral-filtration-extension`).
No sorry remains in the delivered module, and no new hole is added.
The proof uses the existing stated theorem
`AlgebraicGeometry.RingedSpace.coherent_kernel_cokernel_sum`; its upstream hole is
an intended stage-3 dependency, not a new hole in this delivery.

## No longer needed

Removed the direct proof-only import
`WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions`: the needed
machinery is available through the all-import of the refinement module.
The three duplicate private declarations listed above are no longer needed.
No DAG node or library module is pruned: the extension-closure module is still
needed transitively, and the existing refinement module is now reused directly.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery copied three private categorical helpers from an existing
module and was correctly refused by import_prune_check.py. Ordinary import does
not expose those private declarations; Lean's supported `import all` form does.
The repaired proof uses the existing helper instead of reproducing its proof.

The existing node `lem-pc-s3-finite-filtration-refinement` describes this helper's
construction in proof step 3. It is used as a categorical tool from another unit;
the present unit's extension step is preserved. No node of this unit already
provides that categorical realization interface. No new node is introduced.

The earlier second reading concerned the superseded duplicate-helper version;
a fresh independent second reading is required for this repaired delivery.

## Second reading by R2

1. I compared the delivered module with the repository version. The theorem signature and all
existing declarations are unchanged byte for byte; only proof-only imports, the unused universe
declaration, and the theorem proof differ.

2. I compiled the module with `lcompile.py`; it compiles cleanly and contains no `sorry`,
`axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. A scratch `#print axioms` reports
only the permitted foundational axioms together with `sorryAx` from the still-open upstream
coherence theorem used by this proof.

3. The proof introduces no split-off statements or new nodes. Its object-property construction,
filtration-closure conversion, extension step, and coherence induction are all well-typed and
use the existing declarations. The target statement is unchanged and remains exactly the
coherent-extension claim.

4. The route is pruned: the duplicate private categorical helpers are absent, and the existing
`CategoryTheory.subobject_filtration_of_closure` is reused through the proof-only `import all`.
The unit's extension-closure route and its realized refinement step are retained. The removed
public proof-only import and duplicate helpers are listed above under `No longer needed`.

5. The target node's `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof and no
new statement needs a node. Verdict: pass.

I changed only the unused universe declaration in the sandbox and added this independent review
record; no proof or interface repair was necessary.
