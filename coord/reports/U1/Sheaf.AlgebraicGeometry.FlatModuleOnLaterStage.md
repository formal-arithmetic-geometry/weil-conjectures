## What changed

Proved `AlgebraicGeometry.exists_flat_module_on_later_stage` without changing its
signature or docstring. Added proof-only imports of FinitePresentationModuleMapDescent,
FlatModuleDescentAffineCharts, AffineFlatModuleDescent, and TensorPullbackFinitePresentation.
Finite-presentation descent supplies the first model; the finite affine argument supplies
one flat later stage; the explicit tensor composition isomorphism supplies the final
comparison with M. Five fully proved private helpers handle sectionwise flatness transport,
cartesian-model comparison, and eventual flatness. Their proofs reuse the existing
PullbackModelFlatnessComparison and FlatModuleDescent arguments, whose modules cannot be
imported here. No definition, public statement, public import or other module changed.
The copied DAG node now records the declarations actually used by this acyclic proof.

Sources read: [Stacks 01ZR](https://stacks.math.columbia.edu/tag/01ZR),
[05LY](https://stacks.math.columbia.edu/tag/05LY), and
[02JO](https://stacks.math.columbia.edu/tag/02JO). These retain the blueprint unit's
Noetherian approximation of the finitely presented module and its relative flatness.
Searches via msearch: LeanFinder found only generic algebraic flatness results; Loogle
found `Module.Flat.of_linearEquiv`; grep found no direct descent theorem. Source searches
found the existing object descent and finite-chart/affine-flatness interfaces used here.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_flat_module_on_later_stage`
(node `lem-pc-flat-module-on-later-stage`), the sole original hole.
No sorry remains in the delivered module, and no hole is added. This is a proof from
existing declarations, not a new decomposition. Existing dependencies may still use sorry.
The private helpers are all proved, including the finite common-upper-bound argument.

## No longer needed

No existing imports were removed: the four public imports of the original file are
retained. The planned direct dependency `lem-pc-flat-module-descent` /
`Sheaf.AlgebraicGeometry.FlatModuleDescent` is bypassed at this item in favor of its
finite chart and affine algebra dependencies. `StagedModuleEventualFlatness`,
`FlatModuleDescentPreorderStage`, and `PullbackModelFlatnessComparison` are not imported.
The transport/composition work is fully proved locally; the original fibre-product,
tensor-pullback composition, and finite-presentation preservation nodes remain used.
No transitive chart or algebra dependencies are claimed pruned. No whole-library
unreachability is claimed: other items may still need the bypassed modules.

## Where the brief, the DAG or earlier work was wrong

The planned flatness interface cannot be imported: `import_direction.py may` reports
that FlatModuleDescent already reaches this item. A source-graph traversal gives
FlatModuleDescent -> DirectImage -> DirectImage.FiniteFreeComplex -> ProperFlatCechModel
-> ProperFlatCohomologyModel -> ProperFlatCohomologyProperties
-> ProperFlatFinitePresentationModel -> ProperFlatBoundedPresentationModel
-> ProperFlatAffineCechPerfectModel -> FiniteAffineCechModelPerfect
-> ProperFlatSingleDerivedDirectImagePerfect -> ProperFlatSingleOpenPseudoCoherent
-> ProperFlatSingleOpenNoetherianComparison -> ProperFlatSingleNoetherianDescent
-> FlatModuleOnLaterStage. StagedModuleEventualFlatness,
FlatModuleDescentPreorderStage, and PullbackModelFlatnessComparison have the same
umbrella DirectImage dependency. The module itself initially had no proof-dependency
imports. Its lower chart and algebra interfaces are acyclic, so the delivery uses
those and proves the transport and finite directed-bound glue explicitly.
No mathematical statement was changed or disputed; no new node was needed.
The first dry run flagged a changed global `open Opposite` command. It was removed;
all opposite-object names in the new proofs are explicitly qualified.
Local lcompile passed with exit code 0 and no warnings before this qualification cleanup.
The delivery tool also compiled the module and ran its per-declaration axiom probe;
no disallowed axiom was reported.

## Second reading by U1

1. Compared the delivered module with the repository version. The public theorem signature, docstring,
   and all existing declarations are byte for byte unchanged; only proof-only imports, private helpers,
   and the target proof were added. The node metadata records the route actually used.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. There are no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations in the delivered
   file. The proof uses only existing declarations and the permitted foundational axioms.
3. The target theorem remains exactly the planned statement. No split-off statement or new node was
   introduced by this delivery, so there is no extra claim to weaken or duplicate an existing result.
4. The proof follows the unit route: finite-presentation module descent, affine chart flatness
   descent, a finite common upper bound, and tensor-pullback composition. The cyclic direct-image
   flat-module route is correctly avoided; all proof-only imports are acyclic and needed.
5. Checked the DAG node against the Lean declaration and proof. Its `proof` and `proof_deps` name the
   declarations used by the implementation, and the unit and chapter fields are preserved.

Changed during this second reading: added this review record only; no Lean code, public signature,
node statement, or dependency was changed.
