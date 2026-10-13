## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel`
with an explicit construction and a complete Lean proof from named statements.
The signature, visibility and existing docstring are unchanged. Choose a finite
subcover of the inverse image of the specified affine open, reindex by `Fin r`,
and use `finiteAffineCechModel` of the restricted morphism and coefficient.
No complex is chosen from an unproved existence statement.

Added proof-only imports of `FiniteAffineCechModelFlatOver`,
`FiniteAffineCechModelComparison`, and the new `FiniteAffineCechModelPerfect`.
The first supplies relative flatness, the second the universal comparison.
The new module asserts only perfection of the fixed, explicitly constructed
complex for a supplied affine cover. Bounds and quasi-coherence are already
proved in `FiniteAffineCechModel`. The calculation of restricted relative
flatness is written directly using `morphismRestrict_appLE` and
`Scheme.Opens.ι_appIso`; no spectrum-chart round trip is needed.

Updated the item's DAG proof to these actual dependencies and added the
perfection node. The coherence unit's route (finite affine Cech construction,
proper perfection by Noetherian approximation, then perfect replacement) is
preserved. There are no signature changes or forced adaptations.

## Proved and sorry left

Closed the direct hole in
`AlgebraicGeometry.Scheme.Modules.exists_proper_flat_affine_cech_perfect_model`
(node `lem-pc-proper-flat-affine-cech-perfect-model`). There are no direct
sorries left in the item module.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.finiteAffineCechModel_perfect`
(node `lem-pc-finite-affine-cech-model-perfect`), in the new module
`Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect`. It proves only the
perfection clause for a specified finite affine Cech complex. This is strictly
part of the original argument: it supplies neither a model, bounds, termwise
flatness, quasi-coherence nor universal base-change isomorphisms.

This is a decomposition: one upper hole closed, one lower hole added, net zero.
The existing `finiteAffineCechModel_comparison` remains a dependency with its
own hole (node `lem-pc-finite-affine-cech-model-comparison`); it is not modified
or added by this delivery. Imported flatness and construction properties have
complete proofs. Both delivered modules compile through `lcompile.py`.

## No longer needed

No original import was removed, and no module is claimed to leave the targets'
import closure. The four original direct proof dependencies
`lem-pc-alternating-cech-computes`, `lem-pc-cech-computes`,
`lem-pc-flat-affine-base-change-sections`, and `lem-pc-rf-perfect-base-change`
are replaced as direct dependencies by the explicit finite-model interfaces
and the isolated perfection lemma. Their underlying mathematics remains
needed through those interfaces, so this is not a global pruning claim.

During simplification removed the trial proof-only imports
`Sheaf.AlgebraicGeometry.FlatOverAffineOpenRestriction`,
`Mathlib.RingTheory.Flat.Stability`, and `Mathlib.RingTheory.RingHom.Flat`:
the direct restriction calculation proves the needed flatness without them.
`lem-pc-flat-over-affine-open-restriction` is not needed by this proof.
No additional splitting nodes are introduced for cover selection or scalar
transport.

## Where the brief, the DAG or earlier work was wrong

The original plan's Cech and alternating-Cech signatures express comparisons
for cohomology/section complexes, rather than perfection of this specified
sheaf complex. `perfect_derivedDirectImage_baseChange` supplies proper
perfection, but assumes a derived-localization family on every scheme and
additive tensor pullbacks, whereas the item only supplies localization on U
and its localized open sites. Applying it directly does not close the
perfection clause: the derived augmentation comparison and localization
transport are still needed. The new node isolates precisely that clause.
The original theorem is mathematically consistent; no statement is disputed.

Read the actual signatures of the plan's four dependencies and the explicit
finite-model declarations. Searches: LeanFinder returned eight unrelated
hits, Loogle did not index the project `IsPerfect` notion, LeanSearch was
unavailable, and grep of both project roots and Mathlib found no fixed-model
perfection theorem. A blueprint search for `finite Cech perfect` returned no
matching blueprint node. The source statements and proofs were read at
Stacks Tags 0B91(2), 0A1H, and 01XD. The new docstring explains the augmentation
comparison and proper-perfect argument instead of inferring a derived
isomorphism merely from abstract cohomology isomorphisms.

Checked the new statement on: r=0 (covering forces empty inverse image),
empty U/zero ring (zero complex), identity f with a one-member cover
(finitely presented flat modules are locally finite projective), and
non-Noetherian affine U (0A1H supplies the necessary approximation).
No termwise finite-presentation claim is made for Cech sections.

## New nodes

`lem-pc-finite-affine-cech-model-perfect`, module
`Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect`: perfection only of the
explicit Cech complex for a specified affine cover of f^{-1}(U). The source
is the derived affine Cech comparison (01XB, 01XD, 01FK) followed by 0B91(2),
with the approximation argument of 0A1H. It inherits the item's chapter and
unit; the source and full proof are recorded in the node and docstring.
No change record is needed because no existing public interface changed.

## Second reading by S1

1. Compared the entire existing module with the repository using `diff -u`.
   The only changes are three plain proof-only imports and replacement of the
   theorem's `by sorry` body. The signature, visibility, options and existing
   docstring are byte for byte unchanged. Compared the existing node too:
   only `proof`, `proof_deps` and `proof_origin` differ. No definition, target
   statement or other group's module is changed. Verdict: pass.

2. Compiled both modules in import order with `lcompile.py --all`, including
   after the second-reading changes. Both compile cleanly (approximately
   4 and 8 seconds). Scanned both files: exactly one `sorry`, the named
   `finiteAffineCechModel_perfect`; no forbidden declarations or hollow
   definitions. The complex is `finiteAffineCechModel`, not a witness chosen
   from an unproved existence theorem. The finite subcover and its reindexing
   use proved library constructions. Scratch `#print axioms` checks of both
   declarations report only `propext`, `Classical.choice`, `Quot.sound` and
   `sorryAx`. The upper theorem therefore remains conditional on the new
   perfection hole and the existing comparison hole. Verdict: valid
   decomposition, not a completed axiom-free proof.

3. Read the new theorem, its node, the explicit model definition and
   `Scheme.IsPerfect`. Read Stacks 0B91(2), 0A1H, 01XD and 01FK directly.
   Properness plus locally finite presentation and quasi-compactness gives
   the finite-presentation assumption of 0B91(2); finite presentation of F
   supplies quasi-coherence, and hF supplies relative flatness. Restriction
   preserves these hypotheses. Separatedness over affine U makes finite
   nonempty intersections affine. The augmented acyclic resolution gives
   a derived comparison; cohomology isomorphisms alone would not suffice.
   The canonical chart in the explicit construction is an isomorphism on
   affine U, so it transports that comparison. Perfection is transported
   through each specified open-site localization, exactly as IsPerfect
   requires. Tested r=0 (covering forces empty source), empty U/zero ring
   (zero complex), the identity with a one-member cover (a finitely presented
   flat module is finite projective), and arbitrary non-Noetherian affine U
   (0A1H's approximation applies). The new lemma asserts only perfection of
   a specified complex and is strictly smaller than the existential item.
   Independent LeanFinder search for proper flat finite-presentation
   pushforward perfection, Loogle search for Scheme.IsPerfect, and searches
   in both Lean roots and the source checkout found no fixed-model theorem.
   Read `perfect_derivedDirectImage_baseChange`: its global localization and
   additive tensor-pullback hypotheses are not available here, and it still
   requires the fixed-model derived comparison. The remaining hole is not
   a few-minute application of that theorem. Verdict: true, needed split.

4. Read the finite-model bounds, quasi-coherence, flatness and comparison
   interfaces and the coherence unit record. The proof uses their exact
   conclusions, selecting a finite cover and proving restricted flatness
   directly by `morphismRestrict_appLE` and `ι_appIso`. It keeps the finite
   affine Čech construction followed by proper perfection/Noetherian
   approximation. The unit's `realized` field is currently empty and is
   unchanged; no realized unit step is bypassed. All four old direct
   dependencies are named in No longer needed, without claiming that their
   modules leave the global closure. The existing public imports serve the
   existing signature and remain unchanged. Reduced the new module's
   `Sections` import to `Basic`, which provides IsFlatOver and the required
   injective-resolution vocabulary; no Sections result occurs in its type
   or proof. Verdict: route preserved, imports repaired.

5. The existing node's three steps match the code: explicit cover/model and
   scalar flatness calculation; fixed-model perfection; universal comparison.
   Its proof_deps are exactly the named interfaces used. The new node has its
   source, proof, statement dependencies, searches, creation/blueprint/Lean
   records and the item's chapter/unit. Found that its first step cited
   `lem-pc-cech-computes` for an augmented derived resolution, while that
   statement gives only cohomology comparison. Replaced that citation and
   the separate affine-vanishing citation by `lem-pc-cech-resolution`, whose
   conclusion supplies a quasi-isomorphic augmentation, acyclic terms and
   the derived direct-image comparison. Read its Lean signature too. This
   existing node from the semicontinuity unit is used as a tool for the
   augmented resolution; no coherence-unit node states that derived
   comparison. The alternating comparison and proper-perfect node remain
   the second and third steps, with canonical chart/localization transport
   explicitly part of the argument. Updated proof_deps to the union of
   the actual uses. Verdict: DAG citation repaired.

Changes by the second reader: reduced the new module's public import from
Sections to Basic; added the new module docstring's source and blueprint;
corrected the new node's derived-resolution citation and proof_deps; wrote
this review. No proof body or existing statement was rewritten. One upper
hole closed, one new lower hole left: net zero, with no global module pruning
claimed. The only new hole is finiteAffineCechModel_perfect.
