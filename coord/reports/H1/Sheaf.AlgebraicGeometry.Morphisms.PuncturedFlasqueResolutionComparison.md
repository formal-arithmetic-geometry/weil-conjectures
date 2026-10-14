## What changed

Completed the proof of `AlgebraicGeometry.Scheme.punctured_flasque_resolution_comparison_maps`.
The proof uses the exact augmented restricted associated-sheaf resolution, termwise flasque
acyclicity, the existing acyclic-resolution comparison, and the degreewise sections-complex
isomorphism. Added proof-only imports for these APIs and delivered the two supporting modules
`PuncturedTildeResolutionExact` and `PuncturedTildeSectionsComparison`. Added the three DAG
nodes corresponding to the explicit restricted functor, exact augmentation, and sections
comparison. Recorded the required elaboration options in
`coord/changes/punctured-flasque-resolution-comparison-options.md`.

## Proved and sorry left

The item's theorem `AlgebraicGeometry.Scheme.punctured_flasque_resolution_comparison_maps`
is proved. Supporting declarations
`puncturedRestrictedAbelianFunctor_preservesZeroMorphisms`,
`punctured_tilde_resolution_exact`, and `punctured_tilde_sections_comparison` are proved.
No `sorry` remains in the delivered modules; no new holes were added.

## No longer needed

Repair B10/C5 reuses the proved public theorem
`AlgebraicGeometry.tilde_preserves_finite_limits` from
`Sheaf.AlgebraicGeometry.TildePreservesFiniteLimits`. Removed the duplicate private
`punctured_tilde_preservesKernel` proof and the direct proof import
`Mathlib.CategoryTheory.Preadditive.LeftExact`. The exact-resolution node now depends on
`lem-sc-tilde-preserves-finite-limits` instead of
`lem-weil-pbc-quasi-coherent-module-kernel`. Retained the `QuasicoherentKernel` import because
it supplies restriction-limit instances; its module is not pruned from the import closure.

No original proof dependency is pruned. The withdrawn earlier equivalent-statement core and
generic glue proposals are not delivered and introduce no library modules.

## Where the brief, the DAG or earlier work was wrong

The earlier core proposal restated the whole comparison theorem under an equivalent
`Nonempty AddEquiv` formulation and therefore was not a strict reduction. The delivered
route instead splits only the exact augmentation and sections identification, then combines
them with the existing acyclic-resolution and flasqueness APIs. The sections node metadata was
updated to contain its complete Lean statement.

## New nodes

`new-punctured-restricted-abelian-functor` records the explicit composite functor and its
zero-map preservation. `new-punctured-tilde-resolution-exact` records the quasi-isomorphic
augmentation before taking sections. `new-punctured-tilde-sections-comparison` records the
complex isomorphism after taking sections. Each node contains LeanSearch, Loogle or LeanFinder,
and grep searches.

## Earlier second reading (a previous round; superseded)

Repair of reviewer X-4a011's return at head 4a011fa99:
- B10/C5: replaced the copied private kernel argument with the existing public
  `AlgebraicGeometry.tilde_preserves_finite_limits` theorem, retained restriction-limit
  instances from `QuasicoherentKernel`, and updated the exact-resolution node's proof,
  dependencies, and proof origin to match this reuse.
- B9: corrected all three new supporting nodes' `blueprint.from.node` to the required
  ancestor `sbc-thm-spreading-finite-etale-galois`, with the complete seven-node `via` path
  specified in the return. Statements and definitions are unchanged.

1. Compared the delivered main module with the repository version. The theorem signature is
   byte-for-byte unchanged; only proof-only imports, transparency options, and the proof body
   changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no errors, no
   `sorry`, no forbidden declarations, and no `sorry` in a definition. Verdict: pass.
3. Checked the three split statements against their uses and edge cases (including arbitrary
   complexes, degree zero, and empty opens). Each is a strict reduction of the target and has a
   matching node, source, proof, and Lean declaration. Verdict: pass.
4. Checked the proof route against the unit record: it retains the exact augmented resolution,
   termwise flasque acyclicity, acyclic-resolution comparison, and sections-complex comparison.
   The imports are the APIs used by those steps; no original proof dependency is removable.
   Verdict: pass.
5. Checked DAG metadata, declaration statements, and the change record. The node statements
   match Lean verbatim, and the transparency-option change is recorded. Verdict: pass.

Changed only the proof and its required supporting modules/nodes, and added this second-reading
record; no statement or definition was changed.

## Second reading by H1

1. Compared each delivered module with the repository. The only existing Lean file is
   PuncturedFlasqueResolutionComparison; its theorem signature and visibility are byte-for-byte
   unchanged. The two supporting modules are new explicit constructions/proofs. No target,
   existing definition, or hypothesis changed. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py. Scratch-copy #print axioms checks
   cover the functor, its zero-map instance, the exact augmentation, sections comparison, and
   main theorem: only propext, Classical.choice, Quot.sound, with no sorryAx. No proof holes or
   forbidden declarations occur. No arbitrary witness from an unproved existence theorem is
   used: the augmentation and componentwise complex isomorphism are constructed. Verdict: pass.
3. No statements are left split off with sorry. The supporting exactness and sections statements
   are true, strictly smaller parts of the comparison and completely proved. Checked empty W,
   the zero ring, zero complexes, and degree zero: exact functorial transport and presheaf
   naturality apply uniformly. Fresh LeanFinder/Loogle searches and rg searches with
   quasi-isomorphism, restrictUnitIso, and image-top terms found generic APIs used here, rather
   than a direct replacement for these concrete statements. Verdict: pass.
4. Read the original proof dependencies and sk-prop-input-spreading realized fields (currently
   empty). The proof retains the exact augmentation, flasque acyclicity, acyclic-resolution
   comparison and sections identification. Both original dependencies remain used. Public
   imports support statement types; additional proof APIs are plain imports. The reported
   finite-limit theorem reuse avoids repeating the kernel argument. No unit route is bypassed.
   Verdict: pass.
5. Compared all node statements with their Lean signatures and checked proof steps, dependencies,
   origin, source, search records, chapter/unit and blueprint ancestry. The existing node differs
   only in proof, proof_deps and proof_origin. New nodes match the explicit functor and the two
   supporting theorems. Verdict: pass.

Changed the elaboration-options change record to name the direct importer
PuncturedFlasqueResolutionCohomology; no Lean proof, statement, definition or node was changed
in this reading. The item closes one existing hole; the supporting modules add zero holes.

The unchanged direct importer PuncturedFlasqueResolutionCohomology also compiles against the
delivered sandbox modules. The flasque-acyclicity step uses the upstream Sheaf.H theorem
recorded in the existing node's proof, avoiding its extra Sheaf.H' encoding comparison.
