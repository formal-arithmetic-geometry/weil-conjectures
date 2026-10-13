## What changed

Replaced the sole sorry in `AlgebraicGeometry.koszulCechComparison_isIso` by a complete
Lean proof from two finite-stage statements. The signature is unchanged. The second reading updated the proof docstring to name
the finite-stage statements actually used.
The proof establishes bijectivity of every component, then invokes
`HomologicalComplex.Hom.isIso_of_components`. Injectivity uses the kernel-zero criterion,
Mathlib's representation of elements in a filtered colimit, and `colimit.w`; surjectivity uses
the stage-lifting statement and `colimit.ι_desc`. The preservation instance is explicitly
shrunk to indexing universe zero, so the proof works for every universe of A.

Added `Sheaf.AlgebraicGeometry.KoszulCechStageLifting` and
`Sheaf.AlgebraicGeometry.KoszulCechStageKernel`, each with one public statement, a full proof
in words, and a matching node. Their conclusions concern finite-stage cocone legs, not the
comparison map or its invertibility. Updated the item's proof route and dependencies.
The unit record has no binding realized node at this item; the localization route is retained.

The three sandbox modules compile together. All additional imports in the item are proof-only.
No definition, existing statement, public import, or other group's module was changed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.koszulCechComparison_isIso`
(node `lem-sc-koszul-cech-comparison-is-iso`). No sorry remains in the item's module.

Added two holes, exactly the named public theorems:

- `AlgebraicGeometry.koszulCechCocone_stage_lifting`
  (`lem-sc-koszul-cech-stage-lifting`): each target cochain has a finite-stage lift.
- `AlgebraicGeometry.koszulCechCocone_stage_kernel`
  (`lem-sc-koszul-cech-stage-kernel`): a finite-stage cochain with zero image dies later.

This is a decomposition: one original hole closed, two lower holes added; it is not a
sorry-free proof of the mathematical comparison. Existing holes in imported construction
modules are untouched. Both new statements were checked on r=0, r=1, F=0, arbitrary integer
degrees, nilpotent or zero generators, and unbounded complexes. Finiteness is only of the
subsets indexing a total degree, not of the modules of coefficients.

## No longer needed

The second reading removed the redundant proof-only import
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`; compilation confirms its
API is already available through the retained imports.

Removed the proof-only import `Sheaf.AlgebraicGeometry.AffineKoszulHomAlternatingCech`
and the direct proof edge to `lem-sc-affine-koszul-hom-alternating-cech`. Its existential
comparison is not used. This route also needs no separate alternating-Cech computation or
multiplication-colimit isomorphism theorem: the lower statements use localization existence
and zero detection directly from Mathlib.

Consequently this comparison branch needs neither `Sheaf.Algebra.Homology.HomComplex`,
`Sheaf.AlgebraicGeometry.AlternatingCechComputes`,
`Sheaf.RingTheory.ModuleLocalizationFilteredColimit`, nor
`Sheaf.Paper.ShiftedKoszulAugmentation`; their associated planned nodes
`def-pur-hom-complex`, `lem-pc-alternating-cech-computes`,
`lem-sc-module-localization-filtered-colimit`, and `def-pc-shifted-koszul-augmentation`
are not proof dependencies of this reduction. Other branches may still need them.
`Sheaf.Paper.KoszulComplex` and the explicit Koszul open system remain needed by the
construction; they are not pruned.

## Where the brief, the DAG or earlier work was wrong

The cited `affineKoszulHomAlternatingCech` theorem is not the specified comparison theorem.
Its diagram is constrained only objectwise: no transition formula is in its statement.
Its target identifications and comparison are existential, with no fraction/sign condition
on the morphism. Moreover it is an additive-group comparison, whereas this item's comparison
is A-linear. Its assertion cannot identify the actual cocone map used here. The new finite-stage
statements supply exactly the two missing localization properties of that actual cocone.

The affine node also cites Tag 0911 as the Koszul fraction-map construction; the current
Stacks Tag 0911 is a Tor/Artin–Rees statement. The relevant source is Tag 08D0, followed by
08D1 for total complexes. Read these sources directly at
https://stacks.math.columbia.edu/tag/08D0 and https://stacks.math.columbia.edu/tag/08D1;
the documented literature file is absent on this machine. New proof texts cite the correct tags.
The sign/differential verification is already supplied by the existing cocone construction;
the new finite-stage proofs use only invertibility of the sign.

`blueprint_refs.py ancestor lem-sc-koszul-cech-comparison-is-iso` returns None because the
created.item chain contains a module name, rather than a node id. New nodes inherit the
recorded nearest blueprint ancestor `lem-sc-finite-duality` through the existing node's
blueprint provenance, without editing that provenance or any unit/chapter record.

## New nodes

`lem-sc-koszul-cech-stage-lifting`, in
`dag/nodes/sec-picard-framework/lem-sc-koszul-cech-stage-lifting.json`, states finite-stage
lifting for the specified cocone. Its proof chooses finitely many localization numerators,
raises them to a common positive exponent, and extends them on the ordered exterior bases.
Source: Stacks 08D0 and 08D1. Searches: LeanSearch unavailable; LeanFinder found only generic
single-cochain lemmas; Loogle found generic bijectivity/isomorphism criteria; Mathlib and
project grep and blueprint search found no statement about these specified cocone legs.

`lem-sc-koszul-cech-stage-kernel`, in
`dag/nodes/sec-picard-framework/lem-sc-koszul-cech-stage-kernel.json`, states eventual
vanishing of a finite-stage element with zero cocone image. Its proof applies localization
zero detection to every exterior-basis coordinate and takes one exponent killing all of
them. Source and search results are as above. These are independent parts of the localization
argument, with a complete Lean proof combining them in the original module.

No change record is needed: no existing interface was changed and there are no adaptations.

## Second reading by V4

1. **Interfaces — pass.** Diffed the existing module and parsed the existing node
   against the repository. The theorem signature is byte for byte unchanged;
   there are no definition, visibility, public-import, or other-module adaptations.
   The existing node changes only proof, proof_deps, and proof_origin. Each new
   module has its own statement and node; no change record is needed.
2. **Kernel proof — pass as a decomposition.** Compiled all three files locally
   in import order. A scratch copy printed axioms for all three declarations:
   exactly propext, Classical.choice, Quot.sound, and sorryAx. The original
   theorem has no sorry; the only two new holes are the reported named theorems.
   No axiom, unsafe, opaque, extern, implemented_by, or hollow definition is added.
   Read the colimit representation, zero-kernel argument, cocone factorization,
   and componentwise isomorphism proof. They prove the unchanged conclusion.
3. **New statements — pass.** Read the actual diagram's object/transition formula,
   cocone fraction formula, exterior diagonal transition, and principal Čech
   terms. The lifting and eventual-kernel claims are distinct, strictly partial
   localization claims, not renamed copies of the comparison theorem. Checked
   r=0 (empty coordinates), r=1 (one localization), zero coefficient complexes,
   zero/nilpotent generators, arbitrary integer degrees and unbounded complexes.
   For fixed total degree there are only finitely many nonempty subsets; a common
   denominator or killing exponent therefore exists without finite generation
   of the coefficient modules. Read Stacks Tags 08D0 and 08D1 directly. Repeated
   searches with “sequential colimit”, “later transition kills”, isLocalizing,
   and affine restriction/power terminology. Mathlib and upstream have generic
   colimit and affine localization tools, not these specified-cocone statements.
   Neither remaining hole can be closed in a few minutes: the missing formal
   work is the coordinate transport through exterior bases and sheaf localization.
4. **Route and pruning — pass after import cleanup.** The old sole proof edge
   lem-sc-affine-koszul-hom-alternating-cech is explicitly reported as unused.
   Its existential objectwise additive-group comparison does not identify this
   A-linear diagram or cocone. The two localization clauses retain the intended
   Koszul-to-Čech route. The unit sk-thm-picard-duality has empty realized statement
   and step lists, so no binding realized step is bypassed here. Removing the
   ConcreteCategory.Basic import still compiled and printed the expected axioms;
   removing ModuleCat.FilteredColimits additionally failed to synthesize the
   required preservation instance, confirming that import is needed.
5. **DAG — pass.** Checked that proof_deps is exactly the union of step uses;
   the existing route matches the two theorem applications and Mathlib argument.
   Both new nodes have source, complete proof text, search records, provenance,
   creation record, matching chapter/unit and verbatim Lean signatures. Their
   construction dependencies supply the formulas used by their written proofs.

Changed only the redundant proof import, an extra blank line, and the existing
proof docstring's obsolete citation to the pruned affine theorem; updated this
report accordingly. No mathematical statement or proof term was changed.
The delivery remains one original hole closed and two lower holes added, hence
net -1 holes for this reduction, not a completed sorry-free comparison proof.
