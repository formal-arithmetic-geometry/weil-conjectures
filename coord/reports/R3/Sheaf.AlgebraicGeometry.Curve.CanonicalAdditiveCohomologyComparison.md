## What changed

The original theorem exists_canonical_additive_cohomology_square now has a compiled
Lean reduction to existing ordinary Cech comparison and one named etale-Cech hole. Its statement, etaleAdditiveSmul, etaleAdditivePullback and public imports
are unchanged. Added proof imports of AffineCechInverseImage, the new
EtaleAdditiveCechInverseImage, and Mathlib's affine morphism/intersection tools.
A fully proved private helper constructs common-index finite refined affine covers,
including empty target opens. Compose the etale-to-Cech comparisons with the existing
ordinary affine Cech linear isomorphisms. Their linearity and the identity scalar
homomorphism for toSpecGamma prove multiplication compatibility; substituting matching
cycle classes into the ordinary inverse-image identity proves the desired square.

## Proved and sorry left

Closed the original direct hole in
AlgebraicGeometry.Scheme.Modules.exists_canonical_additive_cohomology_square
(node lem-pbc-canonical-additive-cohomology-square). There are no direct sorries in
the item's module. The private exists_refined_affine_covers is fully proved.

Added one hole:
AlgebraicGeometry.Scheme.Modules.exists_etaleAdditive_cech_inverseImage,
node lem-pbc-etale-additive-cech-inverse-image, in the new module
Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechInverseImage.
This is a decomposition: one upper hole closed, one strictly narrower etale-to-Cech
hole added, direct-hole net zero. This is not a claim of closure-wide progress;
the pinned sorry ledger decides that after accounting for all dependency imports. It does not restate the original theorem: its targets are Cech
homology, it supplies matching section cocycles, and it asserts no ordinary Ext
pullback square. The ordinary comparison, simultaneous finite cover construction,
scalar normalization and final combination are all handled in the item's proof.
The existing ordinary Cech theorem can still rest on its own recorded holes; no such
hole is added or modified by this delivery. No new definition chooses an arbitrary
witness of an unproved existence theorem. Of the one original holed theorem,
zero is newly proved without sorryAx: one is decomposed, with one hole split off.

Checked edge cases mathematically: n=0 is section gluing; r=0 and r=1 give zero and
identity multiplication; g need not be flat or affine. X empty forces Y empty.
Y empty with nonempty X is handled by the empty target opens. An empty shared
cover index forces both schemes empty and all section complexes and cohomology
vanish. Duplicate opens cause no issue in ordered Cech complexes. Finite tuple
intersections are affine by separatedness.

Both modules compile through lcompile.py in import order, without warnings.
The second reading also imports the four existing tools of the new node's proof
plan, including normalized resolution comparison data.

## No longer needed

No original import is removed: all four public imports supply the unchanged public
interface. The two comparison proof imports and Mathlib's affine tools are added in the
item. The split-off module privately imports its four planned proof tools.

The original node's direct dependency
lem-sc-etale-qcoherent-source-comparison-natural
(Sheaf.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural) is bypassed: the proof
goes through Cech homology and the ordinary affine Cech inverse-image comparison,
not an independently chosen endomorphism-natural source-H equivalence. This is
pruning of this node's route, not a claim that the module is globally unreachable.

The other removed original direct dependency,
lem-sc-etale-tensor-unit-sections-natural, is retained through the new node's
proof plan and its proof import; it is not globally pruned.
lem-pc-affine-cech-inverse-image and def-pc-flat-cohomology-comparison remain needed.
The new node uses the finite-Cech computation and normalized resolution-transfer
tools, including lem-weil-pbc-etale-resolution-section-canonical-data. No chapter or unit step from sk-thm-p1.realized is bypassed.

## Where the brief, the DAG or earlier work was wrong

The stated endomorphism-natural source comparison does not identify a comparison
compatible with a morphism between different schemes. The finite-Cech equivalence
is also only a Nonempty statement; it does not expose an augmentation normalization
or its inverse-image naturality. Thus those declarations alone do not justify the
simultaneous pullback square. The remaining theorem explicitly isolates that missing
etale Cech normalization and matching-cycle step. The ordinary leg is already
provided by exists_affineCech_inverseImage and is used rather than split again.

The local literature/stacks-project directory is absent on this remote machine.
Read the full sources online at https://stacks.math.columbia.edu/tag/03P2 and
https://stacks.math.columbia.edu/tag/01FD. The new proof is marked as agent-written:
03P2 gives affine acyclicity and the Cech degeneration, and the 01FD argument is
applied to the small etale sites using their inverse-image/adjunction normalization.
LeanSearch returned Internal Server Error; the failure is recorded, and LeanFinder,
Loogle and Mathlib grep were run. Blueprint searches found no existing node stating
the new canonical etale-to-Cech inverse-image comparison.

## New nodes

lem-pbc-etale-additive-cech-inverse-image: one public theorem in its own new module,
with the precise finite-cover, affine-intersection, scalar and coordinate-matching
statement, source and full proof in words. It isolates the etale leg and contains
no ordinary Ext inverse-image comparison. Its docstring and node give the missing
augmentation/naturality work. The original node's proof and proof_deps now follow
the compiled composition. No interfaces were changed and no forced adaptations or
change records are required.

## Second reading by R3

1. Compared the full item module with the repository using diff. All three
   existing public declarations retain their signatures byte for byte;
   etaleAdditiveSmul and etaleAdditivePullback retain their complete bodies.
   Changes are three private proof imports, the proved private cover helper,
   and the original theorem's proof. There are no target, definition or
   statement changes and no forced adaptations. The new module states its
   own new theorem, with a matching node. Verdict: unchanged interface.

2. Compiled both modules in import order through lcompile.py. Inspected every
   delivered Lean file for forbidden declarations and for sorry. The sole
   direct sorry is exists_etaleAdditive_cech_inverseImage, the whole proof of
   the public named theorem with its source, proof docstring and node.
   Scratch #print axioms checks cover both unchanged definitions, the private
   cover helper, the original theorem and the new theorem. The definitions
   and helper use only the allowed standard axioms; the original theorem and
   new theorem additionally use sorryAx, as expected for this decomposition.
   No definition extracts an arbitrary object from an unproved existence
   theorem. Verdict: compiled reduction with exactly one new named hole.

3. Read Stacks 03P2, Theorem 59.22.4 (separated affine-cover argument), and
   01FD, Lemma 20.15.1 (refinement coordinate rule and augmentation diagram).
   The new lemma assumes the affine intersections those arguments need;
   compactness supplies the finite covers used in the original theorem.
   Multiplication is prescribed on every etale section, rather than merely
   assumed to be an arbitrary endomorphism. The target cocycle is the image
   of a source representative, so its matching condition is attainable for
   every class. Checked n=0, r=0, r=1, empty schemes, empty intersections,
   an empty finite index and repeated cover members. No flatness or affine
   hypothesis on g is used. Independently searched LeanFinder for Cech edge
   isomorphism functoriality under refinement/pullback, Loogle for homologyMap
   and cech, and Mathlib grep for cech/refinement/naturality; searched the
   DAG, lean/Sheaf and the upstream CechComparison source. Hits concern
   sheafification, presheaf coefficient naturality or ordinary Cech
   comparisons, not the new normalized etale comparison. The existing
   finite-Cech theorem supplies only Nonempty in positive degrees, and the
   source-H theorem only endomorphism naturality on one scheme. Neither
   closes this hole in a few minutes. Verdict: true remaining subproblem,
   strictly limited to the etale leg; not a renamed original Ext square.

4. Read exists_affineCech_inverseImage and its hypotheses. The proof supplies
   both covers, all affine intersections, the unit quasi-coherence instances
   and the precise unitToPushforwardObjUnit coefficient map. Its linear
   isomorphisms composed with a and a' give e and e'; toSpecGamma_appTop and
   GammaSpecIso.inv_hom_id normalize the scalar action. The final three
   substitutions into hbb' prove exactly the coeff/invImage/constIso square.
   The private cover helper uses Mathlib compactness and IsAffineOpen.iInf;
   the empty target opens retain source coverage even for empty Y. Affine is
   the module containing IsAffineOpen.iInf and is a proof-only import. All
   added tool imports are private; all public imports serve signatures or
   definitions. Both old direct dependencies absent from the new direct
   proof_deps are accounted for under No longer needed. Read sk-thm-p1's
   realized statement and four steps: neither this helper nor its bypassed
   source-H comparison realizes a protected unit step. Verdict: valid
   reduction below the unit level, with no claimed globally pruned module.

5. Compared the existing node with its repository version: only proof,
   proof_deps and proof_origin change. Its three steps match cover
   construction, the etale comparison application, and ordinary comparison
   composition. Read each new dependency's Lean declaration and node.
   exists_etaleTensorUnit_sections_natural supplies unit section coordinates;
   nonempty_etaleTensorSectionsSheaf_ulift_finiteCech_succ supplies a
   positive-degree existence comparison, not normalization;
   exists_resolutionSection_canonical_comparison supplies normalized data;
   resolutionSection_canonical_transfer supplies the inverse-image part,
   with the coefficient-map lift handled explicitly in the new proof plan.
   The new node has the item's chapter/unit, worker creation, blueprint
   ancestry, actual logged searches, source, proof origin and verbatim Lean
   statement. Verdict: records agree with the reduction and remaining work.

Second-reading changes: added missing private imports of
EtaleTensorUnitSectionsNatural, EtaleQcoherentULiftFiniteCechComparison and
EtaleResolutionSectionCanonicalTransfer, and added the existing
EtaleResolutionSectionCanonicalData tool with its node citation. Clarified the
new proof docstring and plan to separate inverse-image transfer from the
subsequent coefficient-map lift and to exclude inferring naturality from a
bare Nonempty comparison. Corrected direct-dependency pruning and hole-count
wording in this report. No existing signature, definition or completed proof
was rewritten.
