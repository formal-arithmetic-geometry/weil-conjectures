## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.cechRefinement_resolution_canonical_beta`
without changing its signature. The proof follows the four-complex zigzag of Stacks
[Tag 01FD](https://stacks.math.columbia.edu/tag/01FD), with the global-section and
forgetful-homology identifications explicit. It applies the existing first-quadrant
column comparison, proves coefficient augmentation naturality, and performs the
inverse cancellations in a private categorical lemma. A proved equality of the scheme
and ringed-space forgetful functors makes the final identifications explicit. The
private forgetful homology isomorphism is irreducible, with proved equations for its
hom and inverse; its scalar ring is pinned explicitly. The target refinement alpha
square is transported by those equations before the categorical cancellation.

Added `Sheaf.Paper.CechComplexAugmentations`: concrete termwise Cech and total
functors, alpha and beta for arbitrary module complexes, their cochain equations,
their coefficient naturality, and their specializations to the existing resolution
maps. Every declaration of this module is proved. The double functor packages the
existing unnamed functor; it does not introduce a second definition of Cech cochains
or of the bicomplex object `cupCechDouble`.

Added two strictly smaller obligations in separate modules:
`Sheaf.Paper.CechPushforwardLambdaColumns` and
`Sheaf.Paper.CechRefinementPushforwardTotal`. Proof-only imports in the original
module bring these into the target closure. There are no adapted existing modules,
changed definitions, arbitrary data chosen from an unproved existence theorem,
or changes to target statements. The existential map supplied by the refinement
lemma is used only in this theorem's proof.

Repair of H10: removed the redundant file transparency override and the theorem-local
`backward.isDefEq.respectTransparency.types false` override. Added local irreducibility
for `HomologicalComplex.homologyMap` and `ShortComplex.mapHomologyIso` before the
main theorem. Profiling identified repeated elaboration of the native homology
construction while matching diagram endpoints; the proof now uses its named equations
without eagerly expanding those definitions. The complete public theorem signature
was compared byte-for-byte with the returned delivery and is unchanged. No file or
proof was split, no timeout was raised, and no new hole or adaptation was added.

H10 validation: the revised target compiled without warnings in 52.6 seconds.
The target `#print axioms` probe passed in 54.7 seconds and printed exactly
`propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx` from the two
reported lower obligations. A fresh artifact-producing compile also passed the
unchanged 60-second compiler timeout (its tool elapsed time included slot waiting).
The sole direct importer `Sheaf.Paper.CechRefinementResolutionDiagram`, copied
unchanged into scratch space, compiled against the delivered `.lbuild` overlay in
16.7 seconds without errors or warnings. It is not included as an adaptation.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.cechRefinement_resolution_canonical_beta`
(node `lem-sc-cech-refinement-resolution-canonical-beta`) by decomposition into two
lower obligations. This is a decomposition, not a net decrease in holes: one closed,
two added. No sorry remains in the item's module or in CechComplexAugmentations.

The two new sorries are:

- `AlgebraicGeometry.Scheme.Modules.cech_pushforward_lambda_columns`
  (`lem-sc-cech-pushforward-lambda-columns`). This asserts only the resolution-column
  quasi-isomorphism for a map from pushed-forward injectives to injectives; it has
  no source resolution, augmentation lift, refinement map, or covering assumption.
- `AlgebraicGeometry.Scheme.Modules.exists_cechRefinement_pushforward_total`
  (`lem-sc-cech-refinement-pushforward-total`). This asserts the two augmentation
  squares for tuple restriction on the pushed-forward target resolution. It has
  no source resolution J, lift beta, replacement K, lambda, inverse total map, or
  covering assumption. The composite augmentation is constructed explicitly, and
  its differential-zero equation is proved.

Each remaining theorem has a complete source-based proof in its docstring and node.
The edge cases include arbitrary infinite index sets, empty tuple sets and
intersections, zero coefficients, and degree zero. No target-family cover is used.

## No longer needed

No existing import was removed and no module is claimed as pruned. Both original
public imports are needed by the unchanged statement. The original plan's global
sections theorem `lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`
is not directly applied here: the new columnwise obligation isolates the stronger
sections-on-every-intersection step. That theorem remains transitively needed by
the existing cohomology-map construction, so this is not a global pruning claim.
The first-quadrant total-column comparison remains directly used. No unit statement
or step has been bypassed.

## Where the brief, the DAG or earlier work was wrong

The inherited sandbox attempt had not passed compilation: its alpha-square
application mixed the native forgetful homology isomorphism with an irreducible
wrapper, and its final comparison omitted the scalar-ring normalization. Both
conversions are now explicit; diagnostic tracing was removed.

The existing global-sections quasi-isomorphism theorem is stated only for the whole
space and integer-indexed complexes. By itself it does not supply the resolution
columns of the Cech map, which involve sections on every tuple intersection and
products over tuples. The new column statement names this missing specialization
and product argument rather than assuming that the global statement matches it.

The existing `moduleCechLiftSquares` requires injective resolutions on both sides.
The replacement K in ModuleCohomologyFMapData is an arbitrary injective complex,
so the new, fully proved arbitrary-complex augmentation API is needed.

The repository copy of the cited Stacks TeX file is absent on this machine. The
proof was checked against the official online Tag 01FD instead. LeanSearch returned
Internal Server Error; LeanFinder, Loogle, source searches and blueprint searches
were recorded. There is no statement dispute.

## New nodes

`def-sc-cech-complex-augmentations` records the concrete arbitrary-complex functors,
augmentations and their proved naturality in CechComplexAugmentations.

`lem-sc-cech-pushforward-lambda-columns` records the section-acyclicity and product
step in CechPushforwardLambdaColumns. This is the resolution-column part of the
original plan's second step.

`lem-sc-cech-refinement-pushforward-total` records the tuple-restriction map and its
alpha and beta squares in CechRefinementPushforwardTotal. This is the geometric
part of the original plan's first and third steps, independent of the source lift.

The original node's proof, proof_deps and proof_origin now describe the actual
functorial maps, column comparison, target-only refinement, and categorical
cancellation. The preflight classifies the file-level private-wrapper attribute and elaboration
options as an interface change. Their private/local scope, unchanged public
signature, and absence of required adaptations are recorded in
`coord/changes/cech-refinement-resolution-beta-private-homology-api.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered target module with the repository using `diff -u`, and
   separately compared the text from its existing theorem name to `:= by`:
   byte-identical signature. The only changes to the existing node are `proof`,
   `proof_deps`, and `proof_origin`. No existing public definition, instance, or
   public import changed. The private canonical homology wrapper contains actual
   data and is covered by the supplied change record. Verdict: pass.

2. Compiled all four files through lcompile.py. The three new modules passed on
   the first set compilation. The target initially exceeded 60 seconds under load,
   then passed its single-file retry in 54.0 seconds without errors or warnings.
   A scratch copy of the actual delivered target, with `#print axioms` appended,
   passed in 54.9 seconds. Its axioms are propext, Classical.choice, Quot.sound,
   and sorryAx from the remaining obligations. The new functors, alpha, beta,
   their coefficient naturality, and cechPushforwardAugmentation and its cocycle
   equation use only the three permitted axioms. Both named open theorems also
   have only those axioms plus sorryAx. Source scan finds exactly the two reported
   sorries and no forbidden declaration or hollow definition. In particular the
   adjunction chosen by cechPushforwardAugmentation has no sorry dependency, and
   the existential s is eliminated only inside a theorem proof. Verdict: pass;
   this remains a decomposition, one hole closed and two added.

3. Read the official Stacks sources [01FD](https://stacks.math.columbia.edu/tag/01FD),
   [01EX](https://stacks.math.columbia.edu/tag/01EX), and
   [015E](https://stacks.math.columbia.edu/tag/015E), together with both new theorem
   statements, their docstrings and nodes. For lambda columns, 01EX gives acyclicity
   on every source intersection, the injective target terms are acyclic, and 015E
   preserves the quasi-isomorphism on sections. Arbitrary products preserve this
   on underlying module groups: cycles are componentwise and boundary preimages
   can be chosen componentwise. No finiteness or cover hypothesis is needed.
   The refinement obligation gives only the B-double-prime-to-A map and its two
   squares, not the source lift or the cancellation conclusion. In each bidegree,
   refinement composed with a tuple followed by restriction commutes with face
   maps and the coefficient differential; the alpha and beta equations follow
   from the pinned sections map and the specified gamma components respectively.
   Tested identity morphisms/refinements, zero coefficients, empty schemes, empty
   indexing families, repeated indices, arbitrary infinite products and p=0.
   If the source indexing family is empty, a refinement forces the target family
   empty; all Cech totals are then zero. No invertibility of target alpha is used.
   These are two true, strictly smaller parts of the four-complex argument.
   Independent LeanFinder searches for section-acyclic Cech columns and for
   ringed-space restriction with both augmentations found no exact result;
   Loogle found the already-used ShortComplex homology naturality equations.
   msearch grep and rg of the library found the existing general Leray theorem,
   pushforward acyclicity, ModuleCechLiftSquares, and cupCechDouble. None supplies
   either obligation directly: LiftSquares requires two resolutions on one scheme,
   while cupCechDouble supplies the object but not arbitrary-complex augmentations.
   No additional hole was closed in a few minutes. Verdict: pass after correcting
   the column docstring's erroneous attribution of Leray acyclicity to 01EZ.

4. Read the categorical cancellation from the final beta equation backwards:
   coefficient beta naturality and D.compatible give the left pentagon; lambda
   columns and first-quadrant comparison give l; target-only restriction gives s;
   alpha naturality and the actual hom/inverse equations identify the resulting
   zigzag with the fixed r and t. The source cover is used only for source alpha
   invertibility. Every added proof-only import is used; both original public
   imports serve the unchanged signature. The sole old proof dependency removed
   is lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso, already named
   under No longer needed; it remains transitively used and no module is pruned.
   Read dag/units/sk-prop-av-cube.json: realized.statement and its one realized
   step are empty, so no realized unit node is bypassed. This is below the general
   cube theorem route. The blueprint Markdown is absent on this machine; its text
   is recorded in that unit JSON. Verdict: pass.

5. Matched each of the target node's four proof steps with the Lean proof and its
   dependency calls. The three new node records have source, statement dependencies,
   proof steps and their union, origin, searches, creation, blueprint, chapter/unit,
   and Lean declaration records. The two open theorem signatures match their node
   lean.statement fields; the augmentation node lists its proved API. The column
   node cites the existing pushforward-acyclic and Leray nodes, which actually state
   the facts required; the product step is the explicit elementary cycles/boundaries
   argument. Corrected the source/origin/blueprint-place reference to 015E and marked
   unavailable LeanSearch entries with verdict unavailable. Verdict: pass.

Second-reading changes: corrected the column theorem's 01EZ citation to Derived
Categories 015E in its docstring and node metadata; supplied explicit unavailable
verdicts for failed LeanSearch calls; appended this independent reading. No Lean
signature, proof, import, or definition was changed by the second reader.

## Second reading by G3

1. Compared the target file with the repository using diff and extracted the entire
   existing theorem signature through `:= by`: byte-identical. The original node
   differs only in proof, proof_deps and proof_origin. Both original public imports
   remain; the three added imports are proof-only. The private homology wrapper is
   actual canonical data, and its attributes/options are documented in the change
   record. No existing public definition or instance changed. Verdict: pass.

2. Read all four modules, including every construction and the categorical
   cancellation. Exactly two named theorem bodies contain sorry; no definition does,
   and no forbidden declaration or kernel-check bypass appears. The three new modules
   compiled cleanly (12.9, 3.7 and 9.9 seconds). The initial target set compile and
   target axiom probe timed out at the unchanged 60-second limit; an unchanged
   single-file retry passed in 57.1 seconds. Added local irreducibility for the four
   alpha/beta maps, preserving their proved equations and all signatures: the revised
   target compiled cleanly in 49.2 seconds. Explicit axiom probes of all twelve new
   augmentation API declarations and cechPushforwardAugmentation and its cocycle
   theorem show only propext, Classical.choice and Quot.sound; both lower obligations
   add only sorryAx. The complete target axiom probe passed in 52.2 seconds and printed only
   propext, Classical.choice, Quot.sound and sorryAx. The private canonical homology
   wrapper itself uses only the three permitted axioms. Verdict: pass; this is a decomposition with
   one hole closed and two holes added, not a net decrease in holes.

3. Checked the two new theorem signatures against their node records verbatim and
   against official Stacks Tags 01FD, 01EX and 015E. Column comparison requires
   section-acyclicity on each tuple intersection, then products: cycles are
   componentwise and boundary preimages may be chosen componentwise, including
   infinite products. Target-resolution refinement is constructed by selecting the
   refined tuple and restricting; faces, coefficient differentials and both
   augmentation axes commute. It omits source J, lift beta, replacement K and inverse
   total comparison, so it is strictly part of the original argument. Checked p=0,
   zero coefficients, empty intersections/schemes, repeated indices, empty families,
   identity refinements and arbitrary infinite families. No target cover is needed.
   Independent LeanFinder searches used evaluation on opens and restriction of
   sheaf sections; Loogle found the already-used homology-iso naturality equations.
   msearch grep and rg found no exact replacement. Read ModuleCechLiftSquares,
   PushforwardInjectivesSectionsQuasiIso, CupCechTotalComplex and cupCechDouble:
   their resolution hypotheses do not cover arbitrary K, and the existing double
   object is the same termwise functor, now packaged as a functor. The current upstream
   Acyclic module also has quasiIso_map_of_rightAcyclic_nat; this supplies the
   sectionwise Leray step directly but not the product/column identifications, so it
   does not close either remaining obligation in a few minutes. Verdict: pass.

4. Traced the conclusion backward through refinement_diagram_cancel: beta
   naturality and D.compatible give the pentagon, column comparison gives the
   invertible total lambda, and target-only refinement gives s. The alpha squares
   and canonical forgetting-scalar equations identify the resulting map with the
   fixed r and t, using the source covering only to invert source alpha. Both old
   public imports serve the unchanged signature; every new import is used. Comparing
   old and new proof_deps leaves exactly the old global-sections quasi-isomorphism
   node, already listed under No longer needed; it remains transitively needed.
   No module is pruned. Read sk-prop-av-cube.json: its realized statement and step
   lists are empty, and this reduction remains below its general cube route.
   Verdict: pass.

5. Matched each target-node step with its actual calls and the cancellation lemma.
   New nodes have their source, complete word proof, statement dependencies, proof
   dependencies equal to the union of step uses, proof origin, search records,
   creation, blueprint, chapter/unit and Lean fields. Every dependency node exists.
   The new functors package existing constructions; the augmentation data is fully
   constructed. The existential s is eliminated only in a theorem proof, and the
   chosen tensor-pullback adjunction is proved without sorry. Verdict: pass.

Second-reading changes: added local irreducibility attributes for
moduleCechComplexAlpha, moduleCechComplexBeta, moduleCechAlpha and moduleCechBeta,
then updated the private homology API change record to describe them. No statement,
definition body, import, node or remaining hole changed. Appended this independent
reading and refreshed compilation and axiom checks.

Final target axiom probe: clean compilation in 52.2 seconds; exactly the three
permitted axioms plus sorryAx from open proof dependencies. The private canonical
homology wrapper has no sorryAx.

Delivery dry run: deliver3.py --no-push printed OK; all four modules compiled,
the delivery axiom probes ran, and preflight passed with review class CODEX
(new modules/nodes, change record, local attributes, and repair of a return).
