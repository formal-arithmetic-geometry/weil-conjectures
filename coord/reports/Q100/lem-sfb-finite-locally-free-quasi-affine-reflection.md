# Stage-1 report: lem-sfb-finite-locally-free-quasi-affine-reflection

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-quasi-affine-reflection.json: item, statement unchanged, split into four steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-quasiaffine-affine-basic-open-criterion.json: statement, Mathlib leaf, equivalent global-function criterion for quasi-affineness. No new unsplit node.
- citations.json: one verbatim statement quotation for each node cited in each numbered proof step.

## Attachments

None. Searched the live lean/WeilConjectures tree for the item's blueprint tag and for quasi-affineness, norm and descent/reflection. The existing QuasiAffine module gives preservation from a quasi-affine target along affine morphisms, quasi-finite separated tools and base-change results; none says finite locally free target reflection. The same search found no finished project declaration for the new basic-open equivalence. Its constituent declarations are Mathlib declarations, so it is a Mathlib leaf, not an attachment.

## Literature wanted

None. All mathematical sources used are present in literature/stacks-project/.

## Corrections and scope

The item had no proof. Its statement and three statement dependencies were correct and remain unchanged: positive constant degree is sufficient, even if not invertible, and no reducedness, Noetherianity or field-base assumption is justified. The existing ample-existence node would not suffice: its conclusion provides some ample line, whereas here the structure sheaf itself must be ample. The existing supplied-line ampleness-reflection node does give exactly what is needed, and already records the norm construction. No new norm or ampleness-reflection node was created.

The inherited unit record uses the old six-functors unit. Read its record, the sec-six-functors-basics chapter, and literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/{_section.md,sk-thm-sf-ctf-stability-direct-images.proof.md}. Latest direct-images (3) is organized by compactification. This item is a supporting geometric input already assigned below the old alteration branch, specifically the Conrad quotient quasi-affineness input. Its split does not replace any unit step. blueprint_refs.py ancestor returns None; preserved the inherited null ancestor and via chain, with a precise supporting-input place for the new leaf. Whole-blueprint searches for quasi-affine, quasi-affine norm, basic open, 01P6 and 01QE found no statement matching the new equivalence.

## Searches and Mathlib match

All new searches were run using the mandated msearch.py Q100 lem-sfb-finite-locally-free-quasi-affine-reflection command and their returned log records were copied verbatim into mathlib_searches. Existing item searches were retained. The item was searched in two semantic phrasings, LeanSearch, Loogle and grep: no target-reflection theorem was found. Read the returned morphism-property descent types and the affine-morphism preservation type; they do not match the item.

An initial search for the structure-sheaf ampleness equivalence found no scheme ampleness predicate in Mathlib, but returned the basic-open criterion. Rather than create an unsplit ampleness equivalence, recorded the underlying function criterion as a Mathlib leaf and wrote out the tensor-unit conversion in the item. The exploratory searches remain in searches.jsonl; only queries relevant to the actual leaf are recorded in that node. Every recorded query was run.

For the actual new leaf, the id appears in the LeanFinder query. LeanFinder in two semantic phrasings, LeanSearch, Loogle and grep returned AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen and AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen. Read Mathlib/AlgebraicGeometry/QuasiAffine.lean lines 30-90: lines 34-35 include CompactSpace in IsQuasiAffine; lines 60-71 give the affine global-basic-open basis; lines 75-90 prove the converse with exactly CompactSpace and a pointwise affine-basic-open witness. Forward clause: take a basis neighbourhood inside the whole open and the compactness projection. Converse: apply the named theorem. There are no extra separation or finite-type hypotheses. Thus each clause has a direct Mathlib declaration, and no theorem comparing ampleness definitions is hidden in the match. Grep with the directory AlgebraicGeometry returned accurate file and line information; read these lines directly.

## Not duplicates

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-sfb-quasiaffine-invertible-finite-set-section: the latter (0F20) gives a section of an arbitrary line nonvanishing on a finite set, assuming quasi-affineness; it neither asserts affine nonvanishing loci nor the converse quasi-affineness criterion. Although its proof cites 01QE, its statement is different.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-trf-quasi-affine-canonical-affine-embedding: the latter is only the forward canonical open-immersion assertion (01P9); it supplies no converse from a covering by affine global-function opens. The new leaf directly names the two Mathlib criterion declarations and does not create a separate copy of the canonical-embedding assertion.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-a1-quasi-affine-open-principal-comparison-cover: that node concerns an open immersion U into a given quasi-affine V, restriction of two rings of global functions and principal comparison charts. It does not characterize quasi-affineness of an arbitrary Z from its own affine basic opens.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-pc-ample-affine-loci-criterion: that statement assumes properness over a field and gives the projective very-ample-power conclusion for a supplied line. The new leaf concerns arbitrary schemes and global functions and imposes none of those hypotheses.

Searched the whole DAG for 01P6, 01P9, 01QE, quasi-affine-O-ample, the two Mathlib declaration names, structure-sheaf ampleness, and quasi-affine/basic-open language; read candidate statements before creating the leaf. No existing statement contains the new equivalence. Tags 0BD1/0BD2 and norm/ample words were also searched; reused function-norm and supplied-line ampleness reflection rather than duplicating them. The new node is neither a clause of the item nor a restatement: it contains no covering morphism, finite-flat assumption or reflection assertion.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-coef-infinity-mapping-excision: its statement is mapping-space excision for quasicategories and pushouts of simplicial sets; the coincident tag 01P9 is unrelated to schemes or the global-function criterion.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-sc-ample-finite-affine-cover: it extracts a finite affine-section cover from an already ample arbitrary line; it states neither the global-function quasi-affineness implication nor its converse.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-sc-ample-iso: it states invariance of ampleness under an isomorphism between two supplied invertible modules, with no quasi-affineness criterion.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-sc-ample-positive-tensor-power: it preserves ampleness under positive powers of a line; it says nothing about quasi-affineness or the converse global-function criterion.

lem-sfb-quasiaffine-affine-basic-open-criterion vs def-weil-pbc-ample-invertible-module: it defines absolute ampleness for an arbitrary invertible module; it does not prove that the global-function criterion characterizes quasi-affineness.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-weil-pbc-ample-finite-common-power-cover: it produces a finite equal-power affine-section cover of an already ample line; it neither identifies quasi-affine schemes nor gives the converse criterion.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-weil-pbc-ample-scheme-separated: it derives separatedness from an ample line or suitable affine section witnesses, not quasi-affineness from global functions.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-weil-pbc-projective-ample-invertible: it supplies the ample O(1) pullback for a closed subscheme of projective space over a ring; it has stronger hypotheses and no global-function quasi-affineness equivalence.

lem-sfb-quasiaffine-affine-basic-open-criterion vs lem-trf-finite-coproduct-ample-with-points: it compares ampleness on a finite coproduct and its components, with special zero-dimensional components; it does not characterize quasi-affineness of arbitrary schemes.

## Review by Q100

I read Stacks divisors.tex section Norms (0BCX), lemma-norm-ample (0BD0), lemma-norm-quasi-affine (0BD1), lemma-finite-locally-free-has-norm (0BD2), and the finite-locally-free case of lemma-push-down-quasi-affine. They give a determinant norm of positive degree and show that the norm of the structure sheaf makes the structure sheaf downstairs ample. I also read properties.tex definition-quasi-affine (01P6), lemma-quasi-affine (01P9), and lemma-quasi-affine-O-ample (01QE), together with the actual affine-section definition in def-weil-pbc-ample-invertible-module. The new leaf states the equivalent global-function form, not an existence assertion for an unspecified ample line; its source is precisely those tags and its proof is already supplied by the Mathlib declarations read above.

Step 1 cites def-nagata-quasi-affine-morphism for the assertion that the inverse image of each affine U is quasi-affine, and def-pc-finite-locally-free for finite, flat, locally finitely presented and the fixed fibre dimension. I read both statements. Restricting to an open of the target leaves the same local algebra charts and fibres, so this step is elementary; it makes no arbitrary-base-change theorem assumption. The relation X_U=f^{-1}(Y_U) follows from pi being an S-morphism. This reduction neither asserts that an arbitrary open in a quasi-affine scheme is quasi-compact nor assumes quasi-compactness of S.

Step 2 uses the statement of lem-sfb-finite-locally-free-function-norm: maps on every open, preserving 1 and giving nu(f-sharp(a))=a^d. The statement of lem-weil-pbc-finite-closed-map-finite-fibres gives closedness of the image of the whole source. On its open complement the upstairs section ring is zero, so the two inputs f-sharp(0) and f-sharp(1) agree; their norm values give 0^d=1. Positive d makes this 0=1, contradicted in the local ring at the chosen point. This explicitly proves the surjectivity that the ampleness-reflection theorem requires, without an uncited prime-existence or finite-fibre nonemptiness lemma. Only the norm's statement, not its construction or proof, is used. In the empty-target case the contradiction argument is vacuous.

Step 3 uses the new leaf's forward assertion for quasi-compactness and affine basic-open witnesses. Under n=1 these are exactly the witnesses demanded by the quoted absolute ampleness definition. I read def-sc-invertible-module: O is locally free rank one, with itself as tensor inverse. I read def-pc-module-pullback: its tensor formula is exactly the formula used for the displayed multiplication isomorphism with O upstairs, whose inverse is also written out. This identification preserves the witnesses in the definition of ampleness. Finally I read the entire statement of lem-sfb-finite-locally-free-ample-reflection: it reflects ampleness of a specified line along a surjective finite locally free morphism with no Noetherianity, properness or normality hypotheses. Its hypotheses are now established, so it applies to L=O, and its conclusion is precisely O downstairs ample. Using the more weakly phrased ample-existence node would have been a C4 error; the split avoids that error.

Step 4 uses the absolute ampleness definition for quasi-compactness and positive tensor-power affine-section witnesses, writes multiplication and its inverse for O^{tensor n}=O, and applies the converse of the new basic-open leaf. Those isomorphisms identify values in each local fibre, so nonvanishing loci agree. It then uses the quoted definition of quasi-affine morphism to reassemble the result over every affine U. The step is short and hides no new lemma. No non-elementary step is longer than 2000 characters; the entire assembly is under 3000 characters.

The finite-closed-map citation belongs to another unit; its closedness clause is a generic geometric tool, not a replacement route, declared in split_report.tool_uses. Definitions and the Mathlib leaf are notions/tools. The function norm and specified-line reflection are already in this unit. No SGA source is used.

Preflight also required a numeric mathlib_match.line field in addition to the lines already written in how; added line 75 after rereading the pinned file with sed -n, and made the main declaration field name the converse theorem, with each forward declaration named in how. The first dry run identified nine further tag-sharing nodes. I opened and read each statement and added the precise nonduplicate comparisons above; none gives this equivalence. I checked B through E against the actual files. The only new node is a self-contained statement-only Mathlib leaf, with every notion introduced or defined inline, no proof text or proof dependencies, exact TeX and file/line matches. All step dependencies are the union recorded in proof_deps. citations.json quotes the literal statement part used for every cited node, and local substring checks passed. I tested the empty scheme, the identity (d=1), disjoint unions of d copies, Spec(k[epsilon]/epsilon^2) over Spec(k), and characteristic p with p dividing d. In the nilpotent example the function norm remains determinant multiplication (for degree two, a+b epsilon has norm a^2); no trace splitting or division by d occurs. For the new criterion, empty Z is vacuous and affine Z has the witness 1. Non-quasi-compact open schemes do not accidentally satisfy the criterion because quasi-compactness is explicitly required. No false statement or source correction was necessary.

## What remains

No unfinished part of this one-level split. Existing cited nodes retain their own proof obligations and status. One new node is a Mathlib leaf, with zero new unsplit nodes. Maintainer independent review and landing remain part of the normal delivery process.
