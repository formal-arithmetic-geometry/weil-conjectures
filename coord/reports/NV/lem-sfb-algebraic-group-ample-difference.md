## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-group-ample-difference.json`: item split into four steps; statement and its hypotheses unchanged. Mathlib searches find no ample-difference theorem.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-type-group-ample-line.json`: one new statement-only prerequisite, unsplit, no Mathlib match. It asserts existence of one absolutely ample invertible module on a separated finite-type group scheme over an arbitrary field.
- `citations.json`: eleven entries quoting the full verbatim statement of each node used by each proof step. Search outputs and the authoritative `searches.jsonl` are preserved in the sandbox.

## Attachments

None. Searching `lean/WeilConjectures` for the exact blueprint tag, ample differences, group quasi-projectivity and ample twists found no declaration stating the item. I read `GroupScheme/QuasiProjective.lean`: `AlgebraicGeometry.GrpObj.exists_isAffineOpen_compl_support_zeroLocus` (line 71) assumes an algebraically closed field, whereas the new prerequisite permits any field. `AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace` (line 116) concludes an immersion and does not itself assert existence of an ample module. These are related source material, not exact attachments. Also, the project's absolute `Scheme.Modules.IsAmple` must not be identified silently with the separate proper-scheme `AlgebraicGeometry.IsAmple` in `Modules/Ample.lean`.

## WANTED

None. All mathematical sources used here are present in `literature/stacks-project/`.

## Corrections and route

No statement dispute was found. The imported source mentions Morphisms 0FVC, which proves eventual relative very ampleness, stronger than needed here. I expand its ample consequence using Properties 01Q3(1) => (7) and the affine-locus argument of 0890. This is below the node level and keeps the same ample-twist argument. The generic high-twist theorem is not copied into a new node. Nor is the tensor-with-generated-module consequence made into a node: existing `lem-sc-tensor-section-affine-open` supplies its sole geometric input, so the remaining argument is a short section construction in the item.

The current latest blueprint's `sk-thm-sf-ctf-stability` and direct-image proof (3), and the chapter and unit records, were read. This auxiliary item's recorded ancestry serves the Moret-Bailly II 3.3.3 ample-difference prerequisite. The existing `blueprint.from.node` is null (the ancestor command also prints None); I retain it rather than edit maintainer-owned ancestry. The exact inherited supporting place is extended on the new node. No chapter, unit, target or route is changed. This item is not the unit's key node.

Four generic off-unit tools are declared in `split_report.tool_uses`: high-twist global generation, positive powers of ample modules, nonvanishing cover for a generated line, and the tensor-section affine-locus identity. Their statements are used as black boxes; no unit proof step is replaced.

## Unfinished work

The single new existence input remains unsplit, as required for a one-level split. No Lean is written, no compiler or Lake command is run, and no repository or launcher file is changed.

## Not duplicates

lem-sfb-finite-type-group-ample-line vs lem-sfb-algebraic-group-ample-difference: the new prerequisite gives one ample module on a group without any prescribed L; the item proves a tensor quotient for every prescribed L, using high-twist generation and an explicit affine-locus argument. Two non-elementary assembly steps remain in the item, so its content is not moved wholesale.
lem-sfb-finite-type-group-ample-line vs lem-sc-abelian-variety-projective: that node assumes an abelian variety (proper, smooth, connected) and concludes projectivity; the new node concerns arbitrary separated finite-type group schemes, including nonproper, disconnected and nonreduced ones, and concludes only existence of an ample module. Its statement cannot be obtained by specializing the abelian-variety node.
lem-sfb-finite-type-group-ample-line vs lem-pc-ample-affine-loci-criterion: that node assumes a proper scheme and supplied affine section loci of a line bundle; the new node constructs an ample module on arbitrary finite-type groups.
lem-sfb-finite-type-group-ample-line vs lem-sfb-projective-bundle-relative-ample: that node assumes projectivity, unavailable for nonproper groups, and gives a relatively ample line. The new node requires only a finite-type group over a field.
lem-sfb-finite-type-group-ample-line vs lem-per-projective-bundle-relative-ample: the same projectivity hypothesis prevents application to nonproper groups; the new existence input has no projectivity hypothesis.
lem-sfb-finite-type-group-ample-line vs lem-sfb-proper-relative-ample-projective-bundle: that node takes a relatively ample line and properness as input and proves projectivity, whereas the new node supplies the ample line without properness.
lem-sfb-finite-type-group-ample-line vs lem-per-proper-relative-ample-projective-bundle: that node assumes both properness and an ample line; neither is a supplied input to the new node.
lem-sfb-finite-type-group-ample-line vs lem-sfb-quasiprojective-qc-composition: that node assumes relatively ample lines on two given morphisms; it cannot create the first ample line on a group scheme.
lem-sfb-finite-type-group-ample-line vs lem-per-quasiprojective-qc-composition: composition preserves already supplied relative ampleness; it does not prove existence of an ample module on a general group scheme.
lem-sfb-finite-type-group-ample-line vs lem-weil-pbc-projective-ample-invertible: that node requires a closed immersion into finite projective space and therefore properness over a field. The new group-scheme existence node has no such embedding or properness hypothesis.
lem-sfb-finite-type-group-ample-line vs lem-weil-pbc-coherent-serre-vanishing: that node assumes a proper morphism and an ample module and proves cohomology vanishing; it does not supply an ample module on the group.
lem-sfb-finite-type-group-ample-line vs lem-sfb-space-weak-chow: that node supplies a proper covering modification of a space by a quasi-projective scheme, not an ample module on the original group; general proper-cover descent of ampleness is not asserted.
lem-sfb-finite-type-group-ample-line vs lem-coef-infinity-cocartesian-arrow-projection: this is a quasicategorical trivial-Kan-fibration theorem, unrelated to line bundles; a numerical reference in its source is a coincidental tag-shaped string.

The entire DAG and blueprint were searched by 0BF7, 0FVC, quasi-projective, ample, group scheme and globally generated; the relevant existing statements were opened. No imported blueprint node states general finite-type-group ample existence. The general tensor-product result `lem-sc-ample-tensor` assumes both factors ample and does not provide existence on a group. `lem-pc-ample-affine-loci-criterion` also cannot replace the absolute definition in this nonproper setting.

## Review by NV

I read Groupoids `lemma-algebraic-quasi-projective` (0BF7) in full: its reduction first descends from an algebraic closure, handles finitely many components and nonreduced groups, and then constructs an ample module in the smooth irreducible case. The section explicitly defines algebraic as finite type. I checked Morphisms `definition-quasi-projective` (01VW) and `lemma-ample-over-affine` (01VK): over the affine scheme Spec(k), the ample module guaranteed by quasi-projectivity is absolutely ample. This proves the new statement without imposing smoothness or algebraic closedness. I also read Morphisms 0FVC and Properties `proposition-characterize-ample` (01Q3), `lemma-ample-power-ample` (01PT), and `lemma-ample-tensor-globally-generated` (0890), including the latter's proof. These are the item's sources; the direct affine-locus route is the ample portion of the recorded high-twist argument.

Step 1 cites the new existence statement with precisely the item's separated finite-type group hypotheses, and the actual absolute-ampleness definition for quasi-compactness and section loci. It does not cite abelian-variety projectivity for a general group.

Step 2 cites the invertible-module definition for quasi-coherence and the finite-type definition in `pqf-def-coherent`; a local frame is the explicit one-generator presentation. The global-generation node's statement applies to finite-type quasi-coherent modules on any scheme carrying an absolutely ample module: no properness or coherence-over-a-Noetherian-base hypothesis is being smuggled in. Taking n nonnegative handles its integer threshold. Local frames show that F is invertible. The cited positive-power node asserts absolute ampleness and applies to n+1, which is strictly positive. I read each of these statements, rather than relying on their titles or on their proofs.

Step 3 uses `lem-sc-global-generation-nonvanishing-cover` exactly to find a nonvanishing global section of the generated invertible F. It uses `lem-sc-tensor-section-affine-open` exactly for the equality of the tensor nonvanishing locus with an intersection and for affineness when the M section locus is affine. This node allows arbitrary schemes and line modules, not just curves or proper schemes. Taking the rth tensor power of t and rearranging rank-one tensor factors are explicit elementary operations. This is the elementary proof of 0890 for a globally generated second factor, not an unproved claim that eventual twists are ample. The existing proper-scheme affine-loci criterion was deliberately not used. The absolute definition completes the verification using the quasi-compactness retained from step 1.

Step 4 uses only the rank-one dual and sheaf tensor definitions. Evaluation and its inverse are written in local frames, and the change b -> vb explains why the inverse glues. Thus B^{-1} is exactly Hom(B,O), as the item requires, rather than an unspecified inverse class in Pic. The direction of the final isomorphism is corrected by inversion. No new node merely restates the quotient conclusion.

I checked the small cases: the trivial group Spec(k), nonproper G_a and G_m, finite disconnected groups, and the nonreduced group alpha_p over a field of positive characteristic. The construction never uses a nonempty reduced locus, rational points away from the identity, smoothness, connectedness, symmetry or commutativity. Negative-degree L on a proper group is allowed: n is chosen beyond the global-generation threshold. Choosing n=0 when permitted still makes B=M, since n+1 is positive. The general section arguments and auxiliary existence statement are consistent with empty-scheme conventions, although a group scheme over a field cannot itself be empty because it has its identity section.

Against delivery-errors B–E: the new statement introduces all its objects and cites definitions, has no proof or proof dependencies, and records only actual logged queries. Both semantic phrasings and Loogle were run; the focused Mathlib AlgebraicGeometry grep had zero hits. I read the returned signatures: affine/separatedness, Proj, convex AmpleSet and ring Picard tensor statements are not ample-line existence or an ample quotient theorem. Source tags and labels were checked in the local tag table. The eleven citation quotes were copied verbatim from the live statements and the new statement. The new existence node has no proof edge back to the item, so adds no cycle. All four proof steps are shorter than 2000 characters (355, 647, 880, 593); none hides an unrecorded geometric comparison. The preliminary server review_split passes; the complete delivery dry run follows this report.
