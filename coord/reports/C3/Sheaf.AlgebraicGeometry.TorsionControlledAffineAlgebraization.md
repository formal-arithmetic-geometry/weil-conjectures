## What changed

Completed the earlier sandbox attempt for
`Sheaf.AlgebraicGeometry.TorsionControlledAffineAlgebraization`. Its original public
signature and public import are unchanged. Its proof imports three modules:
`TorsionControlledAffineCandidate`, `CoherentFormalModulesIsoInvariant`, and
`CoherentOfFormalQuotientsAndTorsionKernel`.

The proof obtains a quasi-coherent candidate and its map, transports coherence of
one formal quotient through the candidate isomorphism, proves coherence of the
candidate, and lifts the map and isomorphism into the full coherent subcategories.
Faithfulness proves the required factorization. The existing DAG node now records
these actual proof steps.

The new coherence lemma is proved, including its private finite-generator helpers.
For the multiplication range it reuses the existing private theorem
`AlgebraicGeometry.Scheme.Modules.multiplication_range` via a proof-only
`import all Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.
The duplicate local theorem has been removed; no library visibility is changed. Its hypothesis requires only the quotient
at index `s - 1`, with `s >= 1`, and annihilation of the kernel by `J^s`. No bound
on the cokernel is needed for this step. On affine sections, finite lifts of the
image and the quotient generate the candidate: if L contains both sets of lifts,
then I*P is contained in L because I kills the kernel, and P = I*P + L = L.
This gives a direct finiteness argument instead of formal-gluing finiteness and
localization. The new candidate lemma isolates the construction part of the
original argument and does not claim coherence or finite generation.

Validation: all three delivered modules compile with `lcompile.py --all`.
The only remaining declaration-level warning is the candidate's documented sorry.
The second reader runs the delivery dry run and then pushes the reviewed delivery.
No definitions or existing statements are changed, and no forced adaptations are
needed. The new helper statements have explicit binders and lines of at most
100 characters.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.torsionControlled_affine_algebraization`
(node `lem-weil-pbc-torsion-controlled-affine-algebraization`). There is no sorry
in the item's module.

Also proved the new theorem
`AlgebraicGeometry.coherent_of_formalQuotients_and_torsionKernel`
(node `lem-weil-pbc-coherent-of-formal-quotients-torsion-kernel`), together with
its private helpers `exists_fg_lift`,
`finite_of_quotient_and_torsion_kernel`. The existing library theorem
`AlgebraicGeometry.Scheme.Modules.multiplication_range` is reused rather than reproved.

Added and left exactly one hole:
`AlgebraicGeometry.torsionControlled_affine_candidate`
(node `lem-weil-pbc-torsion-controlled-affine-candidate`), in the new module
`Sheaf.AlgebraicGeometry.TorsionControlledAffineCandidate`.
Its proof is exactly `by sorry`, and its docstring gives the complete construction
argument with source and edge cases. It asserts only a quasi-coherent candidate;
coherence is separately derived by the fully written finite-generator proof.
The combination in the item's module constructs the full-subcategory witnesses
and proves the equality by faithfulness, rather than applying a renamed copy of
the original statement.

This is a decomposition, not a net reduction in holes: one existing hole closed,
one new hole added. Dependencies of the existing library may still use sorry.
No new definition selects data from an unproved existence statement: the
candidate witnesses are eliminated only inside the proof of the existential
conclusion. The coherence argument introduces no unproved statement.

## No longer needed

The route no longer uses
`lem-weil-pbc-formal-glueing-finite-modules`, module
`Sheaf.RingTheory.FiniteIffFormalGlueing`, declaration
`Module.finite_iff_formalGlueing`. Localization of the kernel/cokernel and the
finite-generator maximum of elementwise torsion exponents are also unnecessary:
the gluing comparison isomorphisms transfer a uniform bound before finiteness,
and a single quotient plus the bounded kernel proves finiteness directly.

No proof-only imports were present in the original item's module, so none are
removed there. The new coherence module omits the earlier sandbox's redundant
`Mathlib.RingTheory.Noetherian.Basic` import. It retains
`CoherentAffineSectionsFinite`, whose section-finiteness theorem is used twice.

The duplicate private helper `AlgebraicGeometry.multiplication_range` has been
removed in the repair. Its full tensor/image argument is supplied by the existing
`AlgebraicGeometry.Scheme.Modules.multiplication_range`; no additional DAG node
or sorry is introduced. The tensor comparison import remains needed for the
separate quasi-coherence argument.

The other six original planned dependencies are retained through the
candidate or coherence nodes: affine formal equivalence, annihilation transfer,
completion tensor comparison for finite H, flatness of completion, formal gluing
isogeny, and the affine ideal-product comparison. They are not claimed pruned.
Only the finite-gluing criterion itself is removed from this argument; no claim
is made that other targets or modules cease to reach it.

The unit `sk-thm-p1` and every node in its `realized` statement and proof steps
remain unchanged. This changes only the route below the unit level.

## Where the brief, the DAG or earlier work was wrong

Repair of the maintainer return at e0ca7e57b: the earlier delivery duplicated the
library multiplication-range theorem word for word. It is now imported and used
directly. The existing theorem is private, so `import all` is necessary; this is
a proof-only import and preserves the visibility and signatures of every existing
library declaration. The second-reading section below records the review before
this return and must be refreshed by the independent reader for the repaired set.

The earlier sandbox already had a compiling proof and a substantial coherence
argument, but lacked every new node, the updated original node, and report.md;
therefore it was not a complete delivery. Those records are now supplied.
Its coherence helper assumed coherence of all formal quotients unnecessarily;
the delivered helper uses just the quotient by the annihilating power.

The original planned finiteness criterion is valid but unnecessary in this case.
It is important not to identify completion of the possibly infinite candidate T
with completed-ring tensor T by the finite-module comparison: that comparison is
used only for the already finite H. The candidate docstring instead builds beta
using T/I^n T = (S tensor T)/I^n(S tensor T) from the ring quotient comparison,
then uses naturality of these quotient comparisons.

The local clone has no fetched `literature/stacks-project/coherent.tex`, so the
source was read on the public Stacks pages for Tags 0889, 0ALK, and 0888:
https://stacks.math.columbia.edu/tag/0889,
https://stacks.math.columbia.edu/tag/0ALK,
https://stacks.math.columbia.edu/tag/0888.
These documents are already listed as obtained in literature/LIST.md; no missing
reference or human decision is needed.

Edge cases checked mathematically: J=0 makes the positive quotient F itself;
J=the unit ideal makes the bounded kernel zero, so affine sections embed in the
finite target. In the candidate construction, the unit ideal gives the zero
formal system, and F=H with identity map suffices; J=0 gives the original map
under the affine formal dictionary. The zero ring and empty affine scheme obey
the same formulas. The positive exponent is essential when passing from index
`s - 1` to the quotient by `J^s` and is used by the Lean proof.

## New nodes

`lem-weil-pbc-torsion-controlled-affine-candidate`, in module
`Sheaf.AlgebraicGeometry.TorsionControlledAffineCandidate`, states only the
quasi-coherent construction from the affine part of Stacks 0889(1), using
087W, 0888, finite-module completion tensor comparison, and 0ALK(1).
Its remaining proof includes sheafification and natural quotient compatibility;
it excludes the finiteness step. Recorded searches include an unavailable
LeanSearch request, the successful LeanFinder query yielding completion
flatness and tensor comparisons, and grep with no exact match.

`lem-weil-pbc-coherent-of-formal-quotients-torsion-kernel`, in module
`Sheaf.AlgebraicGeometry.CoherentOfFormalQuotientsAndTorsionKernel`, states
coherence from one positive quotient and an annihilated kernel. It is fully
proved from the existing affine-section, ideal-product, kernel, image, tensor,
and coherence criteria plus a direct finite-generator argument. LeanSearch was
unavailable, LeanFinder returned general finite quotient lemmas rather than
this assertion, and grep found no exact statement. Whole-blueprint searches
for coherent quotient, 0889, and 05EU returned no matching blueprint node.
Both nodes inherit the item's chapter and unit and have their full verbatim
Lean signatures recorded. No change record is needed.

## Earlier second reading (a previous round; superseded)

1. Interface preservation: PASS. Diffed the delivered item against the repository
   and used its declaration parser as a second check. Its existing signature,
   visibility, public import, and docstring are byte for byte unchanged. Only
   three proof-only imports and the theorem body change. The other two modules
   are new. No definition, target, or other existing declaration changes, so no
   change record or forced adaptation is required.
2. Proof and axioms: PASS, with the reported construction hole. Compiled all three
   modules in import order with lcompile.py. Compiled scratch copies with
   `#print axioms` for all six declarations, including the three private helpers.
   The coherence theorem and its helpers use only propext, Classical.choice, and
   Quot.sound. The candidate and original theorem additionally use sorryAx.
   Exactly one delivered theorem, torsionControlled_affine_candidate, has a
   literal sorry, with its source, construction proof, and node. There are no
   delivered definitions or forbidden declarations. Scratch copies were removed.
3. Split statements: PASS. Read the candidate construction against Stacks
   https://stacks.math.columbia.edu/tag/0ALK (including its final kernel/cokernel
   comparisons), https://stacks.math.columbia.edu/tag/0888, and
   https://stacks.math.columbia.edu/tag/0889. The exponent after passage to the
   limit may increase. The kernel/cokernel equivalences transfer that bound to
   the glued map before any finiteness argument. Quotient comparisons give the
   candidate's formal isomorphism without assuming completion equals tensor for
   an infinite module. Checked J=0, J=the unit ideal, the zero ring, and the empty
   scheme; checked the positive-exponent indexing s-1 separately. Independently
   searched with msearch.py (LeanFinder, Loogle, grep) using completed-map and
   finite-kernel queries, and rg over Sheaf, the upstream library, and Mathlib.
   No existing declaration supplies this construction or the combined coherence
   criterion without circular use of the item. The remaining hole excludes
   coherence, and the written finite-generator argument supplies it, so this is
   a genuine decomposition rather than a renamed application of the item.
   The construction is not a hole that can be closed in a few minutes.
4. Route and pruning: PASS. Read the finite lifts, image, multiplication-range,
   quotient, and coherence proofs from top to bottom. Every explicit import has
   a role in the signature or proof; proof-only imports are private. No shorter
   applicable route was found. The original finiteness-criterion dependency
   lem-weil-pbc-formal-glueing-finite-modules is no longer used. The other six
   original dependencies remain in the candidate/coherence route as described
   above; none is falsely claimed globally pruned. Read sk-thm-p1.json and its
   realized statement and steps: this change is below those steps, and they are
   preserved. The accounting remains one old hole closed, one new hole added,
   net zero, with a separately fully proved coherence result.
5. DAG agreement: PASS. Compared every node with its Lean file and the original
   node. The only existing-node edits are proof, proof_deps, and proof_origin.
   Both new lean.statement fields exactly match their declarations; both nodes
   have the required source, searches, creation, blueprint, chapter/unit, and
   Lean records. Each proof_deps is exactly the union of its steps' uses. The
   original node describes candidate construction, coherence transport and
   derivation, and faithful full-subcategory packaging, as the proof does.

Second-reading changes: corrected the report's obsolete no-push sentence and
clarified that six original dependencies are retained. Added this independent
review and its axiom evidence. No Lean proof, statement, import, or node repair
was needed. Delivery follows a successful dry run.


## Second reading by C3

Independent second reading of the repaired delivery after return e0ca7e57b.

1. Interface preservation: PASS. Read the diff of the item against the repository:
   the existing declaration signature, visibility, public import and docstring are
   unchanged. Only three proof-only imports and the proof body differ. The
   declaration parser independently reports no changed statements. The other two
   modules are new; there are no delivered definitions, change records or forced
   adaptations. No target statement changes.
2. Proof and axioms: PASS with the one reported construction hole. Compiled the
   three actual files together in import order with lcompile.py --all (18.9, 3.6,
   and 3.6 seconds). Independently compiled scratch copies with #print axioms for
   exists_fg_lift, finite_of_quotient_and_torsion_kernel,
   coherent_of_formalQuotients_and_torsionKernel,
   torsionControlled_affine_candidate and torsionControlled_affine_algebraization.
   The first three use only propext, Classical.choice and Quot.sound; the last two
   additionally use sorryAx. Exactly the named candidate theorem has literal
   sorry. No axiom, unsafe, opaque, implemented_by, extern, or hollow definition
   occurs. Scratch files were removed before delivery.
3. Split statements: PASS. Read Stacks 0ALK(1), including its final kernel and
   cokernel equivalences, 0888, and the affine paragraph of 0889(1):
   https://stacks.math.columbia.edu/tag/0ALK,
   https://stacks.math.columbia.edu/tag/0888,
   https://stacks.math.columbia.edu/tag/0889.
   Read the library's exists_map_to_of_torsion_baseChange and
   coherentFormalModules_affine interfaces as well. Flatness, finite generation
   of the ideal and the quotient-ring isomorphism supply the gluing hypotheses;
   the kernel/cokernel comparison transfers a uniform bound, without finite
   generation of the candidate. The exponent may increase under 0888, which the
   existential conclusion allows. Quotients of S tensor T recover T/I^n T even
   for infinite T, so reconstruction does not assume the conclusion's finiteness.
   The candidate omits coherence; the fully proved coherence argument supplies
   a substantial separate step, so this is a genuine decomposition. Checked J=0,
   J=the unit ideal, the zero ring, empty spectrum, and the index s-1 at s=1.
   For the coherence lemma, finite lifts of the image and quotient give L1+L2;
   the kernel bound gives IP contained in L1, and quotient surjectivity gives
   IP+L2=P. No cokernel bound is required. Independent msearch.py LeanFinder,
   Loogle and grep queries concerned descent from adic completion and finite
   submodule lifts. Also searched lean/Sheaf, lean/WeilConjectures, upstream
   WeilConjectures, and Mathlib finiteness/noetherian sources. Results give adic
   lift lemmas and finite-range facts, not this construction or coherence result.
   The remaining construction cannot be closed by a short application found
   in these searches; it still needs gluing, sheafification and natural quotient
   compatibility. No new object is chosen in a definition from mere existence.
4. Route and pruning: PASS. Read the upper proof, finite-generator helpers,
   section comparisons and final coherence conversion from top downward. Each
   proof-only import supplies a declaration explicitly used. In particular
   multiplication_range is imported from the existing module via import all;
   inspected its statement and proof and verified the arguments K=J^s, M=F,
   U=top against the local typeclass hypotheses. This resolves the entire
   maintainer return: the duplicate theorem is gone, and its original library
   visibility is unchanged. The tensor comparison is still used separately to
   prove quasi-coherence of the product. No shorter applicable construction or
   coherence proof was found. The old finite-gluing criterion is the sole old
   planned dependency removed; the other six are retained through the new
   candidate/coherence nodes. Read sk-thm-p1.json and its realized statement and
   four step lists: none is bypassed or edited, and the change is below the unit
   level. Accounting is one old hole closed and one hole added, net zero; the
   coherence theorem is independently sorry-free. Pruning is only from this
   argument, not a claim about global reachability.
5. DAG agreement: PASS. Parsed all three delivered node files and compared the
   existing one against the repository: only proof, proof_deps and proof_origin
   change. All three lean.statement fields match their Lean signatures verbatim;
   every proof_deps is exactly the union of step uses. Checked both new nodes'
   source, searches, creation, blueprint, chapter/unit and Lean records. The
   coherence node now explicitly describes reuse of the private library theorem,
   finite lifts, affine sections and coherence criteria. The upper node records
   candidate construction, transported quotient coherence, the finite-generator
   result and faithful subcategory packaging, exactly as the proof does.

Second-reading changes: appended this fresh review of the repaired delivery and
its independently rerun compile, axiom, search and node evidence. No further Lean
or DAG repair was needed. The previous review remains labeled superseded. The
single remaining hole is honestly recorded as a decomposition, not net progress.
