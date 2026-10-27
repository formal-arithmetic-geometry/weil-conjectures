# Q60 stage-1 delivery

Item: lem-sfb-finite-discrete-internal-constructible-kernels.

## Files written

- dag/nodes/sec-proetale-coefficients/lem-sfb-finite-discrete-internal-constructible-kernels.json: repaired four-step split; statement unchanged; Mathlib searches found no match.
- dag/nodes/sec-proetale-coefficients/lem-sfb-finite-discrete-encoded-constant-fp.json: one new statement-only node, unsplit, not a Mathlib leaf. It concerns a single constant finite ordinary module under the particular common sectionwise encoding, and makes no assertion about kernels or constructibility.
- citations.json: all 14 step/node pairs, backed by verbatim complete statements.
- searches.jsonl: actual msearch.py records; retained without alteration.

## Attachments

None. Searching the blueprint tag, finiteDiscrete_constructible_kernel, and constructible-kernel terminology throughout lean/WeilConjectures found no declaration proving this internal-module statement. Its use in ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean is a call, not a declaration. Ordinary etale kernels in ConstructibleSheaf/KernelCokernel.lean concern a different category. The exact theorem is recorded in lean/Sheaf/Paper/FiniteDiscreteConstructibleKernels.lean, but the brief requires attachment declarations under WeilConjectures. That Sheaf file is therefore read as proof material, not claimed as an attachment or proof of upstream closure.

## Wanted

None. The Stacks sources and Bhatt–Scholze PDF needed here are present.

## Problems repaired

The imported proof cited def-weil-pbc-site-comparison-morphism as though its statement supplied full faithfulness. It supplies a geometric morphism and its functors, not that theorem. I now cite det-pe-classical-sheaves-modules, whose statement explicitly gives exactness and full faithfulness on discrete constant-coefficient modules.

The final step cited lem-weil-pbc-finite-discrete-encoded-presentation for the converse passage from an ordinary finite constant sheaf to an internal finite presentation. The existing node only goes from an internally locally finitely presented restriction to ordinary cokernel models. I removed that misuse and stated the actual missing local lemma. I also removed module-constructible-pullback as a justification for encoding invariance: its statement is about geometric module pullback, not the converse encoding comparison.

No mathematical statement correction is required. No bounded-derived comparison is used, and no Noetherian assumption on the scheme has been introduced. The existing new-node ancestry is imperfect: blueprint_refs.py ancestor prints None because the item's created.item is a Lean module name rather than a node. The item already explicitly names sk-def-sfb-bounded-constructible as its blueprint ancestor. The first dry run required the new node to match that computed ancestor exactly. I therefore recorded from.node = null, as blueprint_refs.py actually reports, while naming sk-def-sfb-bounded-constructible and the precise purpose in from.place and retaining the item as its via node. I did not change maintainer-owned created metadata. The item retains its existing explicit blueprint reference.

## Review by Q60

I read the chapter and bounded-constructible unit records, SETUP's three-level route, GOAL, the stage-1 brief and stage document, and both copies of delivery-errors B–E. I followed the latest blueprint's prop-sfb-bounded-constructible-triangulated.proof.md: its cohomological argument needs kernel closure in the heart, and the Kernels paragraph identifies this as a coefficient-coherence input. The item is precisely the finite-discrete specialization of that input. The latest definitions of internal finite presentation and stratified constructibility agree with the unchanged item. No SGA route is used.

For the item I read Stacks proetale.tex Tags 099T (lemma-fully-faithful), 099Y (lemma-compare-locally-constant), and 09AK (lemma-compare-constructible), and etale-cohomology.tex Tag 03RZ (lemma-constructible-abelian). The latter assumes a Noetherian coefficient ring, not a Noetherian scheme; a finite ring is Noetherian, so the already existing finite-ring thm-constructible-serre applies. Tag 09AK's local definition must not silently replace the project's global finite stratification. The fixed-module-origin node explicitly states the source-library global version, so that is the statement I cite. I also read Bhatt–Scholze's Lemma 5.4.1 in the local PDF: it gives inverse-image comparison for arbitrary scheme morphisms, whereas Lemma 5.4.3 has qcqs hypotheses for direct images. We use no direct-image assertion and need no such hypothesis.

For Step 1, I opened the statements of lem-weil-pbc-finite-discrete-condensed-ring-constant, lem-weil-pbc-internal-module-ab-equivalence, def-weil-pbc-common-finite-discrete-encoding, and det-pe-classical-sheaves-modules. The first two supply exactly e and G; the definition constructs the particular equivalence E with those choices; the last supplies exactness and full faithfulness for comparison with the same discrete ring. Equivalences preserve kernels by their universal property, so composing gives the kernel-preserving fully faithful functor H. An arbitrary equivalence is not assumed to identify a regular module without proof; that point is isolated in the new local node.

For Step 2, I opened finite-discrete-constructible-encoding and fixed-module-constructible-origin. The former gives ordinary finite global stratifications for E.inverse(M) and E.inverse(N); the latter produces constructible etale F1,F2 on an arbitrary scheme. The counit supplies H(Fi) isomorphic to M,N. The full-faithfulness statement cited again is exactly what lifts the conjugated map. The equation i2 H(g) = f i1 is written explicitly, so later kernel transport uses the same morphism.

For Step 3, I checked thm-constructible-serre's finite coefficient hypothesis and its explicit kernel clause. It has no scheme Noetherianity hypothesis. Exact module comparison and the chosen equivalence give the first kernel isomorphism. I wrote out the factorization through the conjugation square, so no unrecorded base-change or arrow-transport theorem is being assumed.

For Step 4, I again opened the reverse implication of fixed-module-constructible-origin: it says that the comparison pullback of a constructible etale sheaf is intrinsically constructible with the global convention. I opened finite-discrete-restriction-encoding: it applies to every scheme morphism and the same fixed e,G, hence to the composite of a stratum immersion and a trivializing pro-etale cover member. The unit of E cancels inverse followed by forward encoding; its restriction comparison is normalized by the stated invertible coefficient map. The new node supplies precisely finite presentation of each encoded constant finite value. Restriction along a ring isomorphism carries the regular action, finite sums and the cokernel universal property to their counterparts, so it carries that presentation back to the raw module restriction. The same cover then witnesses the actual definition def-sfb-constructible-module. Transport along the already constructed kernel isomorphism simply composes the presentation isomorphisms. This step needs no local-to-global theorem or new stratification construction.

For the new node I read sites-modules.tex Tag 093N, lemma-locally-constant-finite-type, especially its forward finite-presentation construction, and the existing private regularHomEquiv, scalarRegularIso and encodedConstantFP in lean/Sheaf/Paper/FiniteDiscreteConstructibleKernels.lean. Its argument is: a finite B-module has a presentation by finite free modules (surject from the free module on its finite underlying set; the kernel is a finite set and generates itself). Constant sheafification carries the cokernel diagram to a cokernel. Under the specified G, maps from the internal regular module are determined by the image of 1; the specified equality on forgetful functors identifies this represented functor with Hom(B,-). This identifies the regular objects naturally, and sheafification and scalar transport give the corresponding free-object comparisons on T. The common encoding preserves finite sums and cokernels, yielding an actual internal finite presentation. This is a real encoding-specific comparison rather than a two-line consequence of the currently cited statements; its proof is deliberately retained here for the next worker while its node is statement-only. It is strictly smaller than the item: one constant object, no arrow between constructible modules, no kernel, no stratification and no descent.

I tested B=0 (only the zero module), P=0 (zero ranks suffice), T empty (all sheaves terminal/zero), the identity map (zero kernel), and the zero map (kernel M). The new node only asserts the forward finite-presentation implication, so unlike the reflection part of Tag 093N it requires no nonempty-topos hypothesis. Cover members with empty underlying scheme cause no inference of finiteness from stalks: Step 4 starts with finite constant values already furnished by the cited global-origin statement. Infinite covers and arbitrary non-Noetherian T are allowed; the finite datum is the stratification, not a global uniform rank bound. Scalar presentation ranks may vary with the cover member.

I searched the whole DAG by encoding, finite presentation, regular module, finite discrete, and Tag 093N; searched the blueprint via blueprint_refs.py for kernel, finite discrete, encoded constant, constant module and finite presentation; and searched Lean for the item and new-node notions. Mathlib searches used only the required recorded command, with a second semantic phrasing. The closest hits, Module.finitePresentation_of_finite (Mathlib/Algebra/Module/FinitePresentation.lean:118) and SheafOfModules.IsFinitePresentation (Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:267), were read: the former is scalar algebra, the latter a definition for sectionwise module sheaves. Neither asserts the encoding-specific theorem. All four proof steps are below 2000 characters, and I checked that none hides another independent comparison: the only missing comparison is the new node.

## Not duplicates

lem-sfb-finite-discrete-encoded-constant-fp vs lem-weil-pbc-finite-type-module-sheaf-stalk-finitely-generated: the latter says stalks of a finite-type etale module sheaf are finitely generated; it asserts nothing about the specified sectionwise internal encoding or internal finite presentations.

lem-sfb-finite-discrete-encoded-constant-fp vs lem-weil-pbc-locally-constant-finite-values-finite-type: the latter constructs finite-type generators for ordinary etale module sheaves from finite scalar models; it does not compare regular internal objects or preserve a finite presentation through E.

lem-sfb-finite-discrete-encoded-constant-fp vs lem-weil-pbc-finite-locally-constant-module-values: the latter equates ordinary etale finite-stalk, finite-value and finite-type local constancy; the new node gives a global internal finite presentation of the encoding of one fixed constant object.

lem-sfb-finite-discrete-encoded-constant-fp vs lem-weil-pbc-finite-discrete-encoded-presentation: opposite implication, from internal local finite presentation to ordinary local cokernel models; no converse assertion appears in its statement.

lem-sfb-finite-discrete-encoded-constant-fp vs lem-pe-finite-discrete-scalar-constant-models: that theorem uses a different, normalized section-action encoding and identifies scalar extension models; it does not state compatibility with the arbitrary fixed G and e of the common sectionwise encoding. Citing it here would require an additional identification of these specific encodings. The new node directly supplies the smaller global presentation statement for the actual E used in Steps 1–4.

lem-sfb-finite-discrete-encoded-constant-fp vs lem-sfb-finite-discrete-constructible-model: that theorem concerns bounded derived constructible objects and assumes a Noetherian scheme. Its statement cannot supply a presentation of this particular constant object on an arbitrary scheme. Its proof is not an interface.

## Unfinished work

Only the required one-level statement-only child is left unsplit. No claim of a complete Lean closure is made. All authorized edits are confined to this sandbox, and no compiler, Lake command, project build, direct git command, or local DAG/preflight checker was run.
