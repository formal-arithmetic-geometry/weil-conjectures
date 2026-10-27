# Worker report — Q16

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-lisse-open-relative-line-constructibility.json: re-split item; statement, provenance, previous searches, and Lean record preserved. Eight assembly steps, 2294 characters.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-open-relative-line-principal-geometry.json: statement-only, unsplit; no exact Mathlib match. Extracts old steps 1 and 5: finite principal cover, all intersections, and geometry of finite-etale clopen components.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-etale-shriek-transfer-retract.json: statement-only, unsplit; no Mathlib match. Extracts old step 3: finite module direct-image exactness, derived compact-support comparison and trace retraction.
- citations.json: one entry for each use in each new assembly step, with the verbatim cited statement.
- searches.jsonl and the two *-search-results.json files retain the actual search records and complete returned hits. write_split.py is the sandbox-only generation script.

## Attachments

None. I searched WeilConjectures by the item tag, the recorded theorem name and lisse/constructibility concepts. The recorded Sheaf theorem is still proved by sorry; it cannot be attached. Existing curve-specific transfer theorems impose algebraically closed field, curve and prime-field hypotheses unavailable here.

## Wanted

None.

## What required repair

The old accepted review (2026-10-17) predates the released human repair note of 2026-10-21, applied 2026-10-22. The initial unchanged-copy dry run exposed that newer note: the 7827-character proof must be spread into at least two new nodes and assembled in at most 3000 characters. The report now supersedes the initial stale-assignment diagnostic. This is the requested finer split, not a change of mathematical statement or route. No statement dispute was found.

The geometry node carries the original Noetherian/open/principal/localization work and the finite-etale component checks, rather than leaving them behind the words “the hypotheses hold.” The transfer node carries an isomorphism in the derived category, not a collection of per-degree identifications. It works for a sheaf killed by a prime power even when the covering degree is not invertible in the coefficient ring.

## Argument retained in the new nodes

For principal-open geometry, read morphisms.tex 01T6 (lemma-finite-type-noetherian), 01VC (lemma-open-immersion-smooth), 02NL (lemma-composition-relative-dimension-d), schemes.tex 01I3 (lemma-standard-open-affine), and topology.tex lemma-Noetherian and lemma-Noetherian-quasi-compact. The coordinate ring of a Noetherian affine scheme is Noetherian; its polynomial ring is Noetherian. All opens of the resulting Noetherian space are quasi-compact, so the principal-open basis gives a finite subcover. Intersections are D of the product. Localization R[t] to R[t]_s is presented by adjoining v and imposing sv=1; invertibility lifts uniquely across a square-zero ideal, using (1+i)^{-1}=1-i, giving smooth relative dimension zero for the open inclusion. Compose with the relative affine line. The inclusion and projection are separated and finite type; the principal pieces are affine over the affine base. A clopen part of a finite-etale cover corresponds to an idempotent summand of its finite algebra, hence remains finite etale and affine. Composition gives relative dimension 0+1 and finite type. These are several substantive geometric checks, not a new constructibility assertion or a two-line specialization of one existing node.

For derived transfer, read more-etale.tex 0GKY (lemma-loc-constant-shriek-rel-dim-1), particularly the trace maps and the displayed compact-support composition identity. Its proof calls finite direct-image exactness and shriek composition; the split preserves those arguments in the new statement. The module trace-degree theorem gives t with tη=d. Choose a with ad=1 modulo ell^n; then at retracts η on F. Exactness of finite abelian direct image passes to constant-ring module sheaves because the underlying direct-image functor is the same and exactness is detected on underlying abelian sheaves. An injective resolution thus computes Rg_*G as g_*G in degree zero. The finite morphism is proper; its identity compactification identifies Rg_! with Rg_*. Shriek composition and compactification independence give the displayed derived isomorphism α for the two prescribed compactifications. Applying Rh_! to η and at and conjugating by α yields u and v with vu=1. No local constancy, connectedness, or inverse of d in Λ is used. This is strictly an auxiliary transfer lemma; it proves no constructibility clause of the item.

## Searches and small cases

For each new node I ran two distinct LeanFinder phrasings, Loogle, grep, and LeanSearch through msearch.py, and read their results. Geometry hits provide general Noetherian criteria, affine covers and smoothness of open immersions; none provides this finite principal-cover/intersection and finite-etale-component statement in one specialization. I read the returned smoothness definitions in Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean. Transfer hits concern ring-theoretic etaleness and abstract module pullback; none supplies compact-support transfer. Its LeanSearch returned a rate-limit error, recorded as unavailable. No new node is a Mathlib leaf. DAG statement searches across all chapters and blueprint_refs searches for principal, relative line, retract, compactly supported, 01I3 and 0GKY found no equivalent statement. All original item searches are retained.

Geometry allows the zero ring, empty open, nilpotent s (empty D(s)), r=0, and empty clopen pieces. No nonempty-fibre hypothesis is imposed on smooth relative dimension; its condition is at points. Transfer allows F=0, Λ=0, empty X and T, d=1 and n=1. If X is nonempty, the positive constant fibre degree forces surjectivity. A degree divisible by ell is deliberately excluded: with F=Z/ell and the disjoint union of ell copies, trace after the diagonal is zero. This checks the needed normalization hypothesis. The argument does not require d invertible on all Λ: Λ may have other primary factors while F is ell-primary.

## Review by Q16

I read Stacks 0GKY for the item and the transfer extraction, 0GKX for the constant-coefficient input, the listed geometry passages for the geometry extraction, the released repair note, and the current statements of every cited node. The statement and existing Lean record are unchanged. The coefficient category throughout is constant finite-ring module sheaves on small etale sites, with bounded-below derived functors. No SGA route is used.

Step 1 takes exactly Noetherianity of a finite-type integer base from finite-type-over-Noetherian. The geometry node then supplies the finite cover and geometry, including separated finite type and quasi-separatedness for all opens used later. Nagata's actual statement supplies compactifications over qcqs Y; it is not used for an unqualified arbitrary base.

Step 2 is the old elementary Chinese-remainder decomposition. Orthogonal idempotents act on each finite constant fibre, so the summands are finite locally constant and primary. The finite sum is treated in step 7 by the cited Serre theorem; the zero case is explicit.

Step 3 uses the filtration-cover node's exact constant-degree, finite-etale and finite-clopen-filtration conclusions. W is affine Noetherian by step 1. The positive prime-power exponent and prime-to-ell degree are exactly the new transfer node's assumptions. That node concludes a retract in the derived category for the chosen compactifications, so applying cohomology really preserves its split maps.

Step 4 uses exact extension by zero, the exact-functor derived theorem, additive left exact module direct image, enough module-sheaf injectives and the right-derived triangulated theorem. Each says the property used: a definition of direct image alone is not substituted for left exactness or enough injectives. Exactness also permits restriction of the termwise derived functor to bounded-below categories.

Step 5 checks the component geometry using the new node with the finite cover and its clopen components. The constant-shriek theorem requires an affine separated smooth relative-dimension-one map, a finite-type integer base, finite modules and a chosen compactification; all are present. Filtration devissage states the exact triangulated-functor conclusion needed for all quotients and degrees. The constructible Serre theorem gives kernel, cokernel and extension closure; zero is constructible by the definition. This step uses conclusions of earlier steps, rather than appealing to the proof of a cited node.

Step 6 uses the full sheaf biproduct conclusion of the disjoint-open node. The clopen inclusions have compactifications (i_a,id_T), and exact open extension identifies their shriek values; the actual composition theorem gives the component images. Both derived functors and cohomology preserve the finite biproduct relations. A finite biproduct is built by split extensions, so Serre extension closure is enough, without claiming that arbitrary subobjects of constructible sheaves are constructible.

Step 7 writes the retract as the kernel of 1-sr on the constructible larger sheaf. The cited Serre statement applies to that endomorphism between constructible objects; no blanket subobject closure is needed. The same extension closure combines the primary summands.

Step 8 gives induction on the number of principal opens, with the zero case in step 1. Both the remaining union and its intersection with the first open admit covers of smaller size; all pieces are principal or unions of principal pieces, covered by the geometry node. The actual Mayer--Vietoris node permits arbitrary chosen compactifications and a bounded-below input. The cited long exact cohomology theorem and Serre statement supply the kernel/cokernel extension argument. Thus this proves the specified candidate, not just one newly chosen compactification.

I checked B--E: both new statements introduce their objects, notions are cited or defined inline, new nodes have no proof or proof dependencies, the proof uses existing generic tools without leaving the unit route, citations quote actual statements, and no step exceeds 2000 characters. The two new arguments carry old steps 1/5 and 3; all remaining arguments are explicit short assembly steps or existing cited lemmas. The existing off-unit tool declarations are retained where still used.

## Not duplicates

lem-weil-pbc-open-relative-line-principal-geometry vs lem-sbc-smooth-relative-dimension-permanence: states base change/composition of an already smooth map; it supplies neither the finite principal cover nor affineness and finite type of its finite-etale clopen covers.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-sbc-composite-fibre-local-models: identifies local rings of composite fibres, without finite principal covers or relative-line geometry.

lem-weil-pbc-open-relative-line-principal-geometry vs pqf-def-locnoeth: defines local Noetherianity, without the finite-cover and smooth-component conclusions.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-trf-proper-base-change-coherent-conservative: concerns coherent/conservative morphisms of vanishing topoi under proper surjective base change.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-trf-fibre-component-relative-associated: concerns generic points of fibre components and associated points.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-pc-clopen-smooth-proper-curve: only preserves smoothness and properness over a field on a clopen piece; no principal cover, affine relative line, or finite-etale cover geometry.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-pc-open-immersion-smooth-composition: preserves smoothness alone and neither gives relative dimension one nor the finite principal-cover and affine-component assertions.

lem-weil-pbc-open-relative-line-principal-geometry vs pqf-lem-locnoeth-lft: only gives local Noetherianity of a locally finite-type source.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-weil-pbc-finite-type-over-noetherian: only gives Noetherianity of a finite-type source; it is reused in the item, but does not give the principal-cover, smoothness and component conclusions.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-weil-pbc-smooth-restrict-open-subschemes: only gives smoothness under restriction/isomorphism; no dimension, finite-cover or finite-etale affineness assertion.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-weil-pbc-principal-localization-open-immersion: identifies the localization morphism as an open immersion, without the simultaneous Noetherian, finite-cover and finite-etale-component conclusions.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-weil-pbc-affine-ideals-closed-subscheme: constructs a closed subscheme from compatible affine ideals; its principal-open clause alone does not give the geometry lemma.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-weil-pbc-finite-algebra-noetherian: only proves Noetherianity of a finite algebra over a Noetherian ring.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-weil-pbc-affine-open-section-vanishing-prime: states basic-open affineness/localization and pointwise vanishing, without the cover and relative-dimension conclusions.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-weil-pbc-graded-finiteness-cohomology: proves finite generation of a graded cohomology module on a proper scheme.

lem-weil-pbc-open-relative-line-principal-geometry vs lem-pur-affine-line-support-geometry: only treats the complement of the zero section over a finite-type field base, and supplies no arbitrary-open finite principal cover or finite-etale smooth-component conclusion.

lem-weil-pbc-finite-etale-shriek-transfer-retract vs lem-weil-pbc-etale-lisse-open-relative-line-constructibility: is the parent constructibility assertion; the new transfer node only constructs a derived retract for any primary sheaf and proves no constructibility.

lem-weil-pbc-finite-etale-shriek-transfer-retract vs lem-weil-pbc-affine-line-shriek-finite-type-dense-open: proves generic constructibility of a projection direct image, not a derived finite-etale transfer retract.

lem-weil-pbc-finite-etale-shriek-transfer-retract vs lem-weil-pbc-etale-lisse-filtration-devissage: propagates a Serre cohomology property along a filtration, not the finite-etale comparison and trace retraction.

lem-weil-pbc-finite-etale-shriek-transfer-retract vs split-locally-constant-retraction: the existing node only splits the sheaf unit over a prime field on an irreducible base with connected cover. The new node handles arbitrary primary module sheaves and the comparison and retraction after compactified derived direct image.
