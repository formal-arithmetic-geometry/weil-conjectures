# Worker report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-condensed-lfp-local-triviality.json`: statement unchanged, eight proof steps, status split; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-condensed-point-basis-evaluation.json`: new statement-only generic inverse-image evaluation theorem; unsplit, no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-geometric-field-proetale-evaluation.json`: new statement-only generic geometric-field site/evaluation theorem; unsplit, no Mathlib match.
- `citations.json`: verbatim statements for every cited node, numbered by the eight item steps. Supporting PDF extracts and a sandbox-only writing script are not delivery files.

## Attachments

None. Searched slopmaster2 WeilConjectures by the item tag, local finite presentation, continuous functions, and coefficient descriptions. The existing continuous-function sheaves in SixFunctors/ProEtale/Adic/ConstantSheaf.lean do not give the condensed inverse-image identification AND the finite-presentation-to-local-freeness assertion. Master ConstructibleSheaf/ProEtaleModule/Def.lean:66 defines the local-presentation predicate, and its docstring calls these field sheaves lisse; it supplies no finished theorem proving this bridge. Master is reference material, not attachment evidence.

## Wanted literature

None. Read the two available PDFs, the exact master RefactorInstruction.tex Section 4, and the relevant Stacks source. The auxiliary master TeX exists in the read-only master checkout, although there is no copy at the corresponding literature/upstream-master path. It is an explanation, not a finished proof.

## Faults and corrections

The supplied statement is retained, including topological noetherianity rather than noetherian coordinate rings, arbitrary scheme characteristic, and no completeness assumption. There is no statement dispute. The node had no proof. HRS Theorem 6.2 describes a lisse heart; its hypotheses already concern lisse objects and do not directly show that an arbitrary locally presented module is lisse. I did not use it to conceal the required bridge.

A tempting incorrect argument is to reduce a continuous matrix independently on its presenting pro-etale cover and assume rank is locally constant there. On the profinite set {0} union {1/n : n >= 1}, the continuous function with values 0 at 0 and ell^n at 1/n has jumping rank. The quotient of a free rank-one continuous-coefficient module by this multiplication map need not be locally free at the limit point. The proof therefore descends the numerical rank to the noetherian base before elimination. It does not claim a general local-freeness theorem on every profinite presenting space.

## Not duplicates

lem-weil-pbc-condensed-point-basis-evaluation vs lem-weil-pbc-profinite-point-pullback: the existing node proves well-definedness, exactness, monoidality and composition of the functor; it states no formula for its sections on a contractible affine. The new node supplies that formula for arbitrary condensed sets, abelian groups and rings, not the E-specific continuous-coefficient clause.

lem-weil-pbc-condensed-point-basis-evaluation vs lem-weil-pbc-profinite-test-object-functor: the latter constructs X[S] and its site properties, but does not evaluate the inverse image of an arbitrary sheaf.

lem-weil-pbc-condensed-point-basis-evaluation vs def-weil-pbc-proetale-modules: that definition specifies sheafification of continuous functions with finite discrete ring coefficients. It does not identify the abstract profinite-point inverse image, nor allow arbitrary condensed sheaves.

lem-weil-pbc-condensed-point-basis-evaluation vs lem-weil-pbc-condensed-e-realization: the existing comparison concerns separated finite-type schemes over a positive-characteristic field different from ell and a rationalized derived category. It cannot provide the generic section formula for arbitrary schemes. It also involves the current local-freeness bridge, so citing it here would risk circular reasoning.

lem-weil-pbc-geometric-field-proetale-evaluation vs lem-cbc-proetale-stalk-conservative: the existing node warns against geometric-point conservativity and gives detection statements with finite discrete coefficients or etale origin. The new node instead identifies the entire topos over an algebraically closed field, and only asserts exact evaluation and invariance under changing that field. It does not assert conservativity of final-object evaluation.

lem-weil-pbc-geometric-field-proetale-evaluation vs def-weil-pbc-geometric-stalks: that definition uses pointed ETALE neighbourhoods. It cannot supply a pro-etale field-site equivalence or evaluation exactness.

Before creating either node I searched the whole DAG by continuous functions, connected components, point-eval, w-contractibility, algebraically closed/profinite fields and exact evaluation. Blueprint searches used continuous, continuous functions, profinite point, point-eval, w-contractible and algebraically closed field, covering all imported chapters. The point-eval hit in the trace chapter is a finite fixed-point trace computation, not either new theorem. Both new nodes have the ancestor returned by blueprint_refs.py, thm-weil-pbc-qbar, and the item's full via chain. Same_as is empty for both and for the item; no imported blueprint statement states this bridge.

## Mathlib searches

All new entries were actually run using msearch.py and are recorded verbatim from searches.jsonl with hit names and service notes. Every new node has LeanFinder, Loogle, grep and attempted LeanSearch, plus a second semantic phrasing. LeanSearch returned HTTP Internal Server Error and is recorded as unavailable. Read the successful search hits: Condensed.isSheafProfinite and Condensed.ofSheafForgetProfinite concern the profinite/compact-Hausdorff equivalence, not scheme pro-etale inverse images; LightCondensed declarations concern the light site; formally etale ring equivalences do not identify a geometric-field topos. Read Mathlib/Condensed/Equivalence.lean. For the item, read SheafOfModules.IsFinitePresentation and its exists_quasicoherentData in Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:267-284: they supply local presentations, not local freeness. Module.FinitePresentation.exists_free_localizedModule_powers assumes freeness after a localization and likewise cannot prove the item. No hit is an exact match or one-line specialization.

## Review by ND

I read HRS Example 3.1 (PDF printed page 5) and Theorem 6.2 with its proof (printed pages 16-17), and BS Lemmas 4.2.12-4.2.13 (printed page 30) and Example 4.2.11 (printed page 30). I also read master RefactorInstruction.tex Section 4, lemma point-eval and proposition continuous-X, and master ConstructibleSheaf/ProEtaleModule/Def.lean local finite presentation. The imported source place was honest that Theorem 6.2 does not prove this bridge; the delivery keeps that distinction. The new basis node abstracts the inverse-image computation in BS 4.2.13 and the profinite-point identification in HRS 3.1; it leaves the generic computation unsplit. The new field node abstracts BS 4.2.11 and its naturality, with split singleton covers giving exactness. Neither assumes any finite presentation, noetherianity, E, or local freeness.

Step 1 uses the actual openness conclusion of lem-weil-pbc-fpqc-detects-openness and the actual fpqc covering definition in def-weil-pbc-proetale-site. I checked that the covers here are fpqc, not arbitrary jointly surjective maps. The compatible functions agree above a common base point by a nonempty residue-field tensor product; quotient detection applies to the inverse image of each open of E. This reproduces BS 4.2.12's topology argument and proves sheaf gluing rather than citing an uncited continuous-function-sheaf theorem.

Step 2 uses the new basis-evaluation statement and the existing affine weakly contractible covering-family statement. Both apply on the full small site with the prescribed universes. Total disconnectedness of the normed field makes maps constant on components, and continuity through the quotient is exactly the quotient topology included in the new statement. The coefficient definition fixes p_X^*; it is not cited for the section formula. Ring operations and all restrictions are respected before gluing. The covering-family node supplies a basis, not a single cover only of X.

Step 3 uses the existing site-pullback exactness node for cokernels, the existing point-pullback node for coefficient and composition comparisons, the new field-site node for exact final-object evaluation and split covers, and the pro-etale inverse-image definition for base change. These statements really say those things. I checked the coefficient evaluated at a geometric field is E, not a discrete constant sheaf or an integral coefficient ring. Rank is defined from P itself and is independent of the presenting matrix; pullback of the presentation to a geometric field computes its finite vector-space cokernel. The new field node explicitly includes extension compatibility needed to remove the choice of algebraically closed representative. Exactness of underlying abelian inverse image suffices because the coefficient comparison is an isomorphism; tensoring along that isomorphism introduces no flatness hypothesis.

Step 4 uses weakly etale implies flat as written in the site definition, the local-ring meaning of flatness, and the exact prime-chain lifting statement of lem-sc-flat-going-down. I read Algebra Tag 00HS's statement via the cited node and checked going-down is applied to the flat local ring map at the chosen lift of y. The lift of x is a GENERalization of v, the direction needed for equality of continuous coefficient values. No finite presentation of the covering map is assumed, so no false appeal to openness of a flat non-finitely-presented map occurs.

Step 5 uses the topological statement lem-sc-noetherian-finite-irreducible-components, not the similarly named node requiring a noetherian scheme. I read Topology Tag 0052 (lemma-Noetherian) and Schemes Tag 01IS (lemma-scheme-sober). The former requires only topological noetherianity; the latter applies to every scheme. Their statements give the finite CLOSED components and their generic points. Specialization invariance makes rank constant on each component, even when components meet; meeting components must have the same rank. Every level and its complement is a finite closed union, so every level is clopen. No quasi-separatedness or algebraic noetherianity is smuggled in.

Step 6 uses exact inverse image only for restricting cokernels and the coefficient composition comparison only for identifying restricted rings. These were the precise conclusions read in the cited statements. Pullback of the rank partition makes the pointwise matrix rank genuinely constant on each piece; the piece itself need not be noetherian. Matrix entries are global sections because maps from the rank-one free ring sheaf are specified by the image of its unit. The same holds with zero-sized matrices.

Step 7 is an elementary block-matrix calculation, written explicitly rather than made a node. Nonzero determinants have open loci since E is Hausdorff, and inversion is continuous on E minus zero. The adjugate formula therefore gives actual coefficient sections. The displayed two invertible matrices produce the Schur complement, whose pointwise rank is zero. Here pointwise equality proves equality of continuous FUNCTIONS, not equality of arbitrary pro-etale sheaves. This is why the warning in lem-cbc-proetale-stalk-conservative is respected. The cokernel of the displayed diagonal matrix is explicitly free; no conservativity theorem is used.

Step 8 uses composition of site coverings and applies the statement to each noetherian stratum with exactly the local presentations in the coefficient category definition. I checked no completeness hypothesis appears in that definition or any preceding step. The covering is allowed to have different finite ranks on its different members.

Small cases: X empty gives the empty cover. A zero matrix gives free rank n, an invertible square matrix gives rank zero, m=0 gives the free sheaf of rank n, and n=0 gives zero. At an intersection of irreducible components their ranks necessarily agree, so the clopen rank partition cannot improperly separate intersecting components. The profinite jumping-rank example above is excluded at the BASE, not at the presentation cover. The new evaluation statements apply to the empty affine (F(empty) has the required terminal/zero value), the one-point profinite set and arbitrary algebraically closed characteristic, including characteristic ell. No derived completeness, torsion, characteristic restriction, geometric-point conservativity, or constant-coefficient identification was assumed.

Checked B-E: new nodes are complete statements with empty proofs/dependencies, original imported fields were retained, definitions are cited or spelled out, no local-freeness clause has been renamed, all non-elementary inputs are cited, citation quotes are copied exactly, and blueprint provenance is filled. The generic field site's extension compatibility remains a named unsplit obligation, not an assertion hidden inside the item's argument. Corrected the initially tempting coverwise rank argument by constructing the intrinsic rank on X and proving it specialization-invariant first.

## Unfinished work

Only the two explicitly named new statements remain unsplit, as required for a one-level delivery. No other proof gap is intentionally deferred. No Lean file was written, no compiler/build was run, and no other agent was started.

## Dry-run repair

The first preflight rejected the legitimate TeX double-backslash matrix row separators under B4. Replaced those row separators by the single-command TeX \cr notation, preserving the displayed block calculation. Also made the new generic field node cite the existing Mathlib-backed definition of module sheaves explicitly. The delivery remains stage 1 only; the dry run is rerun after these edits.

## Second reading by ND

- Item statement: checked against HRS Example 3.1, BS Lemmas 4.2.12–4.2.13 and the archived `IsLocallyFinitelyPresented` definition; the prime, finite normed extension, topologically noetherian hypothesis, arbitrary characteristic, finite presentation, and absence of completeness assumptions are all retained.
- Item step 1: checked against BS Lemma 4.2.12 and the statements of `lem-weil-pbc-fpqc-detects-openness` and `def-weil-pbc-proetale-site`; fpqc descent and the residue-field tensor-product argument supply the claimed sheaf and ring structure. Verdict: sound and elementary.
- Item step 2: checked against the master point-evaluation lemma, HRS Example 3.1, and the statements of both cited basis nodes; the weakly contractible affine basis and quotient topology are used exactly as stated. Verdict: sound.
- Item step 3: checked against BS Example 4.2.11, `lem-weil-pbc-site-pullback-abelian-exact`, `lem-weil-pbc-profinite-point-pullback`, `lem-weil-pbc-geometric-field-proetale-evaluation`, and `def-weil-proetale-inverse-image`; intrinsic geometric-fibre rank removes presentation dependence. Verdict: sound.
- Item step 4: checked against the flatness definition and Stacks Tag 00HS (`lem-sc-flat-going-down`); the local-ring map has the required flatness and the specialization direction is correct. Verdict: sound.
- Item step 5: checked against Stacks Tags 0052 and 01IS via `lem-sc-noetherian-finite-irreducible-components` and `lem-sc-scheme-sober`; topological noetherianity, finite closed components, and generic points suffice. Verdict: sound.
- Item step 6: checked against the exact inverse-image and coefficient-comparison statements; restrictions preserve the cokernel presentations and make the matrix rank constant on each pulled-back clopen piece. Verdict: sound and elementary.
- Item step 7: checked directly by the displayed block-matrix/Schur-complement calculation; zero-size matrices and rank zero are included. Verdict: sound and elementary.
- Item step 8: checked against the pro-etale covering definition, constructible-stratification definition, and module-category local-presentation clause; coverings compose and no completeness hypothesis is introduced. Verdict: sound and elementary.
- `lem-weil-pbc-condensed-point-basis-evaluation`: checked against BS Lemma 4.2.13(1), HRS Example 3.1, and the master point-evaluation proof; self-contained statement, correct universe/site hypotheses, and correct quotient-topology clause. Empty and one-point profinite cases checked. Verdict: retain as an unsplit input; no existing node states this evaluation formula.
- `lem-weil-pbc-geometric-field-proetale-evaluation`: checked against BS Example 4.1.10 and Example 4.2.11 and the existing exact-sections node; the statement adds the topos identification and algebraically closed extension compatibility without asserting geometric-point conservativity. Empty and singleton covers and arbitrary characteristic checked. Verdict: retain as an unsplit input; no duplicate found.
- New-node form: both nodes are statement-only, self-contained, have definition dependencies, Stacks/paper source places, blueprint provenance, and recorded grep/LeanFinder/Loogle/LeanSearch searches. No Mathlib declaration is an exact match.
- Changes made in second reading: none; the split passed the content, citation, duplicate, blueprint, and preflight checks as written. The existing report's TeX repair is preserved.
