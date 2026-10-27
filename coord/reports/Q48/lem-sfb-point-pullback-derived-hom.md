## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-point-pullback-derived-hom.json: statement, split into six proof steps; no Mathlib match.
- citations.json: verbatim statement quotes for every step/node pair.
- searches.jsonl: seven actual searches made with the required msearch.py command, with their returned metadata. The item's inherited searches and results are retained.

There are zero new nodes and zero new Mathlib leaves. No Lean, repository, launcher, chapter or unit file was written, and no compiler or build was run.

## Attachments

None. Searches by the exact blueprint tag and by point/pullback/internal-Hom vocabulary in lean/WeilConjectures found no declaration stating this item. Ordinary scheme pullback and condensed pullback composition declarations do not assert this unbounded derived internal-Hom comparison. The parent profinite-functions result and its sorried infrastructure are not a proof of the present item.

## WANTED

No new document is needed for this split. The unavailable historical upstream RefactorInstruction.tex path in the existing point-pullback node's source is not used as an independently verified source here: its statement is used as existing infrastructure. The mathematical proof follows the available Hemo–Richarz–Scholbach PDF and Stacks source identified below.

## Corrections and scope

The imported item has no proof and requires a globalization beyond the literal statement of Hemo–Richarz–Scholbach Proposition 4.3(1). That proposition concerns the component morphism pi_W for a w-contractible affine W, not the condensed-point morphism of an arbitrary scheme. The split factors the latter through the profinite slice, applies the existing component theorem, and detects the cone on the covering basis. It specifies the evaluation transpose at each comparison, so preservation of objects alone is never substituted for equality of the canonical morphisms.

The statement is unchanged, including arbitrary condensed rings, arbitrary unbounded complexes, naturality, and the derived restriction clause. No statement dispute was found. The source and inherited provenance fields are retained. blueprint_refs.py ancestor reports None because the creation chain has a break before an imported blueprint ancestor. The inherited null from.node is retained rather than assigning an invented ancestor. Its already explicit from.place names paragraph (3) of the direct-image proof and the returned profinite-parameter argument; same_as is [] after whole-blueprint searches for internal Hom, condensed-point and component pullback. This is a provenance limitation, not a change of the unit route.

## Not duplicates

No new nodes. In particular, reuse lem-sfb-wcontractible-component-derived-hom rather than restating Proposition 4.3(1), lem-weil-pbc-ringed-internal-hom-exact-restriction rather than creating a profinite slice-Hom lemma, and lem-weil-pbc-ringed-slice-evaluation-transpose rather than hiding evaluation compatibility in an auxiliary node.

## Mathlib search assessment

Both semantic phrasings, both Loogle queries and both grep patterns were actually run and logged. LeanSearch was available for this attempt. LightCondensed.ihomPoints and its naturality formulas were read in Mathlib/Condensed/Light/InternallyProjective.lean, lines 44–78: they concern underived light condensed modules over an ordinary commutative ring and do not specialize to this assertion. The other semantic phrasing returns closed/monoidal light condensed structures; Mathlib/Condensed/Light/Monoidal.lean lines 36–70 constructs these structures, without a scheme condensed-point derived comparison. SheafOfModules.pullback and its adjunction were read in Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean lines 45–64. They define ordinary module pullback as an adjoint and do not prove its closedness on unbounded derived categories. The regex searches have zero hits. No search was inferred from its query or recorded without execution.

## Unfinished work

None at the stage-1 level. The existing component, ringed-site and module-comparison nodes remain their own independent tasks; this delivery supplies the complete one-level split, not Lean proofs of those dependencies.

## Review by Q48

I read the item's chapter, its assigned ctf-stability unit, the three levels of SETUP.md, GOAL.md, the standing stage-1 brief, and delivery-errors B–E in full. The geometric direct-image route of paragraph (3) is unchanged. I read Hemo–Richarz–Scholbach Section 3 (the profinite site, p_X and ordinary condensed coefficients), equation (4.1), and Proposition 4.3(1) with its proof and equation (4.2). The source explicitly permits arbitrary derived objects for component pullback. The extra step from the component theorem to the arbitrary scheme statement is marked agent-written. I also opened Stacks sites-cohomology.tex at lemma-pullback-tensor-product (07A4), lemma-restrict-K-injective-to-open (08FI), lemma-internal-hom (08J9) and lemma-restriction-RHom-to-U (08JB), checking their tags against tags/tags. They impose no boundedness or finite-generation restriction. These are the only external calculations used; no SGA route is cited.

For step 1 I opened all three cited statements. The internal-module equivalence explicitly preserves underlying sheaves and morphisms; the module-object derived comparison explicitly compares the native operations, evaluation and slice restrictions; the sections-model theorem identifies an arbitrary tensor right adjoint with the K-injective Hom model. Thus the step changes presentations without replacing the native operation or silently completing it. For condensed modules the base is the profinite site with its actual ring sheaf, exactly the general-site setting of the sections-model theorem.

For step 2 I checked that the point-pullback node states exact symmetric monoidality and coherent composition on derived module categories, the derived tensor pullback node supplies the full unbounded tensor comparison for an actual ring map, and the closed symmetric monoidal theorem supplies the natural adjunction and its explicit counit formula. Here the ring map is the canonical identification with B, so exact termwise pullback computes derived pullback. Naturality is obtained by transposing the natural evaluation square, before any isomorphism is asserted.

For step 3 I checked the weakly-etale localization node's site-equivalence clause (1). Its separate discrete-coefficient clauses are not used for condensed coefficients. The coefficient comparison instead comes from the point-pullback node's ring/module/derived composition clause. I read the exact-restriction node's all-unbounded slice-Hom isomorphism and the slice-evaluation-transpose node's explicit evaluation and transposition equations. The latter equations identify the restricted comparison with beta_W as a morphism, not merely its endpoints. This establishes the restriction clause for every pro-etale test before using a w-contractible hypothesis.

For step 4 I read the component-relative-profinite-site node: it constructs pi_W, q_S as the profinite slice projection and p_W=q_S pi_W. Restriction on the profinite site is therefore literally the localized-site functor to Prof/S. The same all-unbounded exact-restriction and transpose statements used in step 3 give its canonical invertible Hom comparison, with the specified evaluation normalization. No additional claim that arbitrary inverse images preserve Hom is used.

For step 5 I opened lem-sfb-wcontractible-component-derived-hom and checked that its theorem is about arbitrary K,L in D(Prof/S,Lambda_S), includes the evaluation-adjoint normalization, and excludes any perfectness, boundedness or discreteness assumption. These hypotheses hold for q_S^*K and q_S^*L. I also checked the tensor pullback and closed-adjunction statements cited in this step. The transpose of b composed with pi_W^*a is explicitly the pullback of the original evaluation through the composite tensor comparison. Injectivity of the adjunction bijection proves that this composite is beta_W. This is the small composition argument in the item, not a new node restating its conclusion.

For step 6 I checked that the derived-restriction definition is the termwise functor of an exact module-restriction functor, and that the covering-basis theorem says every pro-etale object is covered by w-contractible affines. Restriction therefore commutes with cohomology and cone triangles. The sheaf separatedness argument is written out: each section of every cohomology sheaf becomes zero on such a covering. It proves vanishing of the cone without a boundedness or convergence argument. I tested the empty scheme, zero inputs, shifted inputs and complexes unbounded in both directions; exact slice restriction and the cited component theorem cover them all. For profinite slices S=empty is harmless as well.

I audited B1–B10: no new node or hidden proof sketch in a statement, no duplicate, unchanged complete statement hypotheses, valid TeX, actual search logs, no claimed Mathlib leaf or finished Lean attachment, and explicit blueprint provenance. I audited C1–C8: every non-elementary input has an existing node, every cited statement was opened and its exact quote placed in citations.json, all dependency closures were checked not to reach the item, and generic off-unit tools are declared individually in split_report.tool_uses. I audited D1–D5: the proof contains the slice factorization, comparison identification and globalization arguments, rather than moving the conclusion to new nodes. I audited E1–E7: all coefficients are the original pulled-back rings, every localization uses its actual slice, arbitrary inverse images are never assumed closed, and equality of transposes is written explicitly. All six steps are below 2000 characters, so none hides an unreviewed long auxiliary argument.
