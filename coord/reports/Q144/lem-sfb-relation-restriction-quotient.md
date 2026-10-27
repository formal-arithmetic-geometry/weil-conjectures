## Worker report

Module: `Sheaf.AlgebraicGeometry.RelationRestrictionQuotient`.
Declaration: `AlgebraicGeometry.AlgebraicSpace.relation_restriction_quotient`.
Stage 2 only: the sole theorem has proof `sorry`; there are no new definitions.
The previous ending concerned a stage-1 unchanged split. The live item is split and
reviewed by Q41 but has no Lean record. This is its stage-2 statement, as authorized
by the handoff in coord/brief-stage2.md §0; the accepted split is preserved.

Source read: literature/stacks-project/groupoids.tex, labels
lemma-quotient-groupoid-restrict (02VH) and
lemma-quotient-pre-equivalence-relation-restrict (045Z), including their proofs.
The former uses the saturation map through t followed by s and assumes no property
of g. The current blueprint unit sk-thm-sf-ctf-stability was also read.

Hypothesis and clause correspondence:

- A scheme S in a chosen bound: `{S : Scheme.{u}}`, with explicit `universe u`.
  V, R, A and all test schemes belong to `Over S`, the big bounded slice site.
  All pullbacks are in this same category. There are no affineness, separation,
  characteristic or finiteness assumptions on these schemes.
- The pair s,t of S-morphisms: `(s t : R ⟶ V)`.
  `[Mono (prod.lift s t)]` is precisely injectivity on all test-scheme sections
  into the product. `hrel` says the image relation
  `∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b` is an equivalence relation for every T.
- Any S-morphism g: `(g : A ⟶ V)`, with no instances or further assumptions.
- R_A is written directly as `pullback (pullback.snd g t ≫ s) g`. Its points
  are (a,r,b) with `g a = t r` and `s r = g b`. The ordered projections (b,a)
  are `pullback.snd (pullback.snd g t ≫ s) g` and
  `pullback.fst (pullback.snd g t ≫ s) g ≫ pullback.fst g t`.
  Both appear explicitly under `yoneda.map` in the signature, without any
  etaleness assumption or dependency on an etale-restriction theorem.
- Sectionwise quotient presheaves: `coequalizer (yoneda.map s) (yoneda.map t)`
  and the coequalizer of the two indicated restricted projections. Colimits in
  Type-valued functor categories are pointwise; for an equivalence relation their
  coequalizer is exactly the quotient set, rather than an unrelated presentation.
- The fppf sheafifications: F,F' are sheaves for `Scheme.fppfTopology.over S`;
  η,η' have the quotient presheaves as sources. hη,hη' say precomposition with
  these units is bijective for every sheaf G. This is exactly the adjunction
  universal property of the recorded sheafification notion. It specifies chosen
  sheafifications without imposing existence of sheafification on *all*
  Type-u presheaves on the big site. This is the established interface of
  EtaleRelationRestrictionQuotient and EtaleRelationQuotient, not a new notion.
- The canonical morphism: `∃ α : F' ⟶ F` with the equation from the restricted
  quotient projection through η' and α.hom to the original quotient projection
  after `yoneda.map g`. The equation uniquely determines α: the coequalizer
  projection is epi and hη' is injective. Thus the existential does not permit
  choosing an arbitrary comparison map or strengthen the source by extra data.
- The unconditional conclusion is `Mono α` in the sheaf category itself.
- The saturation map h_A is `(pullback.snd g t ≫ s).left`, the underlying scheme
  morphism of the S-morphism. Its three stated conditions are precisely
  `Surjective`, `Flat`, `LocallyOfFinitePresentation`; the conclusion is
  `IsIso α`. They occur as implications in the second conclusion, so do not
  restrict the unconditional monomorphism assertion.

Dependency declarations and modules read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom.
- def-weil-size-convention: explicit universes and bounded Over S objects; this
  convention node deliberately supplies no separate Lean object.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  CategoryTheory.Limits.pullback, pullback.fst, pullback.snd; schemes have
  pullbacks via Mathlib.AlgebraicGeometry.Pullbacks.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation.
- Mathlib.CategoryTheory.Sites.Sheafification: presheafToSheaf,
  sheafificationAdjunction, toSheafify; the signature uses their exact reflection
  universal property for these two chosen quotient presheaves.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: Scheme.fppfTopology, fppfPrecoverage;
  Mathlib.CategoryTheory.Sites.Over: GrothendieckTopology.over.
- Proof-plan imports: WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
  (CategoryTheory.sheafification_sections_local),
  WeilConjectures.CategoryTheory.SiteCoveringsCommonRefinement
  (CategoryTheory.Precoverage.siteCoverings_common_refinement), and
  Sheaf.CategoryTheory.SiteCoveringAxioms
  (CategoryTheory.Precoverage.IsSiteForCoverings).

Edge cases: g=id gives the same quotient. For the diagonal relation on V, the
restricted relation is the kernel pair of g. The comparison describes the fppf
sheaf image of g and is monic even when g itself is not mono. The restricted
relation is diagonal on A only when g is mono. A empty gives an empty quotient and cannot have a covering saturation
unless V is empty. V empty forces A,R empty and the comparison is an isomorphism.
For the full relation on a nonempty scheme, g need not be flat even when its
saturation map is an fppf cover; the signature permits this case. No nonempty
index or nonzero object assumptions occur. Reversing the two restricted
projections is harmless to the quotient, but is done explicitly to match the
node's ordered pair (b,a).

Searches (raw wrapper results retained in searches.jsonl):

- msearch leanfinder: "An equivalence relation of schemes restricted along any
  morphism induces a monomorphism of fppf quotient sheaves and an isomorphism
  when the saturation map is an fppf cover". Eight hits, chiefly generic sheaf
  mono criteria and scheme monomorphisms; no exact match.
- msearch leanfinder repeated after the provider interruption with query
  "Restriction of scheme equivalence relation gives monomorphism of fppf quotient
  sheaves and isomorphism under saturation cover". Eight hits, again no match.
- msearch loogle: `"Scheme", "quotient"`. Three hits, all Scheme.Hom.liftQuotient
  or its composition equations for maps to Spec(A/I); not this theorem.
- msearch grep: `quotient.*relation|relation.*quotient`, Mathlib/AlgebraicGeometry.
  No hits.
- msearch leansearch: restriction of an equivalence relation on schemes and the
  surjective flat locally finitely presented saturation criterion; no exact match.
- rg on lean/WeilConjectures and lean/Sheaf for relation/quotient/restriction and
  the exact item id. No upstream item match. The Sheaf etale-restriction theorem
  assumes s,t,g etale, and its isomorphism criterion uses surjectivity of g;
  it is not this statement. Its three general pullback definitions are reused.
  The groupoid-restriction DAG sibling assumes g is an fppf cover, so is not an
  exact existing match either. Exact declaration-name search found no collision.

Validation after the repair: scompile.py compiled both its private sandbox probe
and the actual library module in 11.0 s and 9.3 s respectively, with no errors or unexpected
warnings. All variables and the universe are explicitly bound. The module has
only the named theorem and its whole proof is sorry; its docstring carries all
five steps of the accepted proof. No statement correction, new node, dependency
replacement, or STATEMENT-DISPUTED issue is needed.

## Second reading by Q144

Author's separate final reading (no sub-agent started, as required by dispatcher).
Compared the node, source and complete signature again. The general scheme and
S-morphism binders match; monicity plus hrel is exactly the sectionwise equivalence
relation. Checked the inlined pullback orientation: first pull back t, then s;
`pullback.snd` gives b and the composite of the two `pullback.fst` maps gives a,
so the ordered projections are (b,a). Both quotient units have the reflection universal property over all
sheaf targets. Their projection equation identifies the canonical comparison.
The result is Mono in sheaves unconditionally, with all three conditions on the
saturation map and IsIso only under them. No hypothesis on g was introduced.
No mismatch requiring a statement change was found. The statement dependencies
now agree exactly with the live node: the fibre-product dependency provides
all the pullbacks and projections directly.
The independent maintainer review remains the independent reading of this delivery.

## Repair of returned head 3fa9c62f140b

H2 is repaired using the return's explicit inlining option. Removed
`lem-trf-etale-relation-restriction-quotient` from `stmt_deps` and removed its
module import. Replaced every use of its two named projection definitions by
its exact pullback expression, preserving the domain
`pullback (pullback.snd g t ≫ s) g` and the order (b,a). Imported the Mathlib
modules directly for scheme pullbacks, underlying-map surjectivity, the fppf
site, the over topology and sheafification. The ordinary Mathlib pullback
notion is already carried by `def-pc-fibre-product`; no new definition node
or duplicate declaration is introduced. Updated the theorem docstring and
Lean record to reflect this repair. The statement, proof plan and every
other DAG field agree with current main. The saved packet's first dry run
passed as 57e0bfbdbfc, but that alone did not repair the independent review.

Self-check: after expansion the first quotient projection is b, the second
is a. All equivalence-relation and chosen-sheafification hypotheses are the
same; the projection equation, unconditional Mono and conditional IsIso
clauses are unchanged under definitional expansion. Rechecked g=id, empty
A and V, diagonal and full relations with non-flat g; none needs a property
of g. The sole postponed proof remains the named theorem with its five-step
docstring. No new node, statement correction or dependency module is needed.
