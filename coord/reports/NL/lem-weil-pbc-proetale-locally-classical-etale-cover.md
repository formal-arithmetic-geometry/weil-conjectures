## Worker report

Item: `lem-weil-pbc-proetale-locally-classical-etale-cover`.
Module: `Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover`.
Main declaration: `AlgebraicGeometry.Scheme.proEtale_locallyClassical_etaleCover`.
The theorem is stated with `sorry`; no theorem is proved. The four supporting
fully defined declarations spell out the notions introduced in this very node,
including their canonical restriction. They are listed in `lean.declarations`.
There is no independent new notion requiring a new DAG node, no dependency
repair, and no statement correction.

I read the supplied stage rules, dependency records and their source declarations,
including the current published upstream localization module obtained through
`scompile.py --source`. I read Bhatt--Scholze's PDF, Section 5.1 (Definition 5.1.3
and Lemmas 5.1.1--5.1.4) and Proposition 6.8.4(6), including its final paragraph.
These give exactly the assertions in the node for arbitrary schemes and sheaves
of sets, without Noetherian, connectedness or finite-value-set assumptions.

Clause-by-clause correspondence:

- The scheme is `(X : Scheme.{u})`. A sheaf of sets on its small pro-etale site
  is `(F : Sheaf (ProEt.topology X) (Type (u + 1)))`. The larger coefficient
  universe is the same size convention as the recorded comparison adjunction.
- The comparison inverse image is precisely
  `Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
  (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)`.
  It is the left functor of the recorded `Scheme.proEtaleSiteComparison`,
  not an arbitrary functor or a selected isomorphic replacement.
- Classicality, defined by `IsProEtaleClassical X F`, is
  `∃ G : Sheaf X.smallEtaleTopology (Type (u + 1)), Nonempty (F ≅ ν_X^* G)`.
  In the file the displayed inverse-image term replaces `ν_X^*` verbatim.
- A pro-etale covering family is `(U : I → X.ProEt)` together with
  `(ProEt.topology X).CoversTop U`. On this site with terminal object `id_X`,
  `CoversTop` means the sieve of the structure arrows covers `X`, exactly a
  covering family in its pro-etale topology. This retains the fpqc condition;
  it does not replace it by joint surjectivity.
- `proEtaleSetRestriction X U` is the actual sectionwise restriction:
  precomposition by `MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop`,
  which sends `V → U.left` to `V → U.left → X` and retains underlying arrows.
  The existing `ProEt.isContinuous_overMap U.prop` supplies sheaf preservation,
  explicitly passed to the existing sheaf pushforward constructor. No continuity
  hypothesis or new postponed proof is introduced. Thus its value at a sheaf
  is the node's `F|_U`, with the category and topology of the scheme `U.left`.
- `IsProEtaleLocallyClassical X F` existentially quantifies the preceding cover
  and asks `∀ i, IsProEtaleClassical (U i).left
  ((proEtaleSetRestriction X (U i)).obj F)`. In particular each member has its
  own etale sheaf `G_i`; there is no extra descent datum imposed on these choices.
- The first theorem conjunct is
  `IsProEtaleLocallyClassical X F → IsProEtaleClassical X F`, rendering
  "Every locally classical F is classical."
- `IsProEtaleLocallyConstant X F` quantifies such a cover and, separately for
  each `i`, a set `S : Type (u + 1)` and a `Nonempty` isomorphism from the
  restricted sheaf to `(constantSheaf (ProEt.topology (U i).left)
  (Type (u + 1))).obj S`. This is exactly sheafification of a constant presheaf,
  using the dependency's Mathlib declaration. The value sets may vary with `i`.
- The second conjunct states that such local constancy implies local
  classicality and classicality, expressing the node's "in particular" and the
  source's explicit passage from locally constant to locally classical.
- In the third conjunct `IsProEtaleLocallyClassical X F` is the classicality
  hypothesis. Its other hypothesis is an existential pro-etale cover with
  `∀ i, Nonempty (F.obj.obj (op (U i)))`. This says precisely that sections
  exist on every member, with no compatibility assumption.
- Its conclusion is an existential `(Y : I → X.Etale)` with
  `X.smallEtaleTopology.CoversTop Y` and
  `∀ i, Nonempty (F.obj.obj (op ((toProEt X).obj (Y i)))))`.
  The topology condition is the etale covering condition, equivalently joint
  surjectivity here. The evaluation uses the recorded inclusion to regard an
  etale object as a pro-etale object, giving exactly `F(Y_i) ≠ ∅`.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: publicly exposes the
  recorded small site `Scheme.ProEt` and `Scheme.ProEt.topology` from Mathlib.
  The derived category itself is irrelevant to this set-valued statement.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`,
  `Scheme.Etale`, and its covering-family criterion.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, whose actual left functor is used above.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `Scheme.toProEt`, `Scheme.ProEt.isContinuous_overMap` and the upstream
  localization functor `MorphismProperty.Over.map` used through that interface.
- `Mathlib.CategoryTheory.Sites.CoversTop.Basic`:
  `GrothendieckTopology.CoversTop`, `coversTop_iff_of_isTerminal`.
- Proof-only imports preserve the recorded plan: `Sheaf.RingTheory.IndPrincipalZariski`
  (`Algebra.IsIndPrincipalZariski`, with upstream `Algebra.IndEtale`);
  `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
  (`Scheme.AffineProEt.isCoverDense_toProEt`,
  `isEquivalence_sheafPushforwardContinuous_toProEt`,
  `exists_finite_jointly_surjective_of_mem_topology`, `isPullback_left`);
  `Sheaf.RingTheory.IndEtaleStability`
  (`RingHom.indEtale_principalZariski_stability`);
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
  (`Scheme.ProEt.weaklyEtale_localization`).
  The proof dependencies `lem-weil-pbc-comparison-sections` and
  `lem-weil-pbc-comparison-pullback` have no recorded modules, so cannot yet be
  imported; they remain explicit in the complete four-step proof docstring.
  They are proof prerequisites, not missing objects needed to type this statement.

Edge cases checked:

- Empty scheme: all index types are allowed to be empty. The empty family covers
  its terminal object, and the conclusion does not demand a nonempty etale family.
- Empty constant set: allowed because no `Nonempty S` is assumed. Over a nonempty
  scheme the section hypothesis then fails, as it should; it is not silently supplied.
- Arbitrary infinite sets and disconnected schemes: no finiteness, common cardinality
  or uniform constant set is required. The witness sets vary over the cover.
- The identity cover is permitted, and classicality is up to isomorphism, not equality.
- The pro-etale cover witnessing classicality need not be the cover carrying sections.
  These are separate existential quantifiers.
- All site and coefficient universes are bound explicitly; `I : Type (u + 1)`
  covers families of objects of the small sites, and matches the comparison's
  common larger universe. There is no added equality between site object and
  morphism universes and no hidden auto-bound variable.

Searches (through the prescribed `msearch.py` wrapper):

- `leanfinder`: "A locally classical sheaf of sets on the pro-etale site comes
  from the etale site and local sections descend to an etale cover". Eight hits:
  small/big etale sites, the etale forgetful functor, the small etale pretopology,
  two etale-locus lemmas, generic sheaf localization and the etale pretopology.
  None states local classical descent or descent of sections. The site and
  covering signatures were read in the pinned Mathlib sources.
- `loogle`: `"Sheaf", "constant"`. Twelve hits, including `constantSheaf`,
  `Sheaf.IsConstant`, essential-image characterizations and constant-sheaf
  invariance. Their generic constant-sheaf interface was read; it is reused
  rather than redefined. They do not provide local classical descent.
- `grep`: `locallyClassical|LocallyClassical|proetale.*classical`. Zero Mathlib hits.
- `leansearch`: "A locally classical sheaf on the pro-etale site is classical".
  Unavailable: service returned Internal Server Error. No mathematical verdict
  is inferred from that failure.
- `rg` of the upstream source, the 51-module side framework and `lean/Sheaf` for
  `locallyClassical|LocallyClassical` and the exact blueprint id found no matching
  declaration (only a proof-plan citation in `LisseLatticeEtaleLocal.lean`).
- `rg` of DAG nodes for locally classical terminology found only this item;
  its source definitions therefore belong to this item's own module.
- Exact-name searches in Mathlib, upstream, `lean/Sheaf` and
  `dag/lean_names_upstream.json` found no previous declarations with any of
  the five delivered names. Generic `CoversTop` was found and reused.

Validation: `scompile.py` compiles the delivered module cleanly with no warnings.
The initial inferred localization-continuity argument failed instance search;
passing the already published instance explicitly resolved it without a new
hypothesis or a new theorem. Each declared definition has real data. The only
`sorry` is the named main theorem corresponding to this DAG node.


## Second reading by NL

I independently read the node and complete delivered module, the five statement
prerequisites and their recorded source signatures, and the Bhatt--Scholze source
at Section 5, Section 5.1 (5.1.1--5.1.4), and the last paragraph of 6.8.4(6).
Section 5 starts with an arbitrary scheme X; Lemma 5.1.4 has no Noetherian,
affineness, connectedness, or finite-set hypothesis. Although Proposition 6.8.4
concerns lattices, the section-descent passage uses only the classicality and
inhabitedness of its set-valued sheaf, exactly as extracted by this node.
The supplied source is Bhatt--Scholze, not a Stacks-tagged theorem; I checked its
standing hypotheses rather than importing those of the lattice application.

My object/hypothesis/conclusion checklist, with verdicts:

1. Arbitrary scheme: `(X : Scheme.{u})`, with only bound universe `u` and no
   further instances. This is the recorded Mathlib Scheme. Exact.
2. Small pro-etale site and set sheaf: `(F : Sheaf (ProEt.topology X)
   (Type (u + 1)))`. The recorded ProEtaleDerivedCategory module exposes the
   actual Mathlib weakly-etale over-category and fpqc-generated topology; no
   derived category or coefficient ring is smuggled into this statement. Exact.
3. Comparison inverse image: `IsProEtaleClassical` uses precisely
   `Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
   (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)`, the left functor
   of the recorded `proEtaleSiteComparison`. I opened that definition: its
   adjunction is the canonical sheaf-pullback construction, not an arbitrary
   chosen equivalence. `toProEt` is identity on schemes and underlying arrows.
   Exact.
4. Classicality: existential etale sheaf `G` followed by `Nonempty (F ≅ ... G)`
   expresses essential-image membership up to isomorphism. No selected G or
   equality of presentations is imposed. Exact.
5. Restriction to a cover member: `proEtaleSetRestriction X U` precomposes
   with `MorphismProperty.Over.map ... U.prop`. I opened OverAdjunction's
   definition: its object has structure map `V.hom ≫ U.hom`, and it retains
   the underlying morphism. `sheafPushforwardContinuous` is literally
   precomposition of presheaves. The supplied upstream `isContinuous_overMap`
   ensures the sheaf condition with no new hypothesis. Thus this is F|_U on
   the scheme U.left, not just pullback along an unrelated functor. Exact.
6. Local classicality: `IsProEtaleLocallyClassical` quantifies `I`, `U`,
   `(ProEt.topology X).CoversTop U`, then for every member its own classical
   presentation. I read CoversTop and `coversTop_iff_of_isTerminal`: with
   terminal object id_X it is precisely coverage by the structure arrows.
   The fpqc requirement is retained, not reduced to mere surjectivity. Exact.
7. First conclusion: the theorem's first conjunct is
   `IsProEtaleLocallyClassical X F → IsProEtaleClassical X F`. Exact.
8. Locally constant case: `IsProEtaleLocallyConstant` quantifies a pro-etale
   cover, then a possibly different `S : Type (u + 1)` for each member and an
   isomorphism to `constantSheaf ... .obj S`. I read constantSheaf: it is
   `Functor.const ... ⋙ presheafToSheaf`, as the node requires. The second
   conjunct gives local classicality and classicality; the intermediate clause
   is the stated source implication and follows from the definitions. Exact.
9. Sections hypothesis: the third conjunct assumes local classicality and a
   separately existential pro-etale cover with `∀ i, Nonempty (F.obj.obj
   (op (U i)))`. The section cover need not coincide with the classicality
   cover. There is no compatibility condition or global section hypothesis.
   Exact.
10. Etale-cover conclusion: existential `Y : I → X.Etale`,
    `X.smallEtaleTopology.CoversTop Y`, and nonempty evaluations at
    `((toProEt X).obj (Y i))`. I checked smallEtaleTopology's generated-sieve
    criterion: coverage means joint surjectivity. The evaluations therefore
    mean precisely F(Y_i), with no etale sheaf substituted for F. Exact.

Edge cases: the index types have no Nonempty instance, so the empty scheme and
empty covers are retained. Constant value sets may be empty or infinite, and
may vary over disconnected members. The identity cover is allowed. There is
no rank, n, characteristic, field, or finiteness parameter to restrict. The sites
have objects in Type (u+1), morphisms in Type u; the set universe and family
universe are the recorded common larger universe u+1. Arbitrarily indexed
families have small equivalent subfamilies because these sites have only
u+1-small object collections; the statement makes no smaller-cardinality bound.
No equality of object and morphism universes is assumed, and every variable
and universe in the delivered declarations is bound.

Independent searches, using different wording from the worker:

- `msearch.py ... leanfinder "Essential image of etale sheaf pullback to weakly
  etale site is local for covering families"`: eight hits. Their returned types
  concern small/big etale topologies, generic local sheaf equivalences, or
  condensed topologies, not classicality or this section-descent theorem.
- `msearch.py ... loogle '"Sheaf", "IsLocallyConstant"'`: zero hits.
- `msearch.py ... grep 'etale.*essImage|locallyClassical|IsLocallyConstant'`:
  hits concern etale points, locally constant functions, and flat rank; none
  defines the pro-etale notions or supplies the theorem.
- Direct rg across pinned Mathlib, upstream WeilConjectures, the exact group
  clone's WeilConjectures framework and lean/Sheaf found no existing classicality
  predicate or theorem. I also searched local-constancy terminology and opened
  `ConstructibleSheaf/Defs.lean`: its `LocallyConstantDatum` and
  `IsLocallyConstantSheaf` are for small ETALE sheaves with abelian-category
  coefficients, not the pro-etale set sheaf here. They are not usable duplicates.
  The DAG's classicality hits are this node and citations of it, not a separate
  definition node. The four helpers spell out notions already owned by this node.

No new nodes, dependency modules, statement_change, or mismatches were found.
The recorded localization, affine-basis and stability signatures support the
four-step proof docstring; the two unrecorded comparison proof prerequisites
are correctly left as textual proof dependencies rather than invented imports.
All four definitions contain actual data and the sole postponed theorem is
this node's named theorem. Source/blueprint docstrings and the proof's four
steps are present. No file-local notation, private copy, or proof was added.
I left the correct Lean and node untouched and added this independent report.
The exact theorem signature was mechanically compared with lean.statement;
they are verbatim equal. All Lean lines are at most 100 characters.

Validation: the delivered file passed the prescribed scompile.py wrapper with
no errors or warnings (sandbox and library passes). Delivery preflight and
final delivery are run after this reading.
