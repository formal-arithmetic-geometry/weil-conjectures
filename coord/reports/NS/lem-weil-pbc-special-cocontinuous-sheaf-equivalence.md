## Worker report

Repair of L's H3 return on immutable head 035e407b6233. The previous author and
second reader incorrectly identified Mathlib's strict indexed composition class
with the site convention. This repair changes the Lean signatures and adds two
dependency modules; it is not an unchanged re-push. No informal statement changes.

The main theorem is `CategoryTheory.specialCocontinuous_sheafEquivalence` in
`Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence`. Its proof remains `sorry`.
Sources reread: Stacks sites.tex Definition 00VH and its clarification that (3)
requires some choice of covering fibre products; Definition 00WV; Lemma 03A0.
The complete six-step natural-language proof remains in the theorem docstring.

Hypothesis and clause correspondence, after repair:

- Small categories: `{C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]`.
- Actual coverings: `(J : Precoverage C) (K : Precoverage D)` retain the original
  presieves, without replacing them by saturated covers.
- Sites: `(hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)`. The repaired
  dependency's first conjunct `HasIsos` gives singleton isomorphism covers.
  Its second conjunct uses `R.bind T`, exactly the distinct-arrow composition
  of Mathlib `Pretopology.transitive`. Its third conjunct says every covering
  family has, along every arrow, some family of fibre products whose projections
  form a covering: `IsPullback (p i) (q i) b (a i)` and `ofArrows P p ∈ J Y`.
  It does not require global pullbacks, arbitrary choices of pullbacks, or strict
  composition independently at every repeated index. This repairs the faulty
  precoverage-class convention, preserving the actual covers and their topology.
- Given functor: `(f : C ⥤ D)`.
- All five special-cocontinuity conditions: the unchanged recorded upstream
  predicate `(hf : f.IsSpecialCocontinuousForCoverings J K)`. Its conjuncts are
  cocontinuity for generated topologies; preservation of actual covers and
  covering pullbacks; local equality of arrows with equal images; local lifting
  of arrows between image objects; actual target covers by image objects.
  No global full/faithful/essentially-surjective assumption appears.
- Set sheaves: `Sheaf K.toGrothendieck (Type u)` and
  `Sheaf J.toGrothendieck (Type u)`, using the unchanged generated topologies.
- Equivalence: `∃ e : Sheaf K.toGrothendieck (Type u) ≌
  Sheaf J.toGrothendieck (Type u)`.
- Its inverse image is restriction: `Nonempty (e.functor ⋙ sheafToPresheaf ... ≅
  sheafToPresheaf ... ⋙ (Functor.whiskeringLeft _ _ (Type u)).obj f.op)` identifies
  entire presheaf functors, including sections, restriction maps and sheaf maps.
  The fully faithful sheaf inclusion therefore identifies the equivalence with
  precomposition, not merely an abstract equivalence of the categories.
- The associated morphism of topoi is an equivalence: the repaired adjunction
  identifies exactly this restriction with its inverse image and the canonical
  cocontinuous pushforward with its direct image. Its finite-limit preservation
  supplies the morphism-of-topoi condition. Uniqueness of right adjoints makes
  that direct image the quasi-inverse. No arbitrary geometric morphism is used.

The item adds the already recorded adjunction node to stmt_deps, as authorized
for landed nodes and dependency repair. Apart from this addition, only `lean`
changes. Both dependency node copies change only `lean` with explanatory `note`.
No new DAG node, statement_change, or STATEMENT-DISPUTED is needed.

## Dependency modules

1. `def-weil-pbc-sites-and-cohomology`:
   `Sheaf.CategoryTheory.SiteCoveringAxioms`,
   `CategoryTheory.Precoverage.IsSiteForCoverings`.
   The previous record required strict indexed composition. For a finite
   covering presieve, an infinitely repeated identity presentation allows a
   different finite refinement at each index; the strict class would force
   the infinite union of distinct arrows to be finite. The repair uses the
   existing presieve bind operation from `Sites/Sieves.lean`, as does Mathlib's
   `Pretopology.transitive`. Unlike `Pretopology`, it needs only covering
   pullbacks. These are existential actual pullback squares, with a covering
   presieve of projections, in accordance with the clarification following
   00VH(3). All data in this Prop-valued definition is explicit; no sorry or
   choice of topology or sheaf is introduced. The remaining node notions are
   unchanged existing Mathlib declarations, publicly imported:
   `Precoverage.toGrothendieck`, `Sheaf`, `Sheaf.H'`,
   `Sheaf.cohomologyPresheafFunctor`, and their associated site infrastructure.
   This module repairs the site's unusable component, not its cohomology.
2. `lem-weil-pbc-continuous-cocontinuous-topos-adjunction`:
   `Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings`,
   `CategoryTheory.continuousCocontinuous_toposAdjunctionForCoverings`.
   The old theorem imposed the same strict classes and could not justify the
   main theorem on finite-covering sites. The new signature replaces only
   those site assumptions with `hJ`, `hK` as above. The covering-preservation
   hypothesis `hcover`, covering-pullback-preservation hypothesis `hpullback`,
   and generated-topology `IsCocontinuous` are unchanged. The conclusion retains
   all clauses: the restriction functor L and natural presheaf identification;
   adjunction to the canonical `sheafPushforwardCocontinuous`; finite-limit
   preservation; the exact subtype of compatible families; substitution along
   target arrows; componentwise action on sheaf maps; evaluation counit at
   `(U,id)`; and the unit family `G.obj.map ψ.op t` under the restriction
   identification. Its ten-step proof docstring is retained and its proof is
   `sorry`. The repaired site predicate is used, not a private second copy.

Other dependencies inspected and used:

- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`,
  `CategoryTheory.Functor.IsSpecialCocontinuousForCoverings`: full current source
  read using `scompile.py --source`; it already avoids strict composition.
- Current source of the original adjunction read using the same source wrapper;
  compared its full signature, docstring and all four componentwise equations.
- Mathlib `Sites/Precoverage.lean`, `Sites/Pretopology.lean`,
  `Sites/PrecoverageToGrothendieck.lean`, `Sites/Sieves.lean` signatures and
  docstrings read. `Pretopology` demands all pullbacks, so it cannot replace
  arbitrary sites directly. `Precoverage.IsStableUnderBaseChange` additionally
  demands all choices of pullback squares, stronger than 00VH's existential
  choice. The repaired predicate avoids both extra restrictions.
- `Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf` and Mathlib
  `Sites/Limits`/`Sites/Sheafification` remain the adjunction proof imports.
  The first theorem's strict site signature will need its direct sheaf-condition
  argument rather than direct specialization on the repaired sites; no theorem
  is silently applied or proved in this stage-2 statement delivery.

Edge cases: finite covers compose by a finite set of distinct first arrows and
finite further covers; repeating an index no longer forces an infinite cover.
Pullbacks are required only along members of a cover, so categories lacking
unrelated pullbacks are admitted. Empty covers and empty categories remain
allowed; an empty cover forces singleton sections. Empty source with nonempty
 target is compatible with density exactly when targets admit empty covers.
Identity functors give the identity restriction equivalence. All sites, arrows,
sets and needed indexing pairs fit in the common arbitrary universe u; the site
predicate also explicitly binds the general object and arrow universes u,v.
No nonemptiness or unrelated finite-limit assumption has been introduced.

Searches (repair, additional to searches.jsonl from the original delivery):

- LeanFinder via msearch.py: "Pretopology axioms composition by presieve bind
  and pullbacks of covering arrows only". Eight hits: Pretopology.transitive,
  Pretopology.pullbacks, Pretopology, toPretopology and variants. Full signatures
  inspected: all bundled Pretopology variants demand global HasPullbacks.
- Loogle via msearch.py: "CategoryTheory.Pretopology". Twelve hits confirming
  the same global-pullback restriction. No partial-pullback site predicate.
- Grep via msearch.py: "structure Pretopology|IsStableUnderComposition|def bind"
  in CategoryTheory/Sites. Twenty-five hits; Precoverage.lean explicitly warns
  its indexed composition is stronger than Pretopology. Sieves.lean supplies
  the reused bind operation. No exact partial-pullback site predicate.
- rg across dag/nodes, lean and WeilConjectures for IsStableUnderBind,
  IsSiteForCoverings and SiteAxioms: no matches before this repair.
- Original LeanFinder/Loogle/grep searches in searches.jsonl found dense-subsite
  equivalences, but no exact special-cocontinuous theorem. Their local fullness,
  faithfulness and covering-sieve iff interfaces require a mathematical bridge.

All three modules were compiled together through the required scompile.py,
which compiled each separately in dependency order with a private overlay.
No errors or warnings were emitted. No repository edit, direct git command,
live-library write, global build, or delivery push was performed by this worker.

## Earlier second reading (a previous round; superseded)

The second reading in the returned delivery was superseded by L's H3 finding.
Its claim that strict composition exactly expresses the site axioms was wrong.
This repair is prepared for a fresh second reader; this section records that
history and does not claim an independent review of the repaired delivery.

## Second reading by NS

I independently read the repaired delivery, the three node copies and their base
records, Stacks sites.tex Definition 00VH (including its clarification), Definition
00WV, and Lemma 03A0. I fetched the current published source of
`WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings` through
`scompile.py --source` and read its complete predicate. There is no statement
correction and no new node in this delivery. I found no further signature repair
necessary; I left all three Lean files and all node signatures unchanged.

Object, hypothesis and conclusion checklist (all pass):

1. Two small sites: `{C : Type u} [SmallCategory C]` and the same for `D`
   supply arbitrary small categories in a common ambient universe. `J`, `K`
   are their actual covering presieves; `hJ`, `hK` supply the site's axioms,
   rather than assuming a topology is the specified set of actual covers.
2. Site axiom (i): `IsSiteForCoverings` begins with `J.HasIsos`, whose
   declaration requires each singleton isomorphism to cover. Pass.
3. Site axiom (ii): its second conjunct uses `Presieve.bind`, with a covering
   refinement for each distinct covering arrow. I read `Presieve.bind` and
   `Pretopology.transitive`: their composite arrow is `g ≫ f`. This is the
   presieve encoding of composition, without requiring independently chosen
   refinements at repeated indices of every presentation. In particular finite
   covering presieves are admitted. The source uses indexed families; the
   presieve encoding forgets repetition, not the source's local descent data.
   It must not be confused with the stronger indexed Precoverage class. Pass.
4. Site axiom (iii): for every covering `ofArrows U a` and every `b : Y ⟶ X`,
   the last conjunct supplies objects `P i`, projections `p i`, `q i`,
   `IsPullback (p i) (q i) b (a i)`, and a cover `ofArrows P p`. The orientation
   is correct. These are some choices of actual fibre products, as explicitly
   allowed after 00VH(3). There is no global `HasPullbacks C` assumption and
   no requirement that every isomorphic choice itself be an actual cover. Pass.
5. The given functor is `(f : C ⥤ D)`. `hf` uses the dependency's published
   `Functor.IsSpecialCocontinuousForCoverings`, not a new local predicate. Pass.
6. Cocontinuity, condition (1)/(a): the predicate's first conjunct is
   `f.IsCocontinuous J.toGrothendieck K.toGrothendieck`. I read its `cover_lift`
   signature. On sites as above the generated topology has covering-presieve
   bases, so this expresses precisely source covering refinement of target
   covers, rather than requiring a target actual cover to be literally an
   image family. Pass.
7. Continuity, condition (2)/(b): the next two conjuncts say `R.map f ∈ K _`
   for `R ∈ J _` and `PreservesLimit (cospan a b) f` when `R a`. This is exactly
   cover preservation and preservation of covering fibre products along any
   arrow, as in 00WV. No arbitrary pullback preservation is assumed. Pass.
8. Local faithfulness, condition (3)/(c): equal `f.map a` and `f.map b` give
   a source cover `R` on which every `g` satisfies `g ≫ a = g ≫ b`. Pass.
9. Local fullness, condition (4)/(d): every `c : f.obj X ⟶ f.obj Y` gives
   a source cover and lifts `d` with `f.map d = f.map g ≫ c`. Quantifiers put
   the covering after the given arrow, exactly as in 03A0. Pass.
10. Cover density, condition (5)/(e): for every target object `V`, the last
    conjunct supplies an index type, source objects `U i`, and arrows
    `f.obj (U i) ⟶ V` whose `ofArrows` is an actual `K`-cover. Pass.
11. Sheaves of sets: `Sheaf K.toGrothendieck (Type u)` and
    `Sheaf J.toGrothendieck (Type u)` use the original generated topologies.
    The existential `e` is an equivalence in the required D-to-C restriction
    direction. Pass.
12. Precomposition is the inverse image: the displayed natural isomorphism
    after `sheafToPresheaf` identifies the whole equivalence functor with
    whiskering by `f.op`, including restriction maps and natural transformations.
    This is stronger than an objectwise accidental bijection and exactly the
    node's identification. Pass.
13. The associated morphism of topoi is an equivalence: the repaired adjunction
    node, now explicitly cited in `stmt_deps`, identifies this same restriction
    with the inverse image and the canonical cocontinuous pushforward with its
    right adjoint. Full faithfulness of the sheaf inclusion and uniqueness of
    adjoints identify that right adjoint with the quasi-inverse. Thus the main
    conclusion states the node's geometric equivalence, rather than an
    unrelated equivalence of categories. Pass.

Dependency-module reading (H13): `SiteCoveringAxioms` repairs only the unusable
site-axiom component of `def-weil-pbc-sites-and-cohomology`; it does not introduce
another sheaf, topology, or cohomology construction. The underlying `Precoverage`,
`Precoverage.toGrothendieck`, `Sheaf` and cohomology infrastructure remain Mathlib's.
The data of `IsSiteForCoverings` is an explicit proposition without any sorry.
`ContinuousCocontinuousToposAdjunctionForCoverings` matches its node clause by
clause: its `hcover`, `hpullback` and cocontinuity are exactly the required
hypotheses; `L` and `eL` specify restriction; the adjunction uses the canonical
`sheafPushforwardCocontinuous`; `PreservesFiniteLimits L` gives the morphism of
topoi. The dependent equivalence `e F V` has precisely the node's compatible-family
subtype. Its four subsequent equations give substitution along `h`, componentwise
sheaf maps, counit evaluation at `(U,id)`, and the unit's restrictions along `ψ`.
I checked each equation's source and target under `eL`; all agree. There is no
local fullness, faithfulness or density assumption on this dependency. Both
dependency node copies change only `lean`, with explanatory `note` fields.

Edge cases: empty covering families and empty categories are permitted; all
existential indexed families admit empty types. On an empty cover the sheaf
condition forces a singleton section set, so the proof's gluing and bijectivity
arguments still apply. Empty C with nonempty D is permitted precisely when
cover density can be witnessed by empty covers. No nonempty or finiteness
instance is silently added. Only covering pullbacks are required, so unrelated
missing pullbacks cause no exclusion. Identity functors and identity covers are
included. The common `u` is arbitrary (it can accommodate both small categories
and sets); the predicate separately binds object and arrow universes `u,v` and
indexes by `Type (max u v)`. No independent smaller test universe is used. Zero
objects, schemes, characteristic and degree n do not occur in this statement.

Independent searches (H4):

- LeanFinder, `restriction of sheaves is an equivalence for a locally full
  locally faithful cover dense functor of sites`: eight hits, principally
  `Functor.IsDenseSubsite.sheafEquiv` and its induced-topology variant.
- Loogle, `CategoryTheory.Functor.IsDenseSubsite`: twelve hits. I read the actual
  class and `sheafEquiv` signatures in DenseSubsite/Basic.lean and the equivalence
  instance in DenseSubsite/SheafEquiv.lean. They require the dense-subsite
  sieve-topology interface, including `functorPushforward_mem_iff`; converting
  the present covering conditions to it is mathematical work, not an exact
  existing statement or a direct specialization.
- LeanFinder, `a coverage with identities transitive bind and existence of
  pullbacks only for arrows in covering families`: eight hits, including
  `Coverage`, `Precoverage.toCoverage`, and `Precoverage.HasPullbacks`. I read
  Coverage.lean as well: coverage is a weaker refinement condition, not the
  present identity/composition/existential actual-pullback site predicate.
- `rg` for `specialCocontinuous`, `IsSiteForCoverings`, `IsStableUnderBind`,
  `sheafEquiv` and `IsDenseSubsite` in Mathlib Sites, upstream WeilConjectures,
  and project lean/Sheaf found the dense-subsite infrastructure and scheme
  special cases, but no exact pre-existing theorem or partial-pullback predicate.
  I separately read Pretopology.lean (global HasPullbacks), Precoverage.lean
  (its explicit warnings about stronger composition and base-change classes),
  Sieves.lean (bind), and PrecoverageToGrothendieck.lean (generated topology).

The module/declaration docstrings give the correct source and blueprint IDs.
The main theorem's six proof steps and the adjunction's ten steps retain the
node's descent, choice-independence, naturality, unit/counit and limit arguments.
The main proof avoids the source's erroneous claim that `(U,id)` is final.
Both theorem proofs are only `sorry`; nothing is proved and no data is hollow.
All three `lean.statement` strings were compared verbatim with their signatures
and match. All variables and universes are explicitly bound; no file-local
notation, private construction or local instance is used.

Verification: compiled all three sibling modules through `scompile.py`, in
site-predicate/adjunction/main-theorem dependency order. All passed with no
errors or warnings. The first invocation used relative paths from the read-only
clone and failed before compilation because the sandbox files were elsewhere;
rerunning from the sandbox succeeded. No Lean or node change was needed in
this second reading; this section and independent verification are the additions.
