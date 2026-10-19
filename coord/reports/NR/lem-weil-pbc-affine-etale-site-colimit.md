## Worker report

The module `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit` states
`AlgebraicGeometry.Scheme.exists_affineEtaleSite_colimit`, with `sorry` as its entire proof.
It replaces the inherited file of the same node, which had no current `lean` record.
No definition or proof is introduced. The natural-language statement is unchanged.

### Hypotheses and objects

- The directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. Nonemptiness is part of a directed index set in the source.
  A preorder permits the source's partially ordered sets without restricting them.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. The index lives in the schemes' universe.
- Affine transitions are `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`.
- Quasi-compact and quasi-separated stages are respectively
  `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]` and
  `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`.
- The specified limit and its projections are `c : Cone D`, `hc : IsLimit c`,
  `c.pt` and `c.π.app (op i)`. No extra assumption on the limit is added.
- Each site's objects are the existing `FullAffineEtale`; its finite standard coverings
  are the existing `fullAffineEtalePrecoverage`, and its generated topology is
  `fullAffineEtaleTopology`. These are read in `FullAffineEtaleSite.lean`:
  affine domains, étale structure maps, finite étale jointly surjective families.

### Clause-by-clause correspondence

1. `U i j h` and `v i` are functors between the specified full affine étale categories.
   Thus their images are affine and étale. The natural first projections `p` and `q`
   and the two `IsPullback` conjuncts require exactly the base changes along
   `D.map (homOfLE h).op` and `c.π.app (op i)`, rather than arbitrary functors.
   `U i i le_rfl = 𝟭 _` gives the identity convention.
   The next projection equations characterize the canonical comparisons `gamma` and
   `delta`; their `HEq` normalizations and the two displayed cocycle equations give
   normalized associativity and cone compatibility. Preservation of covering presieves
   and `PreservesLimit (cospan f g)` are the Stacks continuity conditions; the additional
   existential `IsContinuous` witnesses state continuity for the generated topologies.
   Each existential `L` with `Nonempty (L ⊣ ...sheafPushforwardContinuous...)` and
   `PreservesFiniteLimits L` asserts the corresponding morphism of sites. As a left
   adjoint L also preserves finite colimits; no separate redundant clause is added.
   The concluding `F : I ⥤ Cat.{u, u + 1}`, `Q`, `e`, `v'`, `theta`, and `eta`
   implement strictification: `e i` is an equivalence, the covering iff preserves and
   reflects coverings, `theta` compares stage transitions and `eta` compares maps to
   the limit. `(F.map (homOfLE h)).toFunctor ⋙ v' j = v' i` is strict cone
   compatibility; diagram functor laws give strict identity and composition. The Arrow
   equation states compatibility of these comparisons with delta. The `Q` site axioms,
   finite covering presieves, cover and pullback preservation, continuity, and
   finite-limit-preserving left adjoints give the system of finite sites required here.
2. `∀ A : c.pt.FullAffineEtale, ∃ i Ai, Nonempty ((v i).obj Ai ≅ A)` is exactly
   descent of each affine étale object up to isomorphism over X.
3. For each map f at the limit, `∃ j h g` with
   `f = (delta i j h).inv.app A ≫ (v j).map g ≫ (delta i j h).hom.app B`
   states descent at a later stage, with the canonical comparison isomorphisms.
   The following implication `(v i).map f = (v i).map g → ∃ j h,
   (U i j h).map f = (U i j h).map g` is eventual equality.
4. The `∀ n A B f` covering iff uses `Fin n` and `Presieve.ofArrows B f`.
   Its witnesses `i, Ai, Bi, fi, t, s` are a common stage, a standard stage cover,
   and target/source isomorphisms satisfying
   `(v i).map (fi a) ≫ t.hom = (s a).hom ≫ f a`. Every standard finite covering
   family is included, up to bijective reindexing, including the empty family.
5. `K : Cocone F`, object and arrow `IsColimit` witnesses, and
   `(K.ι.app i).toFunctor ⋙ W = v' i` specify the category colimit and induced
   comparison. The defining iff for `P` says precisely that its covers are images
   of stage covers, transported along target equalities. `W.IsEquivalence` and
   `R ∈ P A ↔ R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A)` give the
   asserted equivalence of sites with preservation and reflection of coverings.

### Dependency declarations

Read the dependency records and the declarations/docstrings in these modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition` (the statement uses its cone form).
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`:
  `AlgebraicGeometry.Scheme.fullAffineEtaleInclusion_isContinuous`,
  `fullAffineEtaleInclusion_special_equivalences`, and the cohomology comparison
  declarations. Their shared site definitions come from `FullAffineEtaleSite`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the statement uses `IsPullback` to specify these
  universal products without choosing a second base-change definition.
- `def-weil-pbc-scheme-conventions` defines no new notion: the qcqs instances above
  use its existing Mathlib meanings. The site/cohomology convention node supplies
  `Precoverage`, `Sheaf`, `Functor.IsContinuous`, and `sheafPushforwardContinuous`.
  Cohomology itself does not occur in this lemma.
- `Sheaf.CategoryTheory.SiteSystemStrictification`:
  `CategoryTheory.exists_site_system_strictification`; retained as a statement-dependency
  import. Its unrestricted composition assumptions cannot be applied directly to finite
  standard coverings; the conclusion here uses the existing finite indexed form.
- `Sheaf.CategoryTheory.ColimitSites`: `CategoryTheory.exists_colimit_site`; its
  finite indexed closure axioms are followed in the colimit conclusion.
- Added the already-existing node `def-weil-pbc-finite-precoverage` to `stmt_deps` and
  imported `Sheaf.CategoryTheory.FinitePrecoverage`: the existing classes
  `CategoryTheory.Precoverage.IsStableUnderFiniteComposition` and
  `CategoryTheory.Precoverage.IsStableUnderFiniteBaseChange` are used directly.
- Proof-plan imports are `AffineEtaleBaseChangeSystem`, `AffineEtaleDescentData`,
  `AffineEtaleColimitPresentation`, and
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`. The latter's
  `Scheme.exists_pullback_hom_of_isLimit` and
  `Scheme.exists_pullback_fst_comp_eq_of_isLimit` provide map descent/equality.
  The qcqs permanence proof dependency is a Mathlib leaf. No unstated proof
  dependency is imported by a guessed declaration name.

### Edge cases and inherited file fault

The empty scheme is allowed at every stage and at the limit. `Fin 0` permits its empty
cover. A nonempty target cannot have an empty jointly surjective covering. Singleton
and constant diagrams are allowed, and normalization makes their identity comparisons
explicit. Arbitrary characteristics and nonaffine qcqs stages remain allowed. The site
object universe is u+1 and morphism universe u, as in the actual FullAffineEtale definition;
`Cat.{u, u + 1}` preserves these sizes. No independent smaller index universe is used.

The inherited `exists_affineEtaleSite_colimit` is not an exact existing match. It requires
both finite covering presieves and unrestricted `IsStableUnderComposition` in Q and P.
As documented in `AffineEtaleColimitPresentation.lean`, repeating the identity cover
with an infinite index and refining each copy by a different finite fold cover forces
an infinite covering presieve, contradicting finiteness. This is an inherited Lean
encoding error, not a fault of the natural-language node: standard étale coverings
are finite. This delivery replaces those four occurrences by the already defined finite
indexed axioms and leaves all five natural clauses intact. No second notion or new node
is introduced. The old proof-plan module still has the stronger false conclusion; stage 3
must adapt its finite-family interface before applying it to this statement.

### Sources and searches

Opened `literature/stacks-project/etale-cohomology.tex`, Lemma
`lemma-colimit-affine-sites` (0EYL), including its first (qcqs) proof paragraph.
It uses finite-presentation descent, descent of affineness and étaleness, then descent
of joint surjectivity for coverings, exactly as the node does.

- `msearch.py ... leanfinder`: “The affine etale site of an inverse limit of quasi
  compact quasi separated schemes with affine transition maps is the colimit of their
  affine etale sites”. Eight results on affine limits, affine opens and the affine
  Zariski site; none states this affine étale site-colimit theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.Scheme.FullAffineEtale,
  CategoryTheory.Functor.IsEquivalence`. No hits; FullAffineEtale is unknown to the
  Mathlib index (it is a project definition).
- `msearch.py ... grep`: `affineEtale.*colimit|colimit.*[Ee]tale|0EYL` in
  `AlgebraicGeometry`: no Mathlib hits.
- `rg -n` for `affineEtale.*colimit|affine_etale_site_colimit|
  lem-weil-pbc-affine-etale-site-colimit` in upstream `WeilConjectures` and project
  `lean/Sheaf`: no upstream match; found the inherited project declaration and its
  base-change/descent/presentation modules and citers. Read the full inherited signature
  and the documented refutation before deciding it is not an exact reusable statement.

### Validation

The delivered file compiled cleanly via `scompile.py` on the server: 2.0 seconds,
nice 19, two threads, 60-second per-file limit. No local compiler or global build was run.

## Second reading by NR

Independently read the sandbox node, its entire Lean signature, Stacks
`etale-cohomology.tex`, `lemma-colimit-affine-sites` and its first proof paragraph,
`topologies.tex`, `definition-standard-etale` and `lemma-alternative`, and
`sites.tex`, `situation-inverse-limit-sites` and `lemma-colimit-sites`.
The node deliberately treats the qcqs case of 0EYL. The source's extra phrase
that X is qcqs is a consequence of the stage hypotheses and affine transitions,
not a missing assumption on the specified limiting cone.

Object/hypothesis/clause inventory, matched against the Lean:

- Directed index set I: `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. Correct; the preorder generalization introduces no
  extra hypothesis on a directed partially ordered set.
- Schemes and inverse transitions: `D : Iᵒᵖ ⥤ Scheme.{u}` and the dependent
  `IsAffineHom (D.map a)` instance. Correct direction: `homOfLE h` is reversed
  by `.op`, giving X_j to X_i for i ≤ j.
- Every stage qcqs: `CompactSpace (D.obj i)` and
  `QuasiSeparatedSpace (D.obj i)`. Correct, with no affine-stage, Noetherian,
  separated-stage, base-field, or characteristic assumption.
- Specified limit X and projections: `c : Cone D`, `hc : IsLimit c`,
  `c.pt` and `c.π.app (op i)`. Correct; no chosen limit or additional
  property instance on X is required from the caller.
- Small affine étale categories and their standard covers:
  `FullAffineEtale`, `fullAffineEtalePrecoverage`, `fullAffineEtaleTopology`.
  Correct. Opened their definitions: objects are full-subcategory objects of
  `Scheme.Etale` with affine domain; covers are finite jointly surjective
  families of étale arrows. “Standard” does not require each arrow to be a
  standard étale morphism, exactly as the source explicitly warns.
- Clause (1), base change: the existential functors `U`, `v` land in the
  correct categories; natural transformations `p`, `q` and both `IsPullback`
  conditions specify actual scheme base changes along the transition and
  limit projection. Thus they do not merely assert arbitrary functors.
  `U i i le_rfl = 𝟭 _` is the requested identity convention. Verdict: correct.
- Clause (1), coherence: `gamma`, `delta`, their first-projection equations,
  normalized `HEq` equalities, the four-index gamma cocycle and three-index
  delta compatibility say precisely canonical iterated-pullback coherence.
  Fullness and the pullback universal properties determine these comparisons.
  Verdict: correct.
- Clause (1), continuity and site morphisms: cover preservation and
  `PreservesLimit (cospan f g)` give Stacks continuity, while the existential
  `IsContinuous` instances give Mathlib continuity on generated topologies.
  Each `L` is a left adjoint to the specified restriction functor and preserves
  finite limits. Left adjointness already implies preservation of finite
  colimits, so no exactness clause is lost. Verdict: correct.
- Clause (1), strictification: `F : I ⥤ Cat.{u, u + 1}`, `Q`, `e`, `v'`,
  `theta`, `eta`, equivalence and covering iff for `e`, functor laws of F,
  and `(F.map (homOfLE h)).toFunctor ⋙ v' j = v' i` provide the strict
  system. The Arrow equation compares theta/eta with the same delta, including
  endpoint transports. Q has finite covers and the existing finite indexed
  axioms, cover/pullback preservation and continuous exact inverse images.
  Verdict: correct finite-site form of the node, not unrestricted composition
  on an infinitely repeated presentation of a finite presieve.
- Clause (2), object descent: `∀ A, ∃ i Ai, Nonempty ((v i).obj Ai ≅ A)`.
  Correct: the isomorphism is inside the full category over X.
- Clause (3), map descent: `∀ i A B f, ∃ j h g` followed by the displayed
  delta conjugation formula. Correct domains and orientation of inverse delta
  at the source and delta at the target. Eventual equality separately quantifies
  stage maps `f g : A ⟶ B`, assumes equality under v, and obtains equality
  under U at some j ≥ i. No faithfulness at the initial stage is assumed.
- Clause (4), covering descent: `∀ n A B f`, the covering iff with witnesses
  `i Ai Bi fi t s` and the commuting equations for each a. Correct: a single
  common stage, all source and target isomorphisms, and all family arrows are
  retained. Fin n covers every finite indexed family by bijective reindexing.
- Clause (5), category/site colimit: `K : Cocone F`, the two `IsColimit`
  witnesses on `Cat.objects` and `Cat.arrows`, and `K.ι ⋙ W = v'` specify
  exactly Stacks' category colimit and its induced functor. The iff defining P
  gives covers as images of stage covers, with equality transport for targets.
  `W.IsEquivalence` and the final covering iff give equivalence of categories
  preserving and reflecting coverings. Verdict: all clauses present.

Dependency audit: opened the statement/Lean records of all statement dependencies
and the actual declarations in `LimitAffineTransition`, `FullAffineEtaleSite`,
`FullAffineEtaleTopos`, `FinitePrecoverage`, `SiteSystemStrictification`, and
`ColimitSites`. Also inspected Mathlib's `Scheme`, `Scheme.Hom`, `IsAffineHom`,
`IsPullback`, `pullback`, `Functor.IsContinuous`, and
`Functor.sheafPushforwardContinuous`. The universal-square form uses the same
fibre-product notion, not a second definition. The site-system theorem still
has the inherited unrestricted composition interface; it is not applied in
this statement-only module. Its name does not supply a substitute site notion.
The finite axioms here are the recorded, shared definitions in
`def-weil-pbc-finite-precoverage`, whose node was added to stmt_deps.
There are no new nodes or dependency modules in this delivery. The proof-plan
module `AffineEtaleColimitPresentation` explicitly documents the inherited
false unrestricted-composition conclusion; I read that warning and signature.
Adapting that proof interface is stage-3 work, not a reason to retain the false
conclusion here or introduce a private definition.

Edge cases: an empty directed index is excluded in the source sense and Lean;
a singleton or constant diagram is included. Empty schemes, the zero ring's
spectrum, and empty covering families are allowed (`n = 0` is not excluded).
For a nonempty target the same joint-surjectivity definition prevents an empty
cover. There is no characteristic restriction or cohomological degree binder.
All universes are explicitly bound: I and schemes have the same u, site objects
have universe u+1 and morphisms u; F uses precisely `Cat.{u, u + 1}`. No smaller
independent test-object universe or implicit variable occurs.

Independent searches (different wording from the first worker):

- `msearch.py ... leanfinder "Finite jointly surjective etale affine coverings
  descend along inverse limits of schemes with affine maps"`: eight hits on
  affine transition limits, open covers, and descent of affineness; no complete
  site-colimit declaration.
- `msearch.py ... loogle "CategoryTheory.IsFiltered,
  AlgebraicGeometry.Scheme.Etale"`: zero hits.
- `msearch.py ... grep "etale.*[Ss]ite.*[Cc]olimit|[Cc]olimit.*[Ss]ite|0EYL"`:
  only unrelated Mathlib colimit declarations.
- `rg` for `FullAffineEtale`, affine/étale/colimit combinations, and `0EYL` in
  upstream WeilConjectures, Mathlib AlgebraicGeometry, and project Lean: found
  the project site's existing definition, the inherited theorem and its
  base-change, descent, presentation and later continuity modules; no exact
  reusable theorem with the repaired finite covering conclusion. I opened
  the inherited presentation statement rather than treating a matching name
  as an exact result.

Mismatch repaired: the proof docstring said that affine domains over
quasi-separated bases have finite-presentation structure maps. Without the
étale qualification that sentence is false. Clarified that these maps are
étale, hence locally of finite presentation, and that qcqs permanence supplies
quasi-compactness and quasi-separatedness. The theorem signature and natural
statement needed no further change. The source and blueprint docstrings are
present; the four proof steps are preserved. The only delivered theorem has
`sorry` as its whole proof; no definition, private notation or proof is added.

Second-reader validation: the absolute sandbox file compiled cleanly through
`scompile.py` on the server in 2.1 seconds, nice 19, two threads, 60-second
per-file limit. The signature was also checked textually equal to lean.statement,
and every Lean line is at most 100 characters. An initial relative-path invocation
selected the inherited repository file and failed in its old proof; the successful
check above explicitly compiled the delivered sandbox statement.
