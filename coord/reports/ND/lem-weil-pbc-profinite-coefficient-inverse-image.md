## Worker report

The module `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage` states
`AlgebraicGeometry.Scheme.proEtale_profinite_coefficient_inverse_image`, with `sorry`.
It also states the naturality helper `proEtaleConstantInverseImageMap_naturality`,
with `sorry`, to package the already defined constant-section adjunct as a natural
transformation. This is the naturality assertion of the same DAG node; its proof
is sheafification and adjunction naturality. All five construction helpers have
real data, and all seven declarations are recorded in `lean.declarations`.
No statement was corrected, no dependency record was replaced, and no independent
new notion or new node was needed.

Hypothesis and clause correspondence:

- An arbitrary scheme morphism is `(X Y : Scheme.{u}) (f : X ⟶ Y)` in each clause.
  There is no weakly etale, proper, affine, nonempty or Noetherian hypothesis on f.
- The small site is exactly `Scheme.ProEt.topology X`, with site object universe
  u+1 and Hom universe u; it is never replaced by a same-universe site.
- The countable inverse system is `Q : ℕᵒᵖ ⥤ CommRingCat.{u+1}`, with
  `[∀ n : ℕᵒᵖ, Finite (Q.obj n)]`. All morphisms are unital ring maps by definition
  of CommRingCat. `op n` denotes the paper's n+1, so no level is omitted or added.
  A sequence of adjacent transitions determines this functor by finite composites.
  Ring coefficients are in u+1, the value universe of the recorded constant-sheaf
  and inverse-image APIs. This includes the canonical ULift of every ring in u;
  finiteness is invariant under that lift. No equality of site universes is imposed.
- `(Q_n)_T` is `(proEtaleCoefficientTower T Q).obj n`, i.e. precisely
  `(constantSheaf (ProEt.topology T) CommRingCat).obj (Q.obj n)`.
  R_T and its projections are `limit (proEtaleCoefficientTower T Q)` and `limit.π`.
  This uses constant sheafification directly. The equivalent continuous-functions
  description does not replace it by a second coefficient sheaf.
- `c_{f,n}` is `(proEtaleConstantComparison f).app (Q.obj n)`. Its definition is
  exactly the recorded `proEtaleConstantInverseImageMap`, whose source was read:
  it applies inverse image to `proEtaleConstantDirectImageMap` and then the counit.
  That direct map is the unique sheafification extension of the constant-section
  map. Thus the normalization by the same constant q is fixed in the data.
- `c_f` is `proEtaleProfiniteComparison f Q`. Its data is `limit.post` followed by
  `limMap` of the finite comparisons, not a selected arbitrary isomorphism.
- The first two conjuncts state `IsIso` for these exact maps, at all finite
  levels and at the infinite limit. In a category `asIso` recovers the specified
  isomorphism from `IsIso`; this asserts invertibility of the canonical map.
- The third conjunct is exactly projection compatibility; the fourth says every
  map with those composites is this map, supplying the stated uniqueness.
- The fifth conjunct is transition compatibility for every arrow n → m; adjacent
  arrows give the displayed t_n identity. Compatibility with composites is included
  in saying the sequence is an inverse system, and also follows from adjacent
  compatibility, so this formulation does not strengthen the mathematical claim.
- The sixth conjunct is infinite-level naturality for every natural transformation
  `a : Q ⟶ P` of finite-ring towers; induced limit maps are the canonical `limMap`.
  The seventh is the finite-level naturality square for every `a.app n`.
- The eighth and ninth conjuncts are the finite and limit identity equations.
  `proEtaleRingInverseImageId` is the canonical mate of identity base change.
- The last two conjuncts are the finite and limit composition equations for
  X → Y → Z. `proEtaleRingInverseImageComp` is the mate of canonical fibre-product
  pasting, with the direction `(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹`. Thus the clause uses the
  canonical composite identification, not an assumed or arbitrary comparison.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (source lines 42 and 74), giving the actual schemes and all morphisms.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `Scheme.proEtaleDerivedCategory`; its full definition specifies the small
  pro-etale site and the constant CommRingCat coefficient convention. It is
  available transitively through the inverse-image module; no derived object is
  needed in this theorem.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: full source read, including
  `proEtaleBaseChange`, `proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`,
  `proEtaleSheafAdjunction`, `proEtaleConstantDirectImageMap` and
  `proEtaleConstantInverseImageMap`. Their existing constructions fix the maps.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  source lines 61–66, sheafification of the constant presheaf.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf` and
  `sheafificationAdjunction`, source lines 72–81. Used through `constantSheaf`
  and the recorded inverse-image comparison, not reimplemented.
- Mathlib `limit`, `limit.π`, `limit.post` and `limMap` express the exact inverse
  limit and canonical comparison. Mathlib `Sites.Limits` supplies ring-sheaf limits.
- For the proof plan, the recorded modules of limit-affine-transition,
  ind-etale-algebra, ind-etale-stability and sheaf-algebraic-structures-objects are
  ordinary imports, not public imports. Other proof prerequisites have no Lean
  record yet and are named in the theorem docstring. This is not a statement wait.

Source verification: read the actual text at proetale.tex labels
lemma-morphism-big-small (Tag 098T), part (2), and lemma-ind-etale-implies
(Tag 097N), sites.tex lemma-pullback-representable-sheaf (Tag 04D3), and
limits.tex lemma-directed-inverse-system-affine-schemes-has-limit (Tag 01YW)
and the subsequent affine-transition limit lemma. These give the site's inverse
image, the ind-etale weak-etale property, representable pullback and the limits.
The supplied DAG proof assembles them: represent finite constants by labelled
disjoint unions, take the affine-transition representing limit, and apply
representable pullback. Its eight steps are retained in the main docstring.

Edge cases checked: the zero ring is allowed, all transitions may be
non-surjective, schemes may be empty or disconnected, and f may be an identity
or any composite. The bottom natural-number index denotes level 1, not an
unrequested level 0. No nonempty-scheme or surjective-transition assumption is
introduced. Inverse image is not assumed to preserve arbitrary infinite limits;
only the particular comparison is asserted invertible. Ring operations and
unitality are retained because every sheaf and comparison is CommRingCat-valued.

Searches actually run (ND/item search log):

- LeanFinder: `Inverse image of pro-etale sheaves preserves inverse limits of
  finite constant commutative ring sheaves` returned eight condensed-category
  comparison constructors (including Condensed.ofSheafForgetProfinite and
  LightCondensed.ofSheafForgetLightProfinite); no matching scheme theorem.
- Loogle: `CategoryTheory.constantSheaf, CategoryTheory.Limits.limit` returned
  zero hits.
- msearch grep: `uliftFunctor|mapComparison|limitComparison` in
  `Algebra/Category/Ring` returned zero hits.
- LeanSearch: `Inverse image of inverse limits of finite constant ring sheaves
  on pro-etale sites` was UNAVAILABLE (Internal Server Error). This is not
  recorded as a negative search result.
- Local rg of project `lean/Sheaf/AlgebraicGeometry` and `lean/Sheaf/Paper` for
  profinite/coefficient-tower terms located the relative profinite-test-object
  and point-component framework, not this finite-ring-tower comparison.
- Local rg of DAG nodes for `inverse system of finite|tower of finite|profinite
  coefficient` located this item and its four-corners consumer; none defines
  another canonical comparison that this delivery should use.
- Local rg of upstream ProEtale for profinite found Adic/UpperStar.lean. Its
  header and signatures concern the particular Qbar_l coefficient object;
  it does not state the arbitrary finite commutative ring tower assertion.
- Upstream grep for this exact node id, and rg of both upstream WeilConjectures
  and project lean/Sheaf for the new declaration names, returned no matches.
- Mathlib sources were searched for limit comparisons and site pushforward
  identity/composition APIs. `limit.post`, `limMap`,
  `sheafPushforwardContinuousId'`, and `sheafPushforwardContinuousComp'` supply
  the canonical construction; there is no private copy of these operations.

Validation refreshed 2026-10-15: the prescribed `scompile.py ND
lem-weil-pbc-profinite-coefficient-inverse-image <module>` completed successfully
using the authorized local side-project overlay. Both sandbox and module-path
checks passed (7.9 s and 8.0 s), with no errors or warnings. No global build was run.

Current worker rechecked all five statement-dependency records and declaration
sources, the eight node proof steps, the named Stacks source passages, and the
small-site framework note. The existing module and canonical construction data
needed no changes. Refreshed searches: LeanFinder (inverse image preserving limits
of finite constant commutative ring sheaves) returned eight condensed-category
constructors, none matching this theorem; Loogle `CategoryTheory.Limits.limit.post`
returned eleven generic limit-comparison facts; msearch grep
`profinite.*[Cc]onstant|[Cc]onstant.*profinite` in `CategoryTheory/Sites` returned
zero hits. LeanSearch for inverse image of finite constant ring-sheaf limits
remains unavailable (Internal Server Error), not evidence of absence. Direct rg
across upstream WeilConjectures and project lean/Sheaf found no declaration of
this item or its helpers. The earlier independent reading below is retained;
its old compilation restriction is superseded by the human update of 2026-10-15.
The next independent reader remains responsible for final delivery.

## Earlier second reading (a previous round; superseded)

I independently read the node's statement and eight proof steps, its five statement
prerequisite records and their declaration sources, and the delivered module.
I read Stacks proetale.tex, lemma-morphism-big-small (098T), including the
base-change/direct-image formula in (2), and lemma-ind-etale-implies (097N);
sites.tex, lemma-pullback-representable-sheaf (04D3); and limits.tex,
lemma-directed-inverse-system-affine-schemes-has-limit (01YW) and the immediately
following affine-transition result (01YX). These statements impose no properness,
Noetherian, connectedness or surjectivity assumption here. The result of this
node is their coefficient-system consequence, not a verbatim theorem of 098T.

Object, hypothesis and conclusion checklist (in node order):

1. Arbitrary schemes U,V and morphism u: rendered by `X Y : Scheme.{u}` and
   `f : X ⟶ Y` in every relevant conjunct. Verdict: exact; no extra condition on f.
2. Small pro-etale sites and inverse image: `ProEt.topology X/Y` and
   `proEtaleSheafInverseImage f CommRingCat.{u + 1}`. The actual recorded
   ProEtaleInverseImage source uses `MorphismProperty.Over.pullback @WeaklyEtale ⊤ f`,
   followed by left Kan extension and sheafification; direct image is sectionwise
   precomposition. The ProEtaleDerivedCategory dependency uses these same sites.
   Verdict: exact, with site objects in u+1 and morphisms in u retained.
3. Countable tower of finite commutative rings with unital transitions:
   `Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}` and `[∀ n, Finite (Q.obj n)]`.
   `op n` labels mathematical n+1. Functor maps encode transitions and their finite
   composites; CommRingCat morphisms preserve one. Verdict: exact.
4. Constant ring sheaves: `proEtaleCoefficientTower T Q = Q ⋙ constantSheaf ...`.
   I opened Mathlib constantSheaf: it is precisely constant presheaf followed by
   presheafToSheaf, whose sheafification adjunction I also read. Verdict: exact;
   the node's continuous-functions description is an equivalent description of
   this sheaf, not another input or hypothesis requiring a different object.
5. R_T and its projections: `limit (proEtaleCoefficientTower T Q)` and `limit.π`.
   Verdict: exact ring-sheaf limits, with no arbitrary replacement object.
6. Normalized finite comparison: `proEtaleConstantComparison f` has components
   `proEtaleConstantInverseImageMap f ... A`. I read that dependency's definition:
   it is inverse image of the unique sheafification extension of the constant
   section map, followed by the actual adjunction counit. Verdict: exactly the
   specified adjunct sending q to the same constant q, not a chosen isomorphism.
7. Finite and infinite isomorphisms: conjuncts 1 and 2 assert `IsIso` of those
   precise finite maps and `proEtaleProfiniteComparison f Q`. The latter is
   `limit.post` followed by `limMap` of the finite comparisons. I read both Mathlib
   definitions and their projection equations. Verdict: canonical isomorphisms;
   no infinite-limit-preservation hypothesis has been assumed.
8. Projection equation and uniqueness: conjuncts 3 and 4 use exactly
   `c_f ≫ π_X,n = f⁻¹(π_Y,n) ≫ c_f,n` and equality of every competing map satisfying
   those equations with this c_f. Verdict: exact.
9. Adjacent transition equation: conjunct 5 gives the same square for every arrow
   n → m of ℕᵒᵖ. For (n+1) → n this is the displayed t_n equation; the remaining
   squares follow by finite composition. Verdict: equivalent tower compatibility.
10. Naturality in tower morphisms: conjuncts 6 and 7 quantify over each finite
    ring tower P and natural transformation a : Q ⟶ P, using limMap of a for the
    infinite square and a.app n for finite squares. Verdict: both levels retained.
11. Identity compatibility: conjuncts 8 and 9 compare to
    `proEtaleRingInverseImageId X`. This is the adjunction mate of Mathlib's actual
    base-change-by-identity pushforward isomorphism. Verdict: canonical identity
    identification, at both levels.
12. Composition compatibility: conjuncts 10 and 11 use the adjunction mate of
    `MorphismProperty.Over.pullbackComp` via sheafPushforwardContinuousComp'.
    Direction is `(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹`, followed by f⁻¹(c_g) and c_f.
    Verdict: the node's exact canonical composition equations at both levels.

Edge cases: the index is the fixed countable nonempty tower, so an empty index
set is not part of this node. Lean n=0 denotes mathematical level 1 and includes
that first stage. The zero ring (one-element underlying type) is permitted;
there is no Nontrivial requirement. Empty schemes, disconnected schemes,
non-surjective transition maps, all characteristics, identity morphisms and
arbitrary composites remain included. Finite coefficients in the sheaf-value
universe u+1 do not omit smaller-universe finite rings: their canonical ULift
has the same ring structure and finite cardinality. Conversely any such finite
coefficient can be represented in the smaller scheme universe by a finite type;
thus the proof's finite representing scheme has no extra size assumption.
There is no independent smaller universe for test schemes or a site-universe
identification hidden in the signature.

Independent searches: LeanFinder query "Pullback of a tower limit of finite
constant sheaves along scheme base change on the proetale site" returned eight
hits about affine limits, finite maps and scheme module pullback, not this
statement. Loogle `CategoryTheory.Limits.limit.post` returned eleven generic
limit-comparison facts, including the exact constructor used here, not the
pro-etale coefficient theorem. LeanSearch query "Proetale inverse image commutes
with inverse limits of finite constant commutative ring sheaves" was unavailable
(Internal Server Error); this supplies no negative search evidence. I also ran
rg independently over upstream WeilConjectures, project lean/Sheaf, the exact
side-framework pro-etale sources, and Mathlib Sites, for constant/comparison,
profinite/inverse and CoefficientTower variants. The adic UpperStar module treats
the particular adic constant sheaf, not arbitrary finite-ring towers. The
side-framework ModuleObject.Basic profiniteToProEtOf defines profinite test
objects, not this comparison. The finite-coefficient upperStarId/upperStarComp
signatures require Abelian and IsGrothendieckAbelian on the coefficient category;
CommRingCat does not satisfy them. Consequently these ring-valued mates do not
duplicate a usable upstream declaration. No new definition node or dependency
module is present or needed in this delivery.

Construction/docstring check: all five construction helpers contain real data;
the naturality helper is a named theorem for the naturality clause of this node,
with its proof plan, source and blueprint reference. Only this helper and the
main statement have sorry proofs. The main docstring retains all eight steps,
including representability, ring operations, normalized adjunct, projections and
coherence. Every declaration has a source/blueprint docstring. No local notation,
private construction or unbound variable was found. All seven declarations are
recorded. No mathematical mismatch was found, and no Lean or node text was
changed; this independent report is the only intended review addition.

Historical validation note from the earlier reader: that attempt stopped because
it interpreted the local-first scompile.py wrapper as contrary to the then supplied
server-only instruction. The human parallel-landing update of 2026-10-15 explicitly
authorizes this wrapper and its private local overlay. The current worker reran
that exact wrapper successfully, as recorded above; this old tool concern is resolved.

## Second reading by ND

Independent final reading, 2026-10-15. I read the sandbox node and module,
all five statement-dependency nodes and their declaration sources, the framework
note, and the actual Stacks passages. Checklist in the order of the node:

1. Schemes U,V and arbitrary u: `X Y : Scheme.{u}`, `f : X ⟶ Y` in the
   conjuncts. Exact: Mathlib Scheme and Hom, with no property of f assumed.
2. Small pro-etale sites and inverse image: `ProEt.topology X/Y` and
   `proEtaleSheafInverseImage f CommRingCat.{u + 1}`. Exact: I read
   ProEtaleDerivedCategory and ProEtaleInverseImage, including the base-change
   functor, sectionwise direct image, Kan-extension inverse image, and adjunction.
   The object universe u+1 and Hom universe u are retained.
3. Countable finite unital commutative-ring tower: `Q : ℕᵒᵖ ⥤ CommRingCat.{u+1}`
   with `[∀ n, Finite (Q.obj n)]`. Exact: adjacent maps and their composites are
   encoded by the functor; op 0 denotes the first mathematical level.
4. Constant sheaves: `proEtaleCoefficientTower T Q` is Q followed by Mathlib
   `constantSheaf`. Exact: I read constantSheaf and presheafToSheaf; these are
   sheafified constant presheaves, with the node's equivalent clopen-partition
   description. No alternative coefficient sheaf is introduced.
5. R_T and projections: `limit (proEtaleCoefficientTower T Q)` and `limit.π`.
   Exact: limits in commutative-ring sheaves, not underlying sets alone.
6. Normalized c_(u,n): `(proEtaleConstantComparison f).app (Q.obj n)` is precisely
   `proEtaleConstantInverseImageMap`. Exact: its dependency definition applies
   inverse image to the unique sheafification extension of the same constant
   section and then the actual adjunction counit.
7. Infinite c_u: `proEtaleProfiniteComparison f Q` is `limit.post` followed by
   `limMap` of the finite comparisons. Exact: I read both Mathlib constructors
   and their projection identities. Its data fixes the map before invertibility.
8. Both comparisons are isomorphisms: conjuncts 1 and 2 are `IsIso` for those
   exact arrows. Exact: neither arbitrary isomorphisms nor limit preservation
   assumptions replace the canonical comparison.
9. Projection compatibility and uniqueness: conjuncts 3 and 4 give the displayed
   equation and equality of every competing map with those projections. Exact.
10. Transition compatibility: conjunct 5 treats every n → m in ℕᵒᵖ. Exact:
    the adjacent case is the node's t_n square, and other cases follow by finite
    composition, so no independent stronger assertion is imposed.
11. Tower naturality: conjuncts 6 and 7 quantify over finite towers P and maps
    `a : Q ⟶ P`; their arrows are `limMap (whiskerRight a ...)` and constantSheaf
    applied to `a.app n`. Exact at infinite and finite levels.
12. Identity compatibility: conjuncts 8 and 9 use `proEtaleRingInverseImageId`.
    Exact: its data is the adjunction mate of canonical base-change-by-identity,
    using Mathlib sheafPushforwardContinuousId', not a chosen identification.
13. Composition compatibility: conjuncts 10 and 11 use
    `proEtaleRingInverseImageComp f g`, followed by f-inverse-image of c_g and c_f.
    Exact: I checked the pullbackComp pasting and pushforward-composition mate,
    with direction `(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` as required.

Source context: proetale.tex lemma-morphism-big-small (098T), part (2), permits
an arbitrary scheme morphism and gives the direct-image evaluation formula.
lemma-ind-etale-implies (097N) assumes only ind-etaleness. sites.tex
lemma-pullback-representable-sheaf (04D3) assumes continuity; limits.tex
lemma-directed-inverse-system-affine-schemes-has-limit (01YW) and the following
lemma-directed-inverse-system-has-limit (01YX) give the affine and affine-transition
limits. Their hypotheses are precisely those established in the node's eight-step
argument; there is no hidden Noetherian, properness or transition-surjectivity
assumption. This is an assembled consequence, not a verbatim assertion of 098T.

Edge cases: the index is specifically a countable tower, so an empty index set
is outside the node. Lean n=0 includes the paper's first level. The zero ring,
empty and disconnected schemes, arbitrary characteristics, non-surjective maps,
identity maps and composites are all included. Finite rings in universe u are
included by canonical ULift into the coefficient universe u+1; finite rings in
that universe admit small finite models. No equality of site universes is added.

Independent searches: LeanFinder query "Base change on small proetale sites
commutes with countable inverse limits of finite constant ring sheaves" returned
eight condensed-category constructors, none a scheme-base-change theorem.
Loogle query `CategoryTheory.constantSheaf, IsIso` reported unknown identifier
IsIso, so that query is not evidence of absence. LeanSearch query "Pullback of
inverse limits of finite constant rings on small proetale sites" was unavailable
(Internal Server Error), also not evidence of absence. Direct rg searches used
`profinite.*constant|constant.*profinite|coefficienttower|profinitecomparison`
across Mathlib Sites, upstream WeilConjectures and project lean/Sheaf, and
`inverse system of finite|profinite coefficient|proEtaleRingInverseImage|proEtaleConstantComparison`
in the DAG and declaration-name index. No exact duplicate was found. I opened
upstream Adic/UpperStar: its coefficient is the particular ℓ-adic sheaf, not an
arbitrary finite-ring tower. I also opened the exact side-framework finite
coefficient upperStarId/upperStarComp signatures: they require Abelian and
IsGrothendieckAbelian value categories, so they do not supply these CommRingCat
mates. Mathlib limit.post and limMap are reused directly.

No new nodes, dependency modules or statement_change are in this delivery.
All five construction helpers have real data; the naturality proof is a named
sorry theorem with its source and proof plan. Both theorem proofs remain sorry.
All seven declarations are listed; their docstrings carry the source and blueprint,
and the main docstring retains all eight proof steps. Variables and universes
are explicitly bound. The recorded proof dependencies with project modules are
imported; the unstated proof prerequisites remain named in the proof plan.

Mismatch repaired: lean.statement had flattened whitespace rather than the
verbatim file signature. I replaced only that field with the exact multiline
signature, from `theorem` to before `:=`. No mathematical statement or Lean
construction required a change. The worker report and historical reading remain.

Validation: prescribed scompile.py completed with exit 0, sandbox check 7.6 s
and module-path check 7.7 s, with no errors or warnings. No global build was run.

Additional successful Loogle search: `CategoryTheory.Limits.limit.post` returned
11 generic comparison and preservation facts. I read the constructor and
projection equation in HasLimits.lean; none is the pro-etale coefficient theorem.
The verbatim signature equality was checked programmatically and is true.
Delivery dry run passed preflight and compilation (OK; nothing pushed).
