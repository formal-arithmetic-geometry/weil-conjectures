## Worker report

Existing declaration bundle; no Lean module is written. The primary declaration is
`AlgebraicGeometry.Scheme.AffineProEt.isEquivalence_sheafPushforwardContinuous_toProEt`
in `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`. Its source and the
other declarations below were read in both the group clone and slopmaster2.
The blueprint source read is
`literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lem-weil-pbc-ind-etale-basis.md`,
statement and both proof paragraphs. No statement correction, new node, dependency
module, or disputed statement is needed.

Hypothesis and clause correspondence (all short declaration names below are in
`AlgebraicGeometry.Scheme.AffineProEt`):

- Affine base X: specialize the existing declarations' `S : Scheme.{u}` to an affine
  scheme. They are available for all bases, but only this specialization is attached.
  The dependency's `Scheme.AffineProEt S` is the full category of affine ind-etale
  S-schemes when S is affine; its inclusion is `toProEt S`. No different basis is used.
- Every pro-etale object has a basis cover: `isCoverDense_toProEt` (lines 157–275)
  states `(toProEt S).IsCoverDense (ProEt.topology S)`. The covering sieve generated
  by arrows from basis objects is exactly the site-theoretic basis-cover assertion.
  Its proof covers by affine opens and applies the weakly-etale ind-etale refinement.
- Every cover of a basis object has a finite basis refinement:
  `exists_finite_jointly_surjective_of_mem_topology` (lines 739–786) takes any covering
  sieve `T` and supplies `ι : Type u`, `Finite ι`, `V : ι → S.AffineProEt`, and
  `f : ∀ i, V i ⟶ X`, with `∀ i, T (f i)` and joint surjectivity on `X.left`.
  For a full-site covering of `(toProEt S).obj X`, use its pullback sieve on the
  full subcategory: it is covering for the restricted topology by definition.
  The supplied arrows factor through the original cover since they belong to its
  generated sieve. This is refinement, not a finite subfamily of the original cover.
  Each arrow between basis objects is ind-etale and hence weakly etale (lines 112–127).
  Both ends are affine, so each arrow is affine. The finite jointly surjective family
  therefore is a pro-etale cover: over any affine open, inverse images are affine and
  their finitely many images cover it. Thus joint surjectivity here renders the full
  covering clause, not merely a topological surrogate.
- Fibre products remain in the basis: `instHasPullbacks` (lines 148–156) gives
  `HasPullbacks (AffineProEt S)`; `isPullback_left` (lines 527–533) states that such
  pullback squares become scheme pullback squares. These together say that actual
  scheme fibre products of basis objects over basis objects belong to the basis,
  rather than only asserting unrelated categorical limits exist. The forgetful
  functor creates these pullbacks (lines 281–291).
- Sheaves are determined by restriction: the primary instance (lines 438–445)
  asserts that the actual `sheafPushforwardContinuous` along `toProEt S` is an
  equivalence; `sheafPushforward` (lines 447–451) is this restriction functor.
  Hence a basis sheaf extends uniquely up to the unique isomorphism compatible with
  its specified restriction. This is the categorical uniqueness meant by the node.
- Morphisms are determined uniquely: the same equivalence is fully faithful, giving
  bijections on Hom sets under restriction.
- Restriction detects isomorphisms: a fully faithful functor reflects isomorphisms;
  lift the restricted inverse by fullness and the inverse identities by faithfulness.
  No stronger literal equality of sheaf objects is asserted.

The value-category binder of the primary declaration allows any category with
`HasLimitsOfSize.{u, u + 1}`. In particular it covers set-valued sheaves in `Type (u+1)`,
abelian groups, and modules over a fixed commutative ring in the larger universe.
These categories have the required limits. The site uses exactly the size convention
of the existing dependency; no additional geometric hypothesis is imposed.

Dependency declarations read and used:

- `def-weil-pbc-ind-etale-basis`: module
  `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`,
  `AlgebraicGeometry.Scheme.AffineProEt` (lines 88–91), its full category, `toProEt`,
  `precoverage` (278–280) and restricted `topology` (381–382).
- `def-weil-pbc-proetale-site`: module
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, full docstring and signature read.
  Its small-site component is Mathlib's `Scheme.ProEt` with `ProEt.topology`; the
  present node makes no assertion about the dependency's derived module category.
  The existing bundle already imports the pro-etale site itself, so a new dependency
  module or redundant import of the derived category is unnecessary.

Edge cases checked: empty affine base and empty basis object are allowed; finite
families may have empty index type (`Finite`, no `Nonempty`). A covering of a nonempty
object forces joint surjectivity, whereas the empty family covers the empty object.
The density declaration does not demand an object be affine; its base may be affine
while the covered object is arbitrary. Pullback legs are arbitrary basis morphisms,
not merely open immersions or surjections. There is no coefficient characteristic
restriction. The `Type u` finite index is large enough since every finite type can
be represented there, and the scheme/site universes agree with the dependencies.

Searches run:

- `msearch.py ... leanfinder` query: "affine ind etale objects cover the pro etale site
  finite refinement coverings and equivalence of sheaf restriction". Eight hits:
  Mathlib etale topologies and affine-refinement lemmas; no exact complete match.
- `msearch.py ... loogle` query:
  `CategoryTheory.Functor.sheafInducedTopologyEquivOfIsCoverDense`. One hit, the
  general comparison theorem; it alone does not state geometric basis properties.
- `msearch.py ... grep` query:
  `IsCoverDense|exists_finite_jointly_surjective|sheafPushforwardContinuous`,
  subdirectory `CategoryTheory/Sites`. Twenty-five hits, general site comparison and
  pushforward results, not the scheme-specific bundle.
- `msearch.py ... leansearch` query: "restriction to affine pro etale basis sheaves
  equivalence". Service unavailable: Internal Server Error; no negative-match claim.
- `rg` of slopmaster2 `WeilConjectures`, group `lean/Sheaf` and the exact framework
  source for `ind.etale.basis|isCoverDense_toProEt|exists_finite_jointly_surjective_of_mem_topology|isEquivalence_sheafPushforwardContinuous_toProEt`:
  found all three named statements in `Comparison/Affine.lean`, none in `lean/Sheaf`.
- `grep -rn` of slopmaster2 `WeilConjectures` for the item id: no hits.
- Read `dag/lean_names_upstream.json` and the compressed slopmaster2 sorry map for
  `AffineProEt` instance names. The latter confirms the exact generated name
  `AlgebraicGeometry.Scheme.AffineProEt.instHasPullbacks` and records the named
  declarations above as not using sorry (including transitively); stage 2 only
  requires the existing signatures and does not alter their proofs.

Validation: the dry-run delivery compiles server-side `#check` probes for every
recorded declaration through `scompile.py`, then performs the stage-2 preflight.

## Second reading by NM

I independently read the node, its blueprint source (order 1279, statement and
both proof paragraphs), both statement-dependency nodes, and their actual Lean
sources. I read the exact group-clone `Comparison/Affine.lean`,
`Morphisms/ProAffineEtale.lean`, and `coord/pefw-upstream-framework.md`; I also
checked the corresponding upstream declarations. The source of this item is the
blueprint, not a Stacks lemma. For the ambient site's conventions I additionally
read Stacks `proetale.tex`, Definition `definition-big-small-proetale` (098K),
and Mathlib `AlgebraicGeometry/Sites/Proetale.lean`. There is no hidden Noetherian,
separation, characteristic, or nonemptiness hypothesis.

Objects, hypotheses, and conclusion clauses, checked separately:

1. Base: an arbitrary affine scheme X. Lean's section binder is
   `S : Scheme.{u}`. The recorded bundle is applied to affine S; its availability
   for other S does not change this node's scope. Verdict: matches.
2. Basis: the full category of affine ind-etale S-schemes, with all S-morphisms
   and induced coverings. The dependency's `Scheme.AffineProEt S` is
   `proAffineEtale.Over ⊤ S`; `proAffineEtale.isAffine` gives absolute affineness,
   and `proAffineEtale_iff_appTop` identifies its property with ind-etaleness
   over affine S. `toProEt S` retains all morphisms and is full and faithful.
   `topology S` is its restricted `ProEt.topology S`. The other dependency's
   `proEtaleDerivedCategory` uses this same Mathlib `ProEt` site; no derived
   category or coefficient hypothesis enters this statement. Verdict: matches.
3. Every pro-etale object has a basis cover. `isCoverDense_toProEt` says
   `(toProEt S).IsCoverDense (ProEt.topology S)`. I checked Mathlib's definition:
   the sieve consists of arrows factoring through basis objects and is covering.
   This is the sieve generated by the arrows from basis objects, hence the
   covering assertion, for every object, including nonaffine ones. Verdict: matches.
4. Every covering of a basis object has a finite basis covering refinement.
   `exists_finite_jointly_surjective_of_mem_topology` takes an arbitrary covering
   sieve T on X and returns `ι : Type u`, `Finite ι`, `V : ι → S.AffineProEt`,
   `f : ∀ i, V i ⟶ X`, membership `∀ i, T (f i)`, and joint surjectivity on X.
   For an original family, membership in its generated sieve means factorization
   through a family member, exactly refinement. For a full-site cover use its
   inverse-image sieve under the full inclusion; the restricted topology makes
   this covering. Each returned map is weakly etale by the existing instance
   following `proAffineEtale_hom`; both schemes are affine, so it is affine.
   Inverse images of each affine open are affine and their finitely many images
   have union exactly that open. Thus this is an fpqc/pro-etale covering, including
   the quasi-compact-open clause, not just joint surjectivity. Verdict: matches.
5. Fibre products of arbitrary basis arrows remain basis objects.
   `instHasPullbacks` supplies pullbacks in `AffineProEt S`;
   `isPullback_left` sends their squares to scheme pullback squares. I read the
   `CreatesLimitsOfShape WalkingCospan` instance as well. This renders the actual
   scheme fibre product, with arbitrary legs over any basis object. Verdict: matches.
6. Restriction determines sheaves. The primary declaration
   `isEquivalence_sheafPushforwardContinuous_toProEt` states `IsEquivalence` for
   the actual restriction functor; `sheafPushforward` is that functor. Essential
   surjectivity and full faithfulness give extension and uniqueness up to the
   unique isomorphism compatible with a specified restriction. No literal equality
   of objects is intended in the source. Verdict: matches.
7. Restriction determines morphisms uniquely. Full faithfulness of this same
   functor gives precisely bijections on Hom sets. Verdict: matches.
8. Restriction detects isomorphisms. Fullness lifts a restricted inverse, and
   faithfulness lifts both inverse identities. Verdict: matches.
9. Coefficients and size: the primary binder `{A : Type*} [Category* A]` with
   `[HasLimitsOfSize.{u, u + 1} A]` supplies the comparison limits. In particular
   set-valued sheaves in `Type (u+1)`, abelian groups and modules in that universe
   are covered, as in the node's proof. All schemes are `Scheme.{u}` and the
   category of objects has size u+1. No independent small test universe or finite
   presentation restriction is added. Verdict: matches dependency conventions.

Edge cases: empty affine bases and empty schemes are allowed. The finite index
has no `Nonempty` instance: the empty family can cover an empty object. On a
nonempty object the surjectivity conclusion forces an inhabited family. Pullback
legs need not be surjective. Zero coefficients and every characteristic are
allowed. There is no degree n or exceptional n=0 case. Every finite index type
has a representative in `Type u`, so the index size excludes no finite cover.
All universes and variables of the recorded signature are bound by the source
section or declaration; its signature is verbatim the source declaration.

Independent searches, using words other than the worker's queries:

- LeanFinder: `dense affine subcategory weakly etale scheme site restriction
  equivalence finite covering sieve`: eight hits, principally affine Zariski and
  etale density; no complete geometric replacement.
- Loogle: `CategoryTheory.Functor.IsCoverDense`: twelve hits, including the
  definition and general restriction results. I opened DenseSubsite/Basic.lean
  to check the meaning of density rather than relying on the name.
- Mathlib grep through msearch: `cover.*dense|finite.*refin|restrictedTopology`
  in AlgebraicGeometry/Sites: twenty hits, including affine etale density and
  ProEt restricted topology, not this complete bundle.
- LeanSearch: `cover dense full subsite restriction sheaves equivalence`:
  unavailable (Internal Server Error); recorded as unavailable, not a no-match.
- Direct rg of upstream WeilConjectures and project lean/Sheaf for affine density,
  finite refinements, jointly surjective families, and ProEt density locates this
  exact existing AffineProEt bundle. The related etale/Zariski and fppf declarations
  use different sites. Direct rg also locates and verifies both affine ind-etale
  equivalence declarations in Morphisms/ProAffineEtale.lean.

No mathematical mismatch was found; no statement, signature, dependency record,
or module was changed. There are no new definition nodes or dependency modules
in this delivery. H5/H6 introduce no obligations because no definitions or proofs
are written. H8/H9 for a new statement module do not apply to this existing-source
attachment; the source and full node proof remain in the node and worker report.
The only change of this second reading is this independently checked review.
Validation uses deliver2.py's server-side scompile.py probes of all six recorded
existing declarations and its stage-2 preflight; no local compiler or global build.
