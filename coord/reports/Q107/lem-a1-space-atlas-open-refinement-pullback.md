## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAtlasOpenRefinementPullback` states
`AlgebraicGeometry.AlgebraicSpace.space_atlas_open_refinement_pullback`, with its
only proof `sorry`. It introduces no definitions and changes only the item's `lean`
record. There is no statement correction, dependency repair, or new node.

Source checked: `literature/stacks-project/spaces-properties.tex`, Tag 03FX,
`lemma-cover-by-union-affines`, lines 700–723. The prescribed atlas and the
open-cover coproduct construction are exactly those in its proof. The expanded
scheme-test and residue-field arguments are the five accepted DAG proof steps,
which are included in the theorem's docstring with their dependency ids.

Hypotheses and clauses, in order:

- The scheme S is `{S : Scheme.{u}}`, and the algebraic space over it is
  `(E : AlgebraicSpace S)`. All charts, atlases and tests are objects of `Over S`;
  this supplies their structural morphisms and compatibility over S.
- The prescribed scheme V is `(V : Over S)` and its atlas is
  `(p : yoneda.obj V ⟶ E.obj.obj)`. The three hypotheses are exactly
  `hp : IsRepresentable p`, `hpEt : IsEtale p`, and `hpSurj : IsSurjective p`.
  These are the recorded scheme-test definitions, rather than assumptions about
  rational lifts or an unrelated notion of surjectivity.
- The arbitrary set-indexed open covering is quantified as
  `(I : Type v) [Small.{u} I] (U : I → Over S) (j : ∀ i : I, U i ⟶ V)`.
  `∀ i, IsOpenImmersion (j i).left` says that these are open subschemes, with
  no affineness assumption. The next premise
  `∀ x : V.left, ∃ i y, (j i).left y = x` says their images cover V.
  An open subscheme presented by an open immersion is equivalent to a literal
  open subset with its restricted structure sheaf. Repeated and overlapping
  opens are allowed. Smallness is the stipulated universe bound on schemes and
  their set-indexed coproducts; v is otherwise independent of u.
- W is the actual coproduct `∐ U` in `Over S`; its disjoint open components are
  the standard `Sigma.ι U i`, using the scheme coproduct dependency. The map r is
  `Sigma.desc j`, and w is the explicit composite
  `yoneda.map (Sigma.desc j) ≫ p`. No existential arbitrary substitute for r or w
  occurs. Coproducts in `Over S` are created by its forgetful functor, so their
  underlying schemes are the required scheme coproducts.
- The first conclusion quantifies over every `(T : Over S)` and
  `(t : yoneda.obj T ⟶ E.obj.obj)`. Its witnesses `P`, `q : P ⟶ T`, `a : P ⟶ V`
  satisfy `IsPullback (yoneda.map a) (yoneda.map q) p t`. This is precisely a
  representing scheme with both projections for T ×_E V, rather than merely a
  scheme isomorphic to an unspecified object.
- Each P_i is the actual `Limits.pullback a (j i)` in `Over S`.
  `IsOpenImmersion (pullback.fst a (j i)).left` states the required open immersion
  P_i → P. The subsequent `∀ x : P.left, ∃ i y, ... = x` states that these opens
  cover P.
- The second displayed `IsPullback` has top-left object the Yoneda presheaf of
  `∐ fun i ↦ Limits.pullback a (j i)`. Its map to W is
  `yoneda.map (Sigma.desc (fun i ↦ pullback.snd a (j i) ≫ Sigma.ι U i))`;
  its map to T is
  `yoneda.map (Sigma.desc (fun i ↦ pullback.fst a (j i) ≫ q))`.
  Its other arrows are exactly w and t. This is the universal-property form of
  saying that the canonical comparison to h_T ×_E h_W is an isomorphism, with
  exactly the canonical restrictions on every component. It asserts both
  representability by the specified scheme coproduct and compatibility of its
  projections. All the presheaves here are fppf sheaves, and sheaf inclusion
  preserves and creates limits, so this is also exactly the sheaf fibre-product
  assertion. It does not assert that Yoneda preserves arbitrary coproducts.
- The next two clauses are `Surjective` and `Etale` of precisely that coproduct
  projection to T. Thus surjectivity means scheme-point surjectivity and not
  surjectivity of sections over a fixed field.
- The final four clauses of the universal-cover conclusion are
  `IsRepresentable w`, `IsSurjective w`, `IsEtale w`, and
  `Function.Surjective (schemePointMap w)`. The point map is the dependency's
  residue-field point-class map without a second definition of point classes.
- The last conjunct states existence for this same prescribed V and p of
  `(I : Type u) (U : I → Over S) (j : ∀ i, U i ⟶ V)`, with the same open-immersion
  and covering clauses, plus `∀ i, IsAffine (U i).left`. Mathlib's `IsAffine`
  means isomorphic to the spectrum of a commutative ring. For every i it supplies
  `(B : S.Opens) (_ : IsAffineOpen B) (b : (U i).left ⟶ B.toScheme)` with
  `b ≫ B.ι = (U i).hom`, which is exactly the factorization of the structural
  morphism through an affine open of S. Applying the first conjunct at v = u
  gives all the refined-atlas conclusions for such a family.

Recorded dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (the latter two underpin `IsAffine`).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentable`, `.IsEtale`, `.IsSurjective`. Its full
  definitions were read: each property is quantified over scheme-test pullbacks.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`:
  `AlgebraicSpace.Point`, `PointRepresentative.Rel`, `schemePointMap`.
  The map's full construction uses `fromSpecResidueField` and `Quot.mk`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Limits`: scheme discrete colimits, `sigmaOpenCover`,
  `disjoint_opensRange_sigmaι`; `Sigma.desc` and `Sigma.ι` are their universal
  maps. The coproduct dependency has a `mathlib_match`, needing no repair.
- The size-convention node is metatheoretic and has no declaration to import;
  it is implemented by the explicit universes and `Small.{u}` binder.

The already-stated proof dependencies are imported through their recorded Mathlib
modules: `Sites.Fpqc` (Zariski covers are fppf), `AffineScheme` (affine-open basis),
`Morphisms.Etale` (composition, cancellation, open immersions), `Morphisms.Basic`
(source locality), `OpenImmersion` and `Restrict` (open factorization),
`ResidueField` (field-point factorization), `Pullbacks` and `PullbackCarrier`
(open fibre products), `Gluing` (scheme-morphism gluing), and the existing public
point-class module. There is no import cycle with the downstream affine-atlas
or point-topology statements.

Edge cases checked before and after writing: an empty atlas with empty index
set (no `Nonempty I` is assumed), empty test schemes, repeated opens, overlapping
opens, an identity atlas, arbitrary infinite covers within the universe bound,
nonaffine tests and nonaffine prescribed opens. When the cover is empty, V is
empty and scheme-test surjectivity makes every relevant T empty. The displayed
coproducts and universal properties still apply. Point surjectivity uses residue
field extensions and does not require a K-rational lift. The affine existence
uses an index of size u, as the set of points of V has that size.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “A surjective etale algebraic space atlas refined
  by an open covering has scheme pullbacks equal to the coproduct of pulled back
  opens”. Eight results concerning scheme pullback open covers and scheme
  pullback gluing; none includes the algebraic-space test and point assertions.
- `msearch.py ... loogle`: `"sigmaOpenCover", "pullback"` — zero hits.
- `msearch.py ... grep`: `atlas.*[Rr]efin|[Rr]efin.*atlas|AlgebraicSpace`, restricted
  to Mathlib AlgebraicGeometry — zero hits.
- `msearch.py ... leansearch`: “An algebraic space atlas refined by a disjoint
  union of open charts has pullbacks the coproduct of the pulled back charts and
  is surjective on points”. Eight hits including scheme coproduct surjectivity
  and manifold atlases, not the node's statement.
- `rg -n 'atlas.*[Rr]efin|[Rr]efin.*atlas|lem-a1-space-atlas-open-refinement-pullback'`
  on both `lean/WeilConjectures` and `lean/Sheaf`: no upstream statement;
  downstream affine-atlas and quotient modules have related proofs.
  `grep -rn` of the exact node id in `lean/WeilConjectures` had no hit.
  In particular, `AlgebraicSpaceAffineEtaleCover.lean` gives existence of an
  atlas and topology, not pullbacks of a prescribed open refinement, and is
  downstream. `EtaleQuotientAffineOpenCover.lean` was read: its helper maps apply
  to open covers but its theorem is about quotients of étale equivalence
  relations, not this statement. Here the actual Mathlib coproduct expressions
  avoid creating another definition of those helper constructions.

Validation: the prescribed `scompile.py Q107 ...` compiled the sandbox and library
module successfully (1.8 s and 1.7 s). No errors or warnings were emitted.
No `#check`, local notation, local instance, implicit variable, or helper theorem
is left in the module. No statement fault or STATEMENT-DISPUTED issue found.

## Second reading by Q107

A separate in-thread rereading compared the node and the completed signature.
The dispatcher explicitly prohibits starting another agent, so this is not
represented as an independent review; the maintainer supplies that review.

The rereading checked the binders S, E, V and the prescribed p against the opening
hypotheses, and matched each open-immersion and point-cover premise. It checked
that neither given opens nor test schemes are required affine; that the two
coproduct arrows in the second `IsPullback` use the correct snd and fst
projections; that the first `IsPullback` has arrows a, q, p, t in the correct
orientation; and that the three representable properties and point surjectivity
all concern the same literal composite w. Finally it checked that the affine
existential retains this prescribed V, and that its base-factorization equality
uses the actual structural map of U_i, rather than an unrelated map to S.
The arbitrary-cover statement and affine existence are separate conjuncts,
so no affine hypothesis has slipped into the former. The empty-family case is
still included. No mismatch or change was needed after compilation.
