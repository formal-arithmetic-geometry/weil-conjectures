## Worker report

The module `Sheaf.AlgebraicGeometry.UnmarkedFiniteOpenPartsSpace` states
`AlgebraicGeometry.exists_unmarked_finite_open_parts_space`, with `sorry` as its
entire proof. It introduces no extra definitions, assumptions, or nodes. The base
node's accepted statement, split, dependencies and proof plan are unchanged;
only its `lean` field is added.

Source read: `literature/stacks-project/spaces-more-groupoids.tex`, section
“The finite part of a morphism”, equation-finite-conditions (04PC), equation-finite
(04PD), lemma-finite-sheaf (04PE), and proposition-finite-algebraic-space (04QH).
The current online [Tag 04QH](https://stacks.math.columbia.edu/tag/04QH) agrees.
Also read the current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/` direct-images statement and proof.
The present node is a supporting input, not that blueprint unit's own statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A base scheme S in the chosen size: `{S : Scheme.{u}}`, with explicit `universe u`.
  `Over S` has objects in `Type (u+1)` and morphisms in `Type u`. Both the pair
  sets and the sheaf values are in `Type u`, as in the recorded algebraic-space
  interface. No equality between unrelated universes is imposed.
- X and Y are S-schemes: `(X Y : Over S)`; f is an S-morphism: `(f : X ⟶ Y)`.
  The slice-category morphism includes the required compatibility over S.
- Separatedness and local finite type, exactly of f: `[IsSeparated f.left]` and
  `[LocallyOfFiniteType f.left]`. There is no properness, flatness, finite
  presentation, global quasi-compactness, or section hypothesis.
- The set P(T) is written literally as
  `Σ a : T ⟶ Y, {Z : (pullback f.left a.left).Opens //
  IsFinite (Z.ι ≫ pullback.snd f.left a.left)}`.
  The sigma component is the S-map a. The subtype component is an actual open
  subset of the scheme fibre product, and `Z.ι` is its canonical open-subscheme
  immersion. The subtype proof is exactly finiteness of its projection to T.
  This uses opens, hence identifies embedded open subschemes rather than adding
  choices of isomorphic source schemes to the pair data.
- E is an algebraic space over S: the existential `(E : AlgebraicSpace S)` uses
  the recorded definition, including its fppf sheaf condition, representable
  absolute diagonal, and representable surjective étale scheme atlas.
- The natural bijections from sheaf values, rather than morphisms or stalks:
  `(e : ∀ T : Over S, E.obj.obj.obj (op T) ≃ ...)`.
- Forgetting the open part is the natural transformation
  `(p : E.obj.obj ⟶ yoneda.obj Y)` and the first conjunct
  `(e T x).1 = p.app (op T) x`.
- Restriction is pullback: for every `h : T' ⟶ T` and section x, the second
  conjunct supplies b between the two scheme fibre products. Its first
  projection is unchanged, and its second projection is followed by `h.left`.
  These two equations determine b uniquely by the fibre-product universal
  property; it is the canonical base-change map, not an arbitrary map.
  The equation `(e T' (E.obj.obj.map h.op x)).2.val = b ⁻¹ᵁ (e T x).2.val`
  states precisely that the open subscheme is pulled back. Naturality of p and
  the first conjunct also give `a' = h ≫ a`. Since e is bijective, these clauses
  determine the full restriction on every pair. Transporting the existing
  sheaf functor through e gives the exact functor P; identity and composition
  follow from its functor laws. Thus there is no need for a duplicate named
  construction, a choice of an arbitrary functor, or extra functor-law sorries.
- Chartwise étaleness is the final conjunct: for every scheme V over S and every
  `c : yoneda.obj V ⟶ E.obj.obj`, `AlgebraicSpace.IsEtale c` implies
  `Etale (yoneda.preimage (c ≫ p)).left`. Yoneda's preimage recovers the actual
  S-morphism V to Y, so this is exactly the required scheme étaleness. There is
  no requirement that p itself satisfy representable `AlgebraicSpace.IsEtale`.
- Small charts: `E.property.2` supplies an atlas with `U : Over S`, so its source
  scheme is `Scheme.{u}`. Every chart quantified in the last conjunct has the
  same chosen scheme universe. The predicate `IsRepresentableWith` also uses
  only representing schemes in `Over S`.
- The node's exclusions are respected: no separatedness of p, scheme
  representability of E, flatness or finite presentation of f, or section is
  concluded or assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (def-pc-scheme). Their signatures and docstrings describe the actual locally
  ringed-space schemes and morphisms, not a replacement category.
- def-weil-size-convention is its recorded metatheoretic convention; explicit
  universe u and the recorded `AlgebraicSpace S` implement it.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` records the proper/separated node;
  the precise needed declaration is `AlgebraicGeometry.IsSeparated` in its
  defining module `Mathlib.AlgebraicGeometry.Morphisms.Separated`. It asks that
  the diagonal be a closed immersion; no `IsProper` assumption is used.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (def-weil-finite-type-morphism).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, for the actual
  scheme fibre products (def-pc-fibre-product).
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`, via the canonical `Scheme.Opens.ι` of
  actual open subschemes (def-weil-open-immersion).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`:
  `AlgebraicGeometry.IsFinite` (def-weil-finite-integral-morphism); its signature
  and affine finiteness docstring are exactly the projection property here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicSpace.IsEtale` (def-trf-algebraic-space). Read their full
  definitions, including `IsRepresentableWith` and `IsAlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (def-weil-etale-morphism), with its affine-local ring-map condition.

Recorded proof dependencies that have modules are imported privately, including
`SpaceEtaleSourceAtlasDetection.etale_source_atlas_detection` (full name
`AlgebraicGeometry.AlgebraicSpace.etale_source_atlas_detection`) and
`AlgebraicSpace.schemeSpace` from `EnlargedEtaleRingedSite`. The Mathlib proof
inputs use Limits, Morphisms.Basic and ResidueField, alongside the public
morphism-property imports. The three new proof inputs
lem-sfb-finite-open-parts-fppf-sheaf,
lem-sfb-finite-open-equality-locus, and
lem-sfb-finite-open-geometric-chart-family have no recorded Lean module in the
read base, so there is no such import to add. They are proof dependencies only,
not missing notions needed for this signature. The docstring contains all six
steps of the accepted proof and names their inputs.

Edge cases checked before and after writing:

- Empty open part is included for every a; there is no nonemptiness binder.
- Empty X leaves only the empty open part, so P is the represented functor hY.
- Empty test scheme is allowed and has the empty fibre product and unique pair.
- Empty Y or base S is not excluded; slice objects and scheme fibre products
  handle them without any point-selection assumption.
- The full open is allowed when f after base change is finite; disconnected
  opens and arbitrary finite parts are allowed. No cardinality or rank is fixed.
- No assumptions on characteristic, Noetherianity, reducedness, or components
  appear. In particular a separated morphism locally of finite type need not
  be flat or locally of finite presentation for this statement.
- Taking h to be an identity or a composite recovers ordinary inverse image;
  uniqueness of b supplies the same canonical pullback identifications.

Searches performed:

- msearch.py LeanFinder: “The functor of finite open subschemes of a separated
  locally finite type morphism is an etale algebraic space”. Eight hits were
  scheme étale-category and étale-property declarations, none this theorem.
- msearch.py Loogle: `AlgebraicGeometry.AlgebraicSpace,
  AlgebraicGeometry.IsFinite`. No hits; AlgebraicSpace is a project declaration,
  unknown to the Mathlib-only index. Its actual project source was then read.
- msearch.py grep, AlgebraicGeometry: `finite.*open.*(part|functor)|finiteOpenPart|04QH`.
  One unrelated FlatMono docstring hit, no finite-open-part parameter functor.
- msearch.py LeanSearch: “The functor of finite open parts of a separated locally
  finite type scheme morphism is an etale algebraic space”. Eight results were
  opens diagrams, finite/quasi-finite constructors, and étale loci; none matched.
- Direct rg of Mathlib/AlgebraicGeometry for `finite.*open.*functor|finiteOpenPart|04QH`:
  no hits. Direct rg of both lean/WeilConjectures and lean/Sheaf for the node id,
  finite-open-part spellings and Tag 04QH found no existing statement. Broad
  finiteOpen searches found unrelated finite-cover and six-functor work.
  The expected declaration name is absent from both source roots.
- The existing node and all its statement-dependency records were inspected;
  there is no reusable finite-open-part parameter-space declaration there.
  `tools/blueprint_refs.py ancestor` reports the inherited ancestor None; no new
  definition node is needed.

The previous worker's unchanged-item rejection was a stage-1 handoff, not a
mathematical fault. The node is stage 2 in coord/queue.tsv and has no Lean record.
The current delivery adds that record and the new module.
No STATEMENT-DISPUTED issue or statement correction is needed.

Validation: scompile.py compiled both sandbox and actual module successfully
against the published server library. Initial nonexistent import paths for
source-local étaleness and residue-field maps were replaced by their actual
Mathlib source modules. No additional warnings or errors remained.

## Second reading by Q22

The author reread the node and complete signature after the successful compile;
no independent second worker was started, as the dispatcher explicitly forbids
starting agents. Independent review is performed by the maintainer.

This second pass checked the separated and local-finite-type binders on f, both
sigma/subtype fields, the sheaf-value type of e, compatibility with the forgetful
p, both projection equations and the inverse-image equation, and the final
universal quantification over representable étale scheme charts. In particular,
p is not accidentally asserted representable étale. The atlas size is contained
in the reused algebraic-space definition, with `U : Over S`. The canonical map b
cannot be freely chosen because both its projections are specified. The first
component's naturality follows from p; the second component is stated explicitly,
so this signature does not omit restriction or replace natural bijections by
unrelated pointwise bijections. No mathematical mismatch was found, and no node
statement, proof, or dependency was changed.
