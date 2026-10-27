## Worker report

The delivery states `CategoryTheory.self_relation_quotient_embedding` in
`Sheaf.AlgebraicGeometry.SelfRelationQuotientEmbedding`. Its only postponed proof
is this named theorem. No definition, auxiliary axiom, or theorem proof was added.
The natural-language node statement and its accepted proof remain unchanged.

The source is the local Stacks Project `algebraic.tex`,
`lemma-map-space-into-stack` (Tag 04T4), parts (1), (4), (5), (6), including the
triple formulas and composition convention in its proof; the final conditional
uses `lemma-characterize-representable-by-algebraic-spaces` (Tag 04Y5), (2) to (3).
The node uses source = first coordinate, target = second coordinate. This follows
its own stated convention; the source proof explicitly discusses the opposite
convention and its equivalent groupoid. Composition here is `c(q,r) = q after r`.

Hypothesis and clause correspondence:

- Base scheme and sizes: `{S : Scheme.{u}}`, explicit universes
  `u v₁ w₁ v₂ w₂`. Target and quotient total categories have independently
  quantified object and hom universes. There is no extra size equality.
- Algebraic target stack: `X : BasedCategory.{v₁, w₁} (Over S)` and
  `hX : IsAlgebraicModuliStack X`. This is the existing etale-stack/diagonal/smooth
  atlas convention, equivalent here to the node's fppf-stack convention:
  `isFppfModuliStack_of_etale_smooth_atlas` supplies fppf descent from exactly
  these hypotheses. This equivalence requires no new hypothesis or correction.
- The algebraic space U and its arbitrary map: `(U : AlgebraicSpace S)` and
  `(a : BasedFunctor (discreteModuli U.obj.obj) X)`. No property of a is assumed.
- R is an algebraic space representing the actual self-relation: the existential
  `R : AlgebraicSpace S`, endpoint natural transformations `s t`, and vertical
  natural isomorphism `η : a s ≅ a t`. For all test schemes and all endpoints,
  the `∃! r` clause identifies the endpoint fibre of R with every vertical arrow
  `β : a(x) ⟶ a(y)`. Such arrows are isomorphisms because X is fibred in groupoids.
  Naturality of η makes this an identification of the whole isomorphism
  presheaf, rather than an unrelated pointwise cardinality assertion. It is
  precisely the triple description of the discrete 2-fibre product U ×_X U.
- Source, target, identity, inverse, and composition: `s`, `t`, `e`, `j`, `c`
  together with `AlgebraicSpace.IsPresheafGroupoid s t e j c` assert every
  groupoid law on every scheme test, including naturality of all operations.
  The subsequent composition equation identifies the image of c(q,r) under η
  with the composite of the images of r and q. Bijectivity on arrows and the
  groupoid laws then force e and j to be the identity and inverse of those same
  isomorphisms, not a different groupoid structure on R.
- Object map to the fppf quotient: universally quantify `Q`, the based functor
  `q : discreteModuli U.obj.obj ⟶ Q`, and
  `hQ : SpaceGroupoidQuotientPresentation s t e j c Q q`. This is the existing
  presentation of the fppf stackification: arrow sheaves with their specified
  comparison and composition, effective fppf descent, and local representatives.
  The node's "let q" is thus rendered for any presentation of its quotient,
  with no arbitrary stackification data chosen from a sorried existence theorem.
  The stackification existence input is the recorded local-description theorem.
- The induced morphism and its specified 2-isomorphism:
  `∃ (i : BasedFunctor Q X) (θ : ModuliTwoIso (q.comp i) a), ...`.
  The first equation fixes the map on every original relation arrow:
  `i(η_Q(r)) ≫ θ_target = θ_source ≫ η_X(r)`. Thus the map is the induced map
  on the specified quotient, with its comparison to a retained.
- Fully faithful on each fibre: for every `T` and `b d : Functor.Fiber Q.p T`,
  `Function.Bijective ((moduliFiberMap i T).map (X := b) (Y := d))`.
  This includes fullness and faithfulness, on every hom set, exactly the node's
  definition of monomorphism. No ordinary-category `Mono` is substituted.
- Conditional representability:
  `IsAlgebraicModuliStack Q → IsRepresentableByAlgebraicSpaces i`.
  The quotient is not assumed algebraic for the existence or full-faithfulness
  clauses. No smoothness, flatness, finite presentation, local finite type,
  surjectivity, or separatedness hypothesis on a or R's projections is added.
  The node's discussion of chartwise flatness/finiteness/surjectivity specifies
  background conventions, not additional assumptions in this lemma.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, its representability predicates.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `IsFibredInGroupoids`, `moduliFiberMap`, `IsRepresentableByAlgebraicSpaces`,
  `HasSpaceBaseChange`, `HasAlgebraicSpaceDiagonal`, `IsModuliStack`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid`:
  `AlgebraicGeometry.AlgebraicSpace.IsPresheafGroupoid`.
- `Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation`:
  `spaceGroupoidPresentationArrow`, `SpaceGroupoidQuotientPresentation`,
  including its arrow bijection, local image, and composition fields.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
- `Sheaf.CategoryTheory.SiteStackification`: `IsFppfModuliStack`,
  `IsFppfStackification`; these are the quotient presentation's fppf conventions.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `Pseudofunctor.exists_groupoid_stackification_local_description`. Its interface
  uses pseudofunctors in the common larger universe; our quotient-presentation
  interface is the already recorded total-category description of that same
  local characterization. It is imported as the recorded statement dependency.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over` gives the over-site.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `.Flat`, `.FinitePresentation`,
  `.FiniteType`, `.QuasiCompact`, and `Mathlib.Algebra.Field.Defs`: the recorded
  smooth, flat, locally finitely presented, locally finite type, quasi-compact,
  and field notions, read for the node's background conventions. They are
  exposed through the existing stack and algebraic-space imports.
- Proof imports: `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`
  (`AlgebraicSpace.schemeSpace`), `.AlgebraicStackFibreProducts`
  (`algebraicStack_twoFiberProduct`), `.AlgebraicStackSetoidSpace`
  (`algebraicStack_setoid_space`), and `Mathlib.CategoryTheory.Sites.Sheafification`
  (`presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`). Also import
  `.EtaleSmoothAtlasFppfDescent` for the convention comparison described above.
- The proof-only nodes `lem-sfb-stack-diagonal-space-source-representability`
  and `lem-sfb-representable-pullback-over-space` have no Lean record in the read
  clone, so there is no module to import for them yet. They do not supply a
  missing statement notion: the relation's representation is asserted here,
  not assumed. Their accepted proof steps remain in the theorem docstring.

Only the item's `lean` record and additions to `stmt_deps` change. The added
dependencies are the already landed definition nodes
`def-sfb-algebraic-space-groupoid`,
`def-sfb-space-groupoid-quotient-presentation`, and
`def-sfb-algebraic-moduli-stack`. No new definition node or dependency repair is
needed, and there is no statement correction or disputed statement.

Edge cases checked before writing:

- Empty U gives the empty self-relation, and the fppf quotient includes descent
  on the empty scheme (and its empty covering). There is no nonemptiness binder.
- Identity map of a space gives its diagonal relation and the identity quotient
  equivalence. A map with nontrivial automorphisms retains all those arrows in R;
  passing to an orbit sheaf instead would fail, and is not done here.
- Nonalgebraic quotient is permitted and still receives a fully faithful map.
  Only the last implication requires quotient algebraicity.
- No atlas or flatness hypothesis on U → X, no positive dimension or
  characteristic condition, and no restriction to geometric points replaces
  the test on all scheme fibres.

Searches for an existing statement (2026-10-24; recorded by `msearch.py` in
`searches.jsonl`):

- LeanFinder: "The quotient stack of the self relation U times X U maps fully
  faithfully to X". Eight hits: scheme forgetful functors, ordinary quotient
  categories, Yoneda, and descent full faithfulness. No self-relation result.
- Loogle: `CategoryTheory.Functor.FullyFaithful`. Twelve hits for the generic
  structure and its elementary operations. These do not assert the stack result.
- Mathlib grep: `selfRelation|SelfRelation|quotientStack`, restricted to
  `CategoryTheory`. Zero hits.
- LeanSearch: "quotient stack of self relation maps fully faithfully into target
  stack". Eight hits about quotient categories and quotient functors; no stack
  result.
- Project/source searches: `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `self.relation|SelfRelation|selfRelation|quotient.*[Ee]mbed`; references in
  supporting stack modules, but no existing statement. A literal item-id search
  in `lean/WeilConjectures` gave no hits. Exact proposed names
  `self_relation_quotient_embedding|selfRelationQuotient` gave no hits across
  Mathlib, upstream, and Sheaf. These searches located and reused the existing
  `SpaceGroupoidQuotientPresentation` instead of creating another quotient notion.

Validation: `scompile.py O4 lem-sfb-self-relation-quotient-embedding` compiled the
module as both sandbox and final library module (4.9 s and 4.6 s). No errors or
warnings were reported. `autoImplicit` is false and all universe and object
variables are explicit. The required `deliver2.py --no-push` passed preflight
and compilation, reporting `OK (dry run)` at commit `7649e280cdf`.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
