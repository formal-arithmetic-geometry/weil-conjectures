## Worker report

Item: lem-coef-enriched-yoneda-evaluation. Module:
`Sheaf.CategoryTheory.EnrichedYonedaEvaluation`. Main declaration:
`CategoryTheory.SimplicialYoneda.enriched_yoneda_evaluation`.

The module states strict enriched Yoneda evaluation and constructs the actual
representable, its enriched postcomposition maps, end-component application, and
identity evaluation. All three theorem proofs are `sorry`; no proof is supplied.
The two auxiliary theorem statements are the representable's functor laws and the
all-mapping-simplices naturality of its postcomposition components, part of the
canonical representable construction in this node. Every helper is recorded in
`lean.declarations` and has this node's blueprint tag and source.

Hypotheses and clauses, matched individually:

- Small simplicial category: `{A : Type u} [Category.{u} A]
  [SimplicialCategory A]`. These are explicit section binders, not auto-implicits.
  Its opposite uses Mathlib's `EnrichedCategory.opposite` and
  `EnrichedOrdinaryCategory.opposite`.
- Locally Kan: `hA : ∀ a b : A, SSet.KanComplex (sHom a b)`.
- Simplicial sets, Kan complexes, and simplicial operators use the existing
  Mathlib notions imported by `EnhancedDiagramsCones`. No coherent-cone or Kan
  definition is repeated.
- The enriched functor category and its mapping ends use
  `E : SimplicialDiagramEnrichment Aᵒᵖ SSet.{u}`. Its `Diagrams` wrapper has
  genuine enriched transformations as arrows. Its mapping objects represent
  Mathlib's `enrichedNatTransYoneda`; that presheaf consists of `GradedNatTrans`,
  whose naturality equation is an equality on the entire mapping simplicial set.
  This avoids the ordinary-arrow-only `EnrichedNatTrans` interface.
- The given projective simplicial model structure is the class binder
  `[@ProjectiveSimplicialModelStructure _ _ _ _ _ kanModel _ T E]`.
  `T : SimplicialTensorCotensor SSet.{u}` supplies the tensor/cotensor data the
  recorded interface requires. This does not assume an unrelated comparison
  map or a new theorem. The projective structure itself identifies its
  fibrations, weak equivalences and enriched end as stipulated by the node.
- `kanModel` is extracted from the first conjunct of the recorded
  `SSet.ProjectivePresheaf.simplicial_presheaf_projective_model`. That assertion
  fixes fibrations, cofibrations and weak equivalences individually. Every
  remaining field of `ModelCategory` is a proposition, including the finite
  limit/colimit existence classes. Consequently its model structure is uniquely
  determined, and the extraction postpones only proof, as permitted by AGENTS §5.
  It chooses no object, diagram, factorization, or map from mere existence.
- The object `Y_a = A(-,a)` is `representable a`, whose value at `x : Aᵒᵖ`
  is `sHom (op a) x = A(x.unop,a)` and whose action is the transpose of enriched
  composition in the opposite category. `representableAction_laws` states its
  identity and composition laws. `representableObject E a` only wraps this
  actual enriched functor in the recorded diagram category.
- Projectively cofibrant-fibrant P: the existing
  `SimplicialModelLocalization.Bif E.Diagrams` is the full subcategory defined by
  `IsCofibrant P ∧ IsFibrant P`. No extra restriction on evaluated objects is used.
- The simplicial isomorphism is `ε a P : sHom (representableObject E a) P.obj ≅
  (SimplicialDiagramEnrichment.value P.obj).obj (op a)`.
- Restriction at the enriched identity is fixed by the first conjunct
  `(ε a P).hom = evaluation E a P.obj`. The definition of `evaluation` inserts
  `eId SSet (op a)` before `componentApplication`, which uncurries the actual end
  projection. Hence it is identity evaluation in every degree, with the unit
  object giving the constant identity simplex.
- The inverse is fixed by the second conjunct, for every `x : Aᵒᵖ`:
  `(𝟙 _ ⊗ₘ (ε a P).inv) ≫ componentApplication ... x =
  (β_ _ _).hom ≫ uncurry ((value P.obj).map (op a) x)`.
  Uncurrying says exactly `(f,p) ↦ P(f)(p)`, including restriction of p along
  every simplex parameter. These equations fix the inverse uniquely because
  the represented enriched end is determined by all of its projections.
- Naturality in P on full mapping complexes is the third conjunct. Its source is
  `Map(Y_a,P) ⊗ Map(P,Q)`, not a set of ordinary arrows. The left composite first
  uses enriched composition and then `ε a Q`; the right evaluates via `ε a P`
  and then applies the end component of the arbitrary parameterized P-to-Q map.
  P and Q range over the full cofibrant-fibrant subcategory, retaining all their
  mapping simplices.
- Naturality in a on full mapping complexes is the fourth conjunct. Its source
  is `A(a',a) ⊗ Map(Y_a,P)`. The Yoneda map `postcomposition E a' a` is lifted
  through `E.represents.inv` from the genuine graded transformation whose
  component is transposed composition `A(x,a') × A(a',a) → A(x,a)`. The right
  side of the equality is precisely the enriched action of P on the same
  mapping parameter and on `ε a P`.
- Faces and degeneracies are preserved because ε is an actual isomorphism in
  `SSet`, and both naturality clauses are equalities of simplicial maps. These
  include every map of the simplex category, not merely vertex restrictions.
- The last two conjuncts state the enriched unit and composition equalities for
  the Yoneda maps. In the P variable, the corresponding equalities are already
  part of `E.projection_id` and `E.projection_comp`; the third conjunct is their
  compatibility with ε. They are used rather than repeated as tautological
  conjuncts. The two inverse identities of the isomorphisms imply both
  naturality equations for the inverse as well. Combining the two equations
  with the graded naturality of a P-to-Q transformation makes the two actions
  commute, as in step 6 of the node's proof.

Dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, recorded
  `SSet.Enhanced.coneCategory`: signature and docstring read; this dependency
  provides the simplicial-set and Kan conventions, while this statement uses
  those existing Mathlib primitives directly.
- `Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel`,
  `SSet.ProjectivePresheaf.simplicial_presheaf_projective_model`: complete
  signature and proof docstring read. Its fixed Kan model structure supplies
  `kanModel`; the module also remains part of the statement and proof plan.
- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`,
  `CategoryTheory.simplicial_projective_model_calculus`: complete signature and
  proof docstring read, including the current server source via `scompile.py
  --source`. Reuses `SimplicialDiagramEnrichment`, `Diagrams`, `value`,
  `projection`, `represents`, `represents_projection`, `projection_id`,
  `projection_comp`, and `ProjectiveSimplicialModelStructure`. Nothing in this
  dependency is replaced or restated.
- Mathlib `EnrichedFunctor`, `GradedNatTrans`, `ForgetEnrichment`, opposite
  enrichments, `MonoidalClosed.curry`/`uncurry`, internal homs and braidings are
  used directly. The standard closed self-enrichment of SSet gives its usual
  Cartesian simplicial mapping object.

Edge cases checked before writing and when reviewing the formulas:

- Empty A is allowed: all a-indexed conclusions are vacuous, and the equations
  impose no nonemptiness condition. No distinguished object is assumed.
- Empty mapping sets are allowed; a self-mapping set has its required identity.
  The construction never chooses a vertex of another mapping space.
- In degree zero the insertion is precisely the identity vertex and inverse
  application is the usual Yoneda formula. In arbitrary degree the same maps
  use the constant identity simplex and retain all parameter restrictions.
- P(a) may be empty. The isomorphism then asserts the end is empty too, rather
  than assuming a point or connectedness.
- Nontrivial higher mapping simplices are retained by `GradedNatTrans` and by
  the enriched-end projection conditions. Naturality is not only naturality in
  the underlying ordinary category.
- The small-object and simplex universe is the same `u` for objects, mapping
  sets and values; the category of all SSet-valued diagrams lies in the
  containing universe, as in the dependencies. No bound is put on dimension.

Searches made:

- `msearch.py`, LeanFinder, query "Simplicial enriched Yoneda evaluation of
  enriched natural transformations from a representable presheaf is an
  isomorphism of simplicial sets", and follow-up "Simplicial enriched Yoneda
  evaluation isomorphism representable enriched presheaf". Returned
  `Presheaf.functorEnrichedHomCoyonedaObjEquiv`,
  `enrichedNatTransYonedaTypeIsoYonedaNatTrans`, `eCoyoneda`,
  `enrichedNatTransYoneda`, and ordinary representability tools. No exact match.
- `msearch.py`, Loogle, `CategoryTheory.EnrichedFunctor, "yoneda"`: four hits,
  the graded-transformation presheaf and its generated equations, and the
  Type-enriched comparison theorem. None is the simplicial evaluation theorem.
- `msearch.py`, LeanSearch, "Enriched Yoneda lemma for simplicial presheaves
  evaluation at identity is a simplicial isomorphism": eight hits, including
  ordinary `yonedaLemma`, `curriedYonedaLemma`, and `SSet.yonedaEquiv`.
  None treats an arbitrary simplicial indexing category and the enriched end.
- `msearch.py`, grep, `yoneda|Yoneda`, in `CategoryTheory/Enriched`: eleven hits,
  including the graded-transformation presheaf and ordinary `eCoyoneda`.
- Read Mathlib `Enriched/Basic.lean` (including the complete Type comparison),
  `Enriched/Ordinary/Basic.lean`, `Enriched/FunctorCategory.lean`,
  `Sites/Monoidal.lean`, `Enriched/Opposite.lean`, and
  `AlgebraicTopology/SimplicialCategory/Basic.lean`. The Type comparison only
  concerns Type enrichment; `eCoyoneda` is an ordinary functor; functor-category
  ends and the sites comparison use ordinary indexing categories.
- `rg` in upstream `WeilConjectures` and in `lean/Sheaf` for Yoneda and enriched
  Yoneda names found uses in rectification, coherent weights, cone presheaves,
  and infinity-Yoneda comparison modules, but no strict evaluation declaration.
  `grep -rn` for this exact item id in upstream returned no match. Searches for
  the newly declared full names in Mathlib, upstream, `lean/Sheaf` and the
  upstream declaration index found no collision.

Source checked: HTT §5.1.3 opening paragraph, printed p. 319 (PDF p. 336),
and Appendix A.3.3.2--A.3.3.5, printed pp. 870--871. Read at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf after the IAS mirror timed
out. The unit statement in the current main-20261015 blueprint was read; this
item supports its coefficient adjunction argument and is not the unit statement.
No statement correction, new independent notion, dependency repair, or
STATEMENT-DISPUTED flag was needed.

Validation: every delivered declaration compiled cleanly through the prescribed
`scompile.py Q11 lem-coef-enriched-yoneda-evaluation` wrapper, including the
library-named module compile. Initial failures in the enrichment wrapper and
explicit model-structure binding were repaired. The final compile emitted no
errors or warnings. All variables and the sole universe are explicitly bound;
all lines are at most 100 characters. Delivery dry run follows this check.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
