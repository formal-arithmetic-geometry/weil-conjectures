## Worker report

The module `Sheaf.AlgebraicGeometry.StackAlgebraSmoothImage` states
`CategoryTheory.exists_moduliAlgebraSmoothImage`, with its proof `sorry`.
Two real helper definitions supply the actual underlying module map and its
morphism in the existing full quasi-coherent subcategory. There are no other
postponed proofs, new mathematical notions, new nodes, dependency rewrites or
statement corrections.

Hypothesis and conclusion audit:

- The field is `(k : Type u) [Field k]`. The stack over k is
  `X : BasedCategory.{v, w} (Over (Spec (.of k)))` with
  `hX : IsAlgebraicModuliStack X`. The existing predicate includes fibred
  groupoids, etale descent, representable diagonal and a smooth surjective atlas;
  its `hX.1.1` supplies the fibred-groupoid proof used by the ringed site.
- Arbitrary commutative algebra sheaves are `A B : ModuliAlgebraSheaf X hX.1.1`,
  and `f : A ⟶ B` is their actual structure-map-preserving ring-sheaf morphism.
  `hA` and `hB` use `IsQuasicoherentModuliAlgebra`, the recorded ringed-site
  local-presentation predicate. No generation, Noetherian, quasi-compactness,
  nonzero-algebra, or injectivity assumption is introduced.
- The result supplies `C`, its quasi-coherence `hC`, and algebra morphisms
  `q : A ⟶ C`, `j : C ⟶ B`, with `q ≫ j = f`.
  `IsSurjectiveModuliAlgebra q` is exactly local surjectivity for the big fppf
  site, rather than surjectivity of each section map.
- The QCoh image inclusion is an actual Mathlib `ImageFactorisation` of
  `moduliAlgebraImageQCohMap f hA hB`. The isomorphism `e` identifies its image
  object with the underlying quasi-coherent module of C. Both equations are
  included: `e.hom ≫ I.F.m` is the underlying j and the underlying q followed
  by `e.hom` is `I.F.e`. Thus this is the whole image factorization, with its
  inclusion and quotient, not merely an isomorphism of objects. In particular
  no ambient big-site module monomorphism has been assumed or asserted.
- A scheme test is `T : Over (Spec (.of k))` and
  `a : BasedFunctor (discreteModuli (yoneda.obj T)) X`. Its smoothness is the
  existing `ModuliSpaceTest @Smooth a`: every scheme base change is an
  algebraic space with smooth projection on all etale scheme charts.
  Its distinguished test object is
  `a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T)))`.
- For every recorded comparison `R : ModuliSchemeRestriction X hX.1.1`, the
  `R.restriction` of the underlying f is given an `ImageFactorisation` in
  ordinary Zariski modules on the underlying scheme of that test object.
  Again both equations relating the quotient and inclusion are present.
  This states the ordinary scheme image, rather than just its value on
  global sections. The algebra structure on this module image is the induced
  one: q and j were algebra morphisms, and R's normalized structure/tensor
  comparisons transport their unit and multiplication. A multiplication on
  the image making q an algebra map is uniquely determined by precomposition
  with the locally surjective q tensor q; the unit is q composed with the
  original unit. Consequently identifying this full underlying image
  factorization identifies its ordinary image algebra as well. No independently
  chosen multiplication or isomorphism of algebras is used.
- The next conjunct is explicitly `Function.Injective` for the actual
  component `j.right.hom.app` at that distinguished smooth scheme test;
  these are exactly C(T) -> B(T).
- Finally Z is any `BasedCategory.{v', w'}` over k with
  `IsAlgebraicModuliStack Z`, and `a : BasedFunctor Z X` is any smooth map.
  The smoothness condition is expanded without defining a new predicate:
  there is a smooth surjective scheme atlas `p : U -> Z` whose composite
  `p.comp a` satisfies `ModuliSpaceTest @Smooth`. This is the usual
  source-atlas criterion for smoothness and includes nonrepresentable maps
  a; representability is tested only for the composite from the scheme.
  `Functor.sectionsFunctor Z.objᵒᵖ` applied to the whiskered actual j is the
  map on compatible families of sections of literal precomposition along a.
  `Function.Injective` is precisely the stated injectivity on Gamma(Z,a*C)
  -> Gamma(Z,a*B). The rings have the original pointwise operations, and
  forgetting them to sets does not alter injectivity. This is the compatible
  section-family convention of `moduliGlobalSections` and
  `moduliGlobalSectionsRing`, whose raw diagrams are used here to retain
  independent universes for Z and X.

Dependency interfaces read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (via the public imports).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `IsAlgebraicModuliStack`, `IsSmoothModuliAtlas` (available publicly from
  the recorded algebra/restriction modules).
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `ModuliAlgebraSheaf`, `moduliAlgebraModule`,
  `IsQuasicoherentModuliAlgebra`, `IsSurjectiveModuliAlgebra`, and the
  fppf site and structure ring. The section-family definitions were read.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction`:
  `ModuliQCoh`, `ModuliSchemeRestriction.restriction`, its structure,
  tensor and section normalizations, and `exists_moduliSchemeRestriction`.
  The comparison is quantified in the conclusion; its existence is already
  provided by the dependency, not an extra theorem hypothesis.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest`.
  Its already landed node `def-sfb-dm-stack-morphism-properties` is the
  sole addition to stmt_deps, under brief-stage2 section 5's permission
  to cite a landed definition. This existing definition applies to arbitrary
  based categories despite its owning module's DM title.
- `Mathlib.CategoryTheory.Limits.Shapes.Images`: `ImageFactorisation`,
  including its monic leg and `IsImage` universal property.
- `Mathlib.CategoryTheory.Types.Basic`: `Functor.sectionsFunctor`.

Plain proof imports are the recorded modules of stack QCoh abelianity,
independent-coefficient tensor colimits, ordinary algebra-sheaf images,
scheme QCoh kernels, and scheme QCoh cokernels/images. The other proof
nodes (flat-atlas exactness, smooth QCoh exactness and smooth-cover section
descent) had no recorded Lean modules when read; their mathematical steps
are retained in the theorem's complete proof docstring. No proof prerequisite
is used as a new assumption.

The upstream `commAlgebraSheafModuleFunctor` was inspected in
`WeilConjectures.CategoryTheory.CommAlgebraSheafModule`: it specializes to
ordinary topological spaces and common coefficient/space universes and
cannot be applied to the total fibred-category site. The two local public
helpers construct only the missing actual maps, with the dependency's
`moduliAlgebraModule` objects unchanged. Their data are the original
component ring maps; linearity follows directly from `Under.w` and
multiplicativity. They introduce no duplicate algebra/module/QCoh definition.

Edge cases checked before drafting: zero and identity algebra morphisms,
zero rings as algebra values, the empty stack and empty smooth scheme test,
non-Noetherian and arbitrarily generated algebras, and smooth maps that
are not representable. All remain included. In particular the zero-ring
map is meaningful when it is a unital algebra map; no arbitrary non-unital
zero morphism of algebra sheaves is assumed. For the identity the entire
algebra is its image, while an empty test has a singleton section ring.
The base-scheme, site-object and site-morphism universes u, v, w are
independent, with the dependency's existing common coefficient universe
max (u+1) v w. Source-stack universes v', w' are also independent in the
last clause; precomposition and section families need no equality of them.

Sources read: Stacks `stacks-sheaves.tex`, lemma-quasi-coherent-algebraic-stack
(06WV), including the distinction between QCoh and ambient module exactness;
`stacks-cohomology.tex`, lemma-flat-pullback-quasi-coherent (076X) and
lemma-quasi-coherent-check-exact (0GQF). Also read the latest blueprint's
`sk-thm-sf-ctf-stability-direct-images` statement and proof (3), as recorded
in this auxiliary node's inherited adequate-moduli prerequisite route.
The node statement agrees with those inputs; no STATEMENT-DISPUTED fault.

Searches for an existing statement (2026-10-24):

- msearch leanfinder: "Image factorization of quasi-coherent algebras on an
  algebraic stack with injective smooth restriction". Eight hits, including
  scheme target-image factorizations and scheme sheaf injectivity; no stack
  quasi-coherent algebra image statement.
- msearch loogle: `"Quasicoherent", "image"`. Zero hits.
- msearch grep: `moduli.*[Ii]mage|[Ii]mage.*[Mm]oduli|[Qq]uasicoherent.*[Ii]mage`.
  Zero Mathlib hits.
- msearch leansearch: "Image factorization of arbitrary quasi coherent
  commutative algebras on algebraic stacks compatible with smooth restriction".
  Eight generic categorical-image hits; reused `ImageFactorisation`.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  moduli images and smooth moduli properties, and focused image searches
  in upstream CategoryTheory and AlgebraicGeometry/Modules. No matching
  theorem. The scheme algebra-image theorem is a proof input; it does not
  apply on the stack's big site where QCoh inclusion need not be exact.
- `grep -rn` of the item id in upstream WeilConjectures: no hits.
- Direct name search of `dag/lean_names_upstream.json` and both source
  trees: none of the three delivered declaration names already exists.

Validation: prescribed scompile.py compiled the sandbox file and final
module path cleanly against the live server library, under its normal
60-second limits (12.7 s sandbox, 4.7 s library). autoImplicit is false;
all universes are explicitly declared. The only sorry is the named item
statement. The first deliver2.py dry run passed both server preflight and compilation
(commit 08e0f0c5d8e, nothing pushed). Direct public imports of all recorded
statement modules were then made explicit before the final dry run and delivery.

## Second reading by NM

This is the delivering worker's second clause audit, not an independent
agent review. The dispatch brief prohibits starting another agent and
assigns the independent review to the maintainer. Reopened the node and
Lean file together: checked k and stack hypotheses, arbitrary QCoh
algebras, the two factorization equations, fppf-local surjection, QCoh
image rather than ambient image, scheme image compatibility including
both arrows, the explicit C(T) injection, and arbitrary smooth-stack
section injection. The final smoothness condition only requires a
representable composite from a source atlas, so it does not discard
nonrepresentable smooth morphisms. No statement text was changed. No
mismatch was found in this second audit.
