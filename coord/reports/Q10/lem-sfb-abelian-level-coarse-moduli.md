## Worker report

`Sheaf.AlgebraicGeometry.AbelianLevelCoarseModuli` states
`AlgebraicGeometry.abelian_level_coarse_moduli`, with its proof `sorry`.
`Sheaf.AlgebraicGeometry.ModuliStackProperties` supplies two actual Prop-valued
definitions, without postponed proofs or chosen data. No existing definition is
replaced, and the item's natural-language statement and proof remain unchanged.

The previous worker's unchanged-node rejection came from mistaking the ND
stage-1 delivery for a stage-2 delivery. The current item has no `lean` record;
ND's report explicitly says it is a stage-1 split. This delivery attaches an
actual theorem and adds the one missing definition node to `stmt_deps`.

Clause-by-clause correspondence:

- A field `k`: `(k : Type u) [Field k]`, using Mathlib's field definition.
- Genus at least two: `(g : ℕ) (hg : 2 ≤ g)`. Nonnegative genus is integral,
  and this covers every integer satisfying the node's bound.
- A prime level at least three invertible in `k`:
  `(ℓ : AbelianLevelPrime (Spec (.of k)))`. The recorded subtype means
  `ℓ.val.Prime ∧ 3 ≤ ℓ.val ∧ ∀ x, IsUnit (ℓ.val : S.presheaf.stalk x)`.
  For `S = Spec k`, local-ring invertibility is exactly invertibility in the field.
- The precise groupoid of smooth projective geometrically connected genus-`g`
  curves with full abelian level structure is
  `BasedCategory.ofFunctor (AbelianLevelModuli.forget (Spec (.of k)) g ℓ)`.
  Its recorded `family` is a smooth stable unpointed genus-`g` family with the
  specified projective-bundle condition; its `frame` is the isomorphism from the
  constant rank-`2g` module sheaf to `abelianLevelCohomology`. The already defined
  category uses frame-preserving cartesian family isomorphisms. Thus this is
  neither a set of curves nor a new, private moduli definition.
- Deligne--Mumford: `IsDeligneMumfordModuliStack` of that exact based category.
  This uses the recorded stack descent, algebraic-space diagonal, and surjective
  etale atlas conditions.
- Separated stack: `HasProperModuliDiagonal` of the same category. This tests
  every pair `h_T → F`, `h_U → F`, represents their actual 2-fibre product by
  `h_R`, and requires `IsProper (prod.lift p q).left`. The product is in
  `Over S`, so it is `T ×_S U`. The equivalence commutes with BOTH projections:
  its first comparison is `ModuliTwoIso`, and its second is a natural isomorphism
  whose components satisfy `IsHomLift` over the identity of every test base.
  For a DM stack this is precisely a proper diagonal. Indeed the unramified
  DM diagonal is locally quasi-finite, so properness makes it finite and its
  scheme base changes are schemes. This scheme-test formulation imposes no
  extra hypothesis on the stack.
- Smooth and finite type: `HasSmoothFiniteTypeModuliAtlas` of the same category.
  Its witness is an actual etale surjective scheme atlas `U → F`, tested after
  every scheme base change by `HasSpaceBaseChange`, `SpaceMapIsEtale`, and
  `SpaceMapIsSurjective`. Its structure map satisfies `Smooth U.hom`,
  `LocallyOfFiniteType U.hom`, and `QuasiCompact U.hom`. On a DM stack over a
  field this is equivalent to smoothness and finite type: restrict an etale
  atlas to finitely many affine opens covering a quasi-compact stack; conversely
  the displayed atlas tests the local properties and supplies quasi-compactness.
  The explicit quasi-compactness clause avoids confusing local finite type
  with finite type.
- The coarse moduli `k`-scheme and coarse morphism:
  `∃ (C : Over (Spec (.of k))) (c : BasedFunctor F
  (discreteModuli (yoneda.obj C))), ...`.
- The full coarse universal property and geometric class bijection:
  `IsCoarseModuliScheme F C c`. Its first clause is the bijection, induced by
  composition with this very `c`, for every algebraic space over the base.
  Its second clause is bijectivity of the induced skeleton map on every
  algebraically closed field fibre. No independently chosen point bijection
  or restriction to scheme-valued destinations replaces those clauses.
- The coarse scheme is separated and of finite type:
  `IsSeparated C.hom ∧ LocallyOfFiniteType C.hom ∧ QuasiCompact C.hom`.
  This uses the node's scheme-morphism conventions. No smoothness, projectivity,
  or fine representability of this scheme is added to the theorem's conclusion.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `AlgebraicGeometry.AbelianLevelPrime`, `AbelianLevelModuli`,
  `AbelianLevelModuli.forget`, `abelianLevelConstant`, `abelianLevelCohomology`,
  `CategoryTheory.discreteModuli`, `discreteModuliMap`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `ModuliTwoIso`, `IsCoarseModuliScheme`,
  `IsDeligneMumfordModuliStack`, `HasSpaceBaseChange`, `SpaceMapIsEtale`,
  `SpaceMapIsSurjective`. Their signatures and docstrings were read in full.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.AlgebraicGeometry.Scheme`:
  `AlgebraicGeometry.Scheme`; `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `Smooth`; `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `QuasiCompact`; `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`.
- The definition module uses the existing product in `Over S` from
  `Mathlib.CategoryTheory.Limits.Constructions.Over.Products` and Mathlib's
  `BasedCategory`, `BasedFunctor`, `Comma.snd`, and `IsHomLift` definitions.
- The main module imports every currently recorded proof module:
  `Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective`,
  `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`,
  `WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable`,
  `Sheaf.TraceFormula.ProjectiveBundleProper`, and
  `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine`.
  Proof dependencies with no current `lean` record are named in the full
  natural-language proof docstring and contribute no speculative import.

Source and edge-case checks:

- Read the primary author PDF, https://arxiv.org/pdf/alg-geom/9501003,
  printed pp.9--10, the specified paragraphs, Theorem 2.3.2(1), and §2.3.3.
  Its full abelian frame has no symplectic restriction. No roots of unity or
  algebraic closure of the base field are assumed here.
- Read the local Stacks `stacks-morphisms.tex` definitions of separated,
  smooth, and finite-type morphisms, including the quasi-compactness clause.
- Genus two and level three are included. Positive characteristics different
  from the level are included; characteristic equal to the level is excluded
  by exactly the specified invertibility hypothesis. Characteristic zero is
  included without an extra characteristic binder.
- Empty test schemes and empty 2-fibre products are allowed. Neither the
  atlas scheme nor the scheme presenting a diagonal base change is required
  to be nonempty. Properness of the empty diagonal base change is appropriate.
- No nonemptiness or surjectivity of the frame-forgetful finite etale cover is
  asserted. The atlas itself is required to be surjective, as in the source.
- Universes of the field and test schemes agree with the recorded groupoid's
  size convention. `v,w` on the auxiliary predicates allow the actual large
  total categories. Every universe and variable is bound explicitly.
- A comparison for only the first projection could allow an unrelated second
  map; the second comparison and its identity-lift condition prevent that.
  Similarly a single smooth family is insufficient: every atlas base change
  is explicitly required to be etale and surjective.

Searches performed through the prescribed wrapper:

- LeanFinder: "smooth curves of genus at least two with full abelian level
  structure have a separated finite type coarse moduli scheme". Eight hits,
  all ordinary scheme-morphism properties; no moduli theorem.
- Loogle: `"AbelianLevelModuli"`: zero hits.
- Mathlib grep: `AbelianLevelModuli|CoarseModuli|ModuliStack` in
  `AlgebraicGeometry`: zero hits.
- LeanSearch: "A Deligne Mumford stack is separated if its diagonal is proper
  and smooth of finite type if it has a finite type smooth atlas". Eight hits
  on scheme or topological separatedness and properness, no moduli-stack notion.
- Loogle: `"ModuliStack"`: zero hits.
- Mathlib grep: `ModuliStack|ProperModuliDiagonal|SmoothFiniteTypeAtlas` in
  `CategoryTheory`: zero hits. These last three complete outputs are copied
  verbatim into the new definition node's `mathlib_searches`.
- Project `rg` searches for `abelianLevel`, `coarse.Moduli`,
  `IsDeligneMumfordModuliStack`, `HasProperModuliDiagonal`, and
  `HasSmoothFiniteTypeAtlas`: upstream contains no matching theorem; Sheaf
  contains the reusable moduli definitions and the stable coarse theorem,
  but neither missing property predicate nor the abelian-level coarse theorem.
- DAG search and `tools/blueprint_refs.py search 'smooth separated finite type
  stack'`: zero blueprint matches. The DAG references these properties in
  statement nodes, but has no existing definition node for the two predicates.
  `tools/blueprint_refs.py ancestor` reports the item's ancestor as `None`,
  retained as JSON null in the new node's blueprint record.

No statement is disputed. There are no dependency repairs or statement changes.
Server `scompile.py` compiled both modules individually in dependency order,
including sandbox and library-module forms, with no errors or non-sorry warnings.

## New nodes

`def-sfb-moduli-stack-properties` supplies the missing atlas and proper-diagonal
predicates, with the precise formulations and source just explained. It has one
module with `CategoryTheory.HasSmoothFiniteTypeModuliAtlas` and
`CategoryTheory.HasProperModuliDiagonal`; both have real definitions using the
recorded groupoid and scheme APIs. The node cites field, scheme, groupoid,
smoothness, finite type, fibre product, and properness definitions. The three
wrapper searches are recorded verbatim in its JSON, and the project/DAG searches
are recorded above. The existing DM predicate supplies an atlas without the
smooth/finite-type structure-map conditions and an algebraic-space diagonal
without properness; it therefore supplies neither of these two missing notions.
The item gains this definition node as a statement dependency.

## Second reading by Q10

This is the worker's separate second pass over both modules and both node files;
the maintainer supplies the independent delivery review, as the dispatch brief
requires. No separate agent was started and no independent reader is claimed.

Rechecked every correspondence listed above against the files, especially the
level subtype, the very same `AbelianLevelModuli.forget` in each conjunct, the
quasi-compact atlas clause, the two diagonal-projection comparisons, and the
composition-induced coarse universal property. Checked that the new definitions
assert no existence for a particular groupoid by themselves, and that they
specialize to the source's meanings on DM stacks. The proper-diagonal test uses
`prod.lift p q` in the over category and compares both projections over identity
base arrows; this avoids weakening separatedness to properness of an unrelated
scheme. The theorem asserts coarse moduli and retains all stack properties,
without adding a fine-representability conclusion. No mismatch remained after
this reading. There is exactly one postponed theorem, matching the item node;
the definition module contains no `sorry`.
