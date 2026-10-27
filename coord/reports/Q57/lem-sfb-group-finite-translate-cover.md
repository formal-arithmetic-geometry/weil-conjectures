## Worker report

The module `Sheaf.AlgebraicGeometry.GroupFiniteTranslateCover` states
`AlgebraicGeometry.AlgebraicSpace.exists_etale_finite_left_translate_cover`, with
one `sorry` and no definitions or proved theorems. It states the dispatched node
without changing its mathematical statement or proof plan. The only additional
statement dependency is the already landed definition node
`def-sfb-smooth-integral-group-space`, whose geometry predicates do not require
its separate `CommutativeSpaceGroup` structure. No new definition or dependency
repair is needed.

Source read: Deligne, *Le lemme de Gabber*, Astérisque 127 (1985), Lemma 4.6,
printed p.144, including the immediately preceding Lemma 4.5 on p.143.
The primary PDF is https://www.numdam.org/item/AST_1985__127__131_0.pdf.
The proof of 4.6 chooses a tuple outside the closure of the constructible bad
locus, after arithmetic approximation, and obtains the finite translate cover.
The delivered theorem is the group-space input isolated by the node, rather than
the Picard schematicness statement that is the heading of Deligne's lemma.
The current blueprint was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`:
`sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3). Its text uses proper
and open direct images plus compactification; the auxiliary Deligne provenance
is the node's inherited route, not a new claim about that blueprint paragraph.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| A locally Noetherian base scheme S | `{S : Scheme.{u}} [IsLocallyNoetherian S]` |
| A group algebraic space G over S; no schematicness assumption | `G : AlgebraicSpace S`, the existing full subcategory of fppf sheaves |
| Multiplication, inverse and identity over S satisfying the group identities | `[GrpObj G.obj.obj]`, using the pointwise cartesian structure of the presheaf category; its multiplication is a natural transformation, identity has terminal source, and inverse is a natural endomorphism |
| No commutativity | There is no `IsCommMonObj` or `CommutativeSpaceGroup` assumption |
| Smoothness on etale scheme charts | The first conjunct of `hG : IsSmoothIntegralGroupSpace G` is `MapIsLocally (@Smooth) (groupSpaceProjection G)` |
| Separatedness as closed relative diagonal | The second conjunct of `hG` is `MapIsSeparated (groupSpaceProjection G)`, whose definition is representability of that diagonal by closed immersions |
| Locally of finite presentation on etale scheme charts | The third conjunct of `hG` is `MapIsLocallyOfFinitePresentation (groupSpaceProjection G)` |
| Finite presentation additionally requires quasi-compactness and quasi-separatedness | The fourth and fifth conjuncts of `hG` are `MapIsQuasiCompact` for the structure map and its relative diagonal |
| Integral geometric fibres, including nonemptiness | The sixth conjunct is `GroupSpaceIntegralFibres G`: every algebraically closed field fibre has `IrreducibleSpace` on its existing point topology (which includes nonemptiness), and all representable etale scheme charts are reduced |
| Open subspace V, possibly not a scheme | `V : OpenSubspace G`, an existing subfunctor with inclusion representable by open immersions |
| V is quasi-compact | `hVqc : CompactSpace (Point V.val.toFunctor)` is compactness of its underlying algebraic-space point topology |
| V meets every geometric fibre | `hV` quantifies over each algebraically closed field K and `s : Spec (.of K) ⟶ S` and asserts `Nonempty (V.val.obj (op (Over.mk s)))` |
| An etale family of schemes over S | Existential `I : Type (u + 1)` and `T : I → Over S`, with `∀ a, Etale (T a).hom` |
| The family is jointly surjective | `∀ s : S, ∃ (a : I) (t : (T a).left), (T a).hom.base t = s` |
| Finitely many actual sections over each family member | For each a, `∃ (n : ℕ) (g : Fin n → (yoneda.obj (T a) ⟶ G.obj.obj))`; Yoneda identifies these natural transformations with G(T a) |
| The translates cover all of G after that base change | For every algebraically closed field K, `s : Spec (.of K) ⟶ (T a).left`, and section x over that geometric test, some j and section v of V satisfy `(yoneda.map (Over.homMk s rfl) ≫ g j) * (v ≫ V.val.ι) = x` |
| The translate is left multiplication, with the specified inverse | In that equation the restricted g is the left factor. `Hom.group`, induced by `GrpObj`, gives actual group multiplication and inverse; left multiplication by the inverse reverses this operation by the group identities |
| Empty base may have empty covering family | Neither I nor S has a nonemptiness assumption; the existential admits an empty I |

Why the two geometric-point formulations are exact: V is an open subspace of a
finitely presented space, so its fibre over an algebraically closed field is
locally of finite type. Such a fibre is nonempty exactly when it has a rational
point: take a nonempty etale scheme chart and a finite-type affine open in it;
a closed point has residue field K. Thus `hV` says precisely that V meets each
geometric fibre. In the conclusion, the pullback of V and each of its translates
are open subspaces of G over T a. They cover if and only if every geometric point
belongs to one of them. The displayed formula is membership in the actual image
of left translation; it does not assert a global factorization on arbitrary
non-geometric test schemes. The chosen x ranges over every geometric point of the
base change, not just residue-field rational points on a base fibre.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, and the underlying fppf sheaf/presheaf interface.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, used
  through the existing chartwise geometry predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, likewise through that predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` for the
  conclusion, distinct from the presheaf predicate `AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`:
  `AlgebraicGeometry.AlgebraicSpace.OpenSubspace`.
- `Sheaf.AlgebraicGeometry.RegularGroupSpace` (landed definition node added to
  `stmt_deps`): `groupSpaceProjection`, `IsSmoothIntegralGroupSpace`,
  `GroupSpaceIntegralFibres`; its module and all these full definitions were read,
  including the current server source through `scompile.py --source`.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory` supplies the pointwise
  cartesian structure; `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` supplies
  `CategoryTheory.GrpObj` and `CategoryTheory.Hom.group`. Their definitions show
  that the law used in the conclusion is the same supplied group law.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus` is a plain import
  for the already stated proof dependency. The four other proof dependencies
  have no Lean record in the read repository and are left for their own stage-2
  items; none is needed to state this theorem. No import cycle is introduced.

Edge cases checked before drafting:

- Empty S: choose empty I; all family and covering assertions are vacuous, with no
  nonempty-base restriction introduced by the group-object structure.
- Nonempty S, trivial or zero-dimensional integral geometric fibres: a fibre is a
  point, and meeting it forces V to contain that point; one translate suffices.
- V = G, when G is quasi-compact: take the identity section as the single translate.
- V empty on nonempty S: `hV` correctly fails, since S has a geometric point.
- A noncommutative smooth connected group, e.g. GL2: there is no commutativity
  binder; g times v is in that order, with inverse left translation by g inverse.
- n = 0 is allowed syntactically; on a nonempty covering member it cannot satisfy
  the geometric cover clause because the group identity supplies a geometric point.
- Arbitrarily large base in universe u: all fields and schemes use the same u,
  with the family index in the scheme-object universe u+1. No separate smaller
  field universe or nonempty index-type hypothesis is imposed.

Searches (all through the prescribed wrapper or read-only rg):

- LeanFinder: "A smooth separated finitely presented group algebraic space with
  integral geometric fibres is etale locally covered by finitely many translates
  of a quasi compact open meeting every fibre". Eight hits, including scheme
  smoothness/etale predicates, etale loci and standard smooth presentations; no
  relative algebraic-space finite-translate statement.
- LeanSearch: "A smooth separated finitely presented group algebraic space is
  etale locally covered by finitely many translates of any quasi compact open
  meeting every integral geometric fibre". Eight hits, including smoothness implies
  local finite presentation and ring smooth/etale results; no exact statement.
- Loogle: `"translate", "cover"`. Only
  `compact_covered_by_add_left_translates` and
  `compact_covered_by_mul_left_translates`. Their signatures were read in
  `Mathlib/Topology/Algebra/Group/Basic.lean`: these are ordinary topological groups,
  not relative algebraic-space group objects or etale-local sections.
- Wrapper grep: `translate.*cover|cover.*translate|AlgebraicSpace`. Sixteen returned
  hits concern ordinary topological group translates, measure and approximate groups.
- `rg -n 'translate.*cover|finite.*translate|finite_left_translate_cover|GroupSpaceIntegralFibres|IsSmoothIntegralGroupSpace' lean/WeilConjectures`
  and the corresponding Sheaf search for finite translates. The upstream Picard
  scheme module contains `exists_mul_mem_picardFunctorInvertibleDirectImage`,
  whose full signature is a special Picard-functor twist over a separably closed
  field and is not this theorem. `GroupNeutralComponentTranslates` concerns the
  components of a finite-type group scheme over an algebraically closed field,
  again not a relative arbitrary-open translate cover. These candidates were read.
- `rg -n 'lem-sfb-group-finite-translate-cover' lean/WeilConjectures`: no match.
  `dag/lean_names_upstream.json` also has no delivered theorem name.
- Further definition searches found `RegularGroupSpace.lean`; its existing
  geometry predicates are reused. The separate commutative structure in that
  module is deliberately not assumed. Thus no duplicate notion is introduced.
- LeanSearch: "Group objects in presheaves, with natural multiplication, inverse
  and identity" found `GrpObj`, `GrpObj.ofRepresentableBy`, `Hom.group` and related
  group-valued presheaf interfaces. The actual Mathlib definitions were read.

No statement fault, correction, or STATEMENT-DISPUTED issue was found. The example
module `Sheaf.CategoryTheory.CompactObject` is currently withdrawn and contains no
declarations; its node record was nevertheless read, and this file follows the
current module-mode, public-import, exposed-section and source-docstring conventions.

Validation: `scompile.py Q57 lem-sfb-group-finite-translate-cover` compiled the sole
module in sandbox mode (35.2 s) and library mode (11.5 s), with no errors or
unexpected warnings. The theorem proof is exactly `by sorry`. The source and JSON
signature were checked directly, and only the sandbox was written.

## Second reading by Q57

This is a second author pass; the maintainer supplies the independent review, as
specified in the dispatcher brief. I reopened the item, the actual theorem signature
and the full reused definitions. The six clauses of `IsSmoothIntegralGroupSpace`
match smoothness, separatedness, local finite presentation, quasi-compactness,
quasi-separatedness and integral fibres in that order. `GrpObj` has no commutative
axiom. The subfunctor inclusion and the NatTrans multiplication in the final equation
are the actual open inclusion and group law. The geometric test has a map to the
chosen T a, so it ranges over the whole base-changed group. A section of V over the
same test is precisely a point of the pullback V there. I checked that no claim of
surjectivity on all arbitrary-scheme sections was substituted for an open cover.
The field nonemptiness hypothesis agrees with meeting each fibre by the locally
finite-type argument above. All group operations, fields, universes, n and the family
index are bound explicitly, and empty I is permitted. No mismatch was found and no
source correction or helper module was added. The already landed geometry-definition
node was added to the item's statement dependencies so this reuse is recorded.
