## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFiniteAlgebraSurjectiveFpColimit` states
`AlgebraicGeometry.AlgebraicSpace.exists_finite_finitePresentation_surjective_colimit`.
Its sole theorem has proof `sorry`; there are no new definitions or auxiliary theorems.
The statement agrees with Stacks Project, Limits of Spaces, Tag 086Z,
`lemma-finite-algebra-directed-colimit-finite-finitely-presented`, read in
`literature/stacks-project/spaces-limits.tex`, including the definition of a finite
quasi-coherent algebra immediately preceding it. The source proof and all eight
reviewed DAG proof steps are included in the declaration docstring as a proof plan.

Hypotheses and clauses, in node order:

- The scheme S and algebraic space Y over S are `{S : Scheme.{u}}` and
  `(Y : AlgebraicSpace S)`. All universes are explicit; `autoImplicit` is false.
  The small etale site has the existing object universe u+1 and section universe u.
- Quasi-compactness is `[CompactSpace (Point Y.obj.obj)]`, using the recorded
  field-point quotient and its final etale-chart topology. No separatedness of S
  and no Noetherian hypothesis are imposed.
- Absolute quasi-separatedness is `(hqs : IsAbsolutelyQuasiSeparated Y)`, the
  existing affine-test criterion for the absolute diagonal. This is not an extra
  relative diagonal hypothesis.
- A commutative O_Y-algebra sheaf with quasi-coherent underlying module is
  `(A : Y.QCAlg)`. This is the existing full subcategory of the under category of
  the commutative structure sheaf, with predicate `A.toModule.IsQuasicoherent`.
  Bundling the sheaf and its quasi-coherence changes none of the quantified objects.
- Finiteness is `(hA : A.obj.IsFinite)`. Unfolding the existing predicate gives, for
  every U in `Y.EtaleSite` with `IsAffine (Y.etaleForget.obj U)`, finiteness of
  `(A.obj.hom.hom.app (op U)).hom`. `RingHom.Finite` is module finiteness for the
  algebra structure induced by that same structure ring map.
- The small nonempty directed set is existential `(I : Type u) (_ : Preorder I)
  (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))`. This follows the project's directed
  set convention, with index universe tied to the section-ring universe.
- The algebras A_i and their transition maps are `(D : I ⥤ Y.QCAlg)` and
  `D.map (homOfLE h)` for `h : i ≤ j`. Being objects and arrows of QCAlg supplies
  quasi-coherence, commutative algebra structures and algebra morphisms. Functor
  laws supply precisely the identity and composition laws for these transitions.
- For every i, finiteness and algebra finite presentation are
  `(D.obj i).obj.IsFinite ∧ (D.obj i).obj.IsFinitePresentation`. Both existing
  predicates quantify over every affine etale chart. The second uses
  `RingHom.FinitePresentation`, hence `Algebra.FinitePresentation`, whose data are
  a surjection from `MvPolynomial (Fin n) R` with finitely generated kernel.
  This is exactly a finite polynomial algebra presentation with finitely many
  relations; it is not `Module.FinitePresentation`.
- Every transition is surjective on each affine etale chart: the second conjunct
  quantifies over `i j`, `h : i ≤ j`, and `U : Y.EtaleSite`, assumes the chart is
  affine, and asserts `Function.Surjective` of
  `((D.map (homOfLE h)).hom.right.hom.app (op U))`.
  Here `.hom` forgets the full-subcategory predicate, `.right` is the map of
  algebra ring sheaves, and `.hom.app` is its section ring map. This states
  sectionwise surjectivity, rather than only an abstract categorical epimorphism.
- The compatible algebra maps to A are `ι : D ⟶ (Functor.const I).obj A`.
  Naturality is exactly `alpha_j ∘ alpha_ji = alpha_i`.
- The last clause `Nonempty (IsColimit (Cocone.mk A ι))` states existence of the
  universal factorization from the specified vertex A for every QCAlg cocone.
  `IsColimit.desc`, `.fac`, and `.uniq` render respectively the algebra map to any
  quasi-coherent B, compatibility with every cocone leg, and its uniqueness.
  The colimit category is QCAlg, exactly as in this node.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme
  morphisms. Their definitions and docstrings were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `etaleForget`, and the structure sheaf.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace` on the recorded `Point`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh` and its specialized sheafification
  instances for the same Mathlib `SheafOfModules.IsQuasicoherent` predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra`: `QCAlg`,
  `CommAlgebraSheaf`, `.toModule`, `.IsFinite`, and `.IsFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, their natural
  transformation data and factorization fields; `Functor`, `homOfLE` and
  `IsDirected` provide the directed diagram. The size convention is metatheoretic
  and has no module to import.

The two already landed definition nodes `def-sfb-space-quasi-coherent-algebra`
and `def-sfb-space-absolute-quasi-separated` are added to `stmt_deps` so that
these existing notions are cited directly. No new node, dependency repair,
statement correction or other field change is needed.

Every stated proof dependency is imported privately: affine etale covering,
finite affine subatlas, module finite-presentation approximation, affine-chart
calculus, symmetric-algebra finite presentation and finite-algebra integrality.
The last uses the existing Mathlib match `Algebra.IsIntegral.of_finite` from
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`. Their node records, source
signatures and proof docstrings were read. No dependency is copied or restated.

Edge cases checked before writing: the empty algebraic space is allowed; its
chart section modules are zero, and the index set is still nonempty. Zero
algebras are allowed since there is no nontriviality assumption. Finite
polynomial presentations allow zero variables and zero relations; a degree-zero
monic relation is permitted and forces the zero algebra. A zero kernel and an
already finitely presented algebra admit a singleton constant system. Identity
transitions are included by the quantifier `i ≤ j`. Arbitrary directed
preorders, all characteristics, non-Noetherian rings and non-quasi-separated
base schemes are not excluded. No assertion of flatness, freeness, finite rank,
or module finite presentation was added. The nonreduced finite algebra
R[x]/(x^2) is included. No statement dispute was found.

Searches performed through `batch2/msearch.py` (raw outputs are retained in
`searches.jsonl` in the worker sandbox):

- LeanFinder: `Finite quasi coherent algebra on qcqs algebraic space is a directed
  colimit of finite finitely presented algebras with surjective transitions`.
  Eight hits on scheme finiteness, module finite presentations and affine limits;
  none states the algebraic-space theorem.
- Loogle: `Algebra.FinitePresentation, Module.Finite`. Four hits on finite-module
  presentation, cotangent modules and free surjections. None supplies a directed
  algebraic-space approximation with surjective transitions.
- Mathlib grep: `surjective.*colimit|colimit.*surjective|finite.*finitely.*presented`
  in `AlgebraicGeometry`. Seven hits on scheme gluing, affine limits and flat rank;
  none is this theorem.
- LeanSearch: `A finite quasi coherent algebra on a quasi compact quasi separated
  algebraic space is a directed colimit of finite finitely presented algebras with
  surjective transition maps`. Eight hits on algebra or module finite-presentation
  definitions; no approximation theorem.
- Local ripgrep in `lean/WeilConjectures`, `lean/Sheaf/AlgebraicGeometry` and
  Mathlib, using finite/colimit/surjective patterns and the exact item id and
  proposed declaration name. No same declaration exists. Scheme-only integral
  algebra approximation has a different category and no matching transition
  surjectivity clause. The space relative-Spec approximation consumer mentions
  this node only in its proof plan. The existing algebraic-space QCAlg and
  absolute quasi-separatedness definitions above were found and reused.

Validation: `scompile.py NJ lem-sfb-space-finite-algebra-surjective-fp-colimit
<module-path>` compiled both its sandbox and library contexts cleanly (1.7 s and
1.5 s), with no errors or warnings.

## Second reading by NJ

This is the worker's separate second pass over the finished node copy and Lean
module; the maintainer supplies the independent review after delivery. The
scheme, algebraic space, compact point space, absolute affine-test separation,
quasi-coherent commutative algebra and module-finiteness hypotheses match the
node in the order listed above. The existential diagram carries all identity,
composition and compatibility laws. Each stage has both chartwise finite-module
and finite-algebra-presentation properties. Surjectivity is quantified over all
transition inequalities and all affine etale charts, and is applied to the
actual section map of that transition. The colimit is in QCAlg with A as its
vertex, not in a different category or with an arbitrary isomorphic vertex.
No clause is lost or strengthened. The two reused definition nodes were added
to `stmt_deps`; the statement and proof split were preserved. No mismatch
requiring a change was found in this pass.
