## Worker report

The module `Sheaf.AlgebraicGeometry.StackArtinianSmoothnessCriterion` states
`AlgebraicGeometry.StackDeformation.stack_artinian_smoothness_criterion`, with
`sorry` as its sole proof. It introduces no definitions. The source is
`literature/stacks-project/stacks-geometry.tex`, Situation `situation-versal`,
`lemma-versal-ring` (0DQX), and `lemma-characterize-smoothness` (0DZS), specifically
(1) iff (3). I read the source statement and proof, including its finite-residue
extension reduction and comparison with the completion of an atlas local ring.

Hypotheses and clauses, in node order:

- Schemes and their maps are Mathlib `Scheme` and `Scheme.Hom`; `Spec (.of R)` and
  `Spec.map` are the recorded affine-spectrum construction. The module imports
  `Sheaf.AlgebraicGeometry.AlgebraicSpace` and uses its algebraic spaces through
  the recorded stack definitions. Explicit `universe u v w`, rings in `Type u`,
  schemes in `Scheme.{u}`, and `BasedCategory.{v,w}` implement the size convention.
- The category over schemes is `F : BasedCategory.{v,w} (Over (Spec (.of R)))`.
  `hF : IsAlgebraicModuliStack F` supplies fibred groupoids, effective etale
  descent, algebraic-space diagonal, and a smooth surjective scheme atlas.
  In the defining source, `IsModuliStack` includes the fibred condition;
  `HasAlgebraicSpaceDiagonal` uses actual 2-fibre products; `IsSmoothModuliAtlas`
  retains their projections and checks smoothness on etale scheme charts.
- The convention for smoothness is the existing `IsSmoothModuliStack`, with
  Mathlib `Smooth` on a scheme atlas. `Flat` and `LocallyOfFinitePresentation`
  are imported from their recorded Mathlib modules; the node's introductory
  conventions impose no separate flatness or finite-presentation assumption.
- The coefficient ring hypotheses are `[CommRing R] [IsLocalRing R]
  [IsNoetherianRing R]`. The specified residue field is `[Field k] [Algebra R k]`
  together with `residueEquiv : IsLocalRing.ResidueField R ≃ₐ[R] k`.
  This is a specified residue-field identification compatible with the base
  map, and permits every isomorphic realization of R/m_R. It is not an added
  field-extension or finite-type assumption.
- The stack is locally of finite type by `hft`: there exist `U` and `a` with
  `IsSmoothModuliAtlas F U a ∧ LocallyOfFiniteType U.hom`. No quasi-compactness,
  global finite type, or extra choice of a chart is required.
- The fixed residue-field point is
  `x : Functor.Fiber F.p (affine (CommAlgCat.of R k))`. The `affine` construction
  uses the structural map given by the R-algebra k, which the residue equivalence
  identifies with the residue map. Thus x lies over exactly that base map.
- Artinian local R-algebras with residue marking are precisely
  `ArtinDeformation.TestCategory R k`. Its `IsTestAlgebra` requires locality,
  `IsArtinianRing`, a surjective augmentation to k, and maximal kernel.
  Its arrows preserve the augmentation and hence induce the identity on k.
  Their local nature follows from the maximal kernels. The structure R -> A
  is local too: the inverse image of the augmentation kernel is the kernel of
  R -> k, namely m_R by `residueEquiv`.
- The groupoid F_x(A) is the existing `Marked F x A`. Its objects are cartesian
  arrows x -> xi over Spec k -> Spec A. In a fibred groupoid these specify
  exactly xi with an identification of its reduction with x. Its morphisms
  belong to the fibre and commute with that marking. No isomorphism-class
  quotient is substituted for this groupoid.
- The left side is `∃ U : OpenModuliSubstack F, IsSmoothModuliStack U.category ∧
  (∀ V : OpenModuliSubstack F, IsSmoothModuliStack V.category → V.IsContainedIn U)
  ∧ U.property x.val`. It says that a largest smooth full open substack exists
  and x belongs to it. `IsContainedIn` is implication of object predicates.
  Since existence of the largest smooth open is guaranteed for algebraic stacks
  by the node's proof dependency, this is exactly factoring through that open,
  without an arbitrary choice or an extra hypothesis about a chosen open.
- The equivalence is Lean `↔`. On the right, `∀ (A' A : TestCategory R k)
  (q : A' ⟶ A), Function.Surjective (ArtinDeformation.map q) → ...` includes
  every indicated surjection, not just small or square-zero extensions.
- `∀ Y : Marked F x A, ∃ Y' : Marked F x A', PullsBack F x q Y' Y` is the
  marked lifting conclusion. `PullsBack` gives an arrow from Y over A to Y'
  over A' above Spec q with equality of the composite marking. Every arrow
  is cartesian in the fibred groupoid. Consequently it is exactly an
  isomorphism between Y' restricted to A and Y, respecting both markings.

Dependency declarations used (their complete signatures and docstrings were
read in the recorded modules):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsAlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: `IsLocalRing.ResidueField`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `IsSmoothModuliStack`, `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`,
  `OpenModuliSubstack.category`, `OpenModuliSubstack.IsContainedIn`.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`:
  `ArtinDeformation.TestCategory`, `IsTestAlgebra`, `map`.
- `Sheaf.AlgebraicGeometry.MarkedStackDeformations`:
  `StackDeformation.affine`, `Marked`, `PullsBack`.
- Proof-only import `Sheaf.RingTheory.AdicFormalSmoothnessDescent` supplies
  `Algebra.formallySmoothAdic_iff_of_smoothCompleteLocalMap`. The other six proof
  dependencies have no Lean records in the read base, so their modules cannot
  yet be imported. Their mathematical steps are reproduced in the theorem
  docstring, with each node id. They introduce no missing notion in this statement.

The four landed definition nodes for stacks, open substacks, Artinian tests, and
marked deformations were added to `stmt_deps`. No existing dependency record was
changed and no new node was needed. No statement correction or dispute was found.

Edge cases checked before writing:

- An empty stack has no x over Spec k, so it does not create a vacuous smooth-point
  assertion. A zero ring cannot satisfy the residue-field hypotheses.
- If R is already a field, any specified R-residue isomorphism is allowed. Neither
  completeness of R nor perfection or separability of k is assumed.
- A = k and identity surjections are included. A marking has a unique compatible
  arrow to any other marked copy of x, even when x has automorphisms. The lifting
  statement asks only for existence, not uniqueness of objects or arrows.
- All surjections of Artinian tests are included, with unrestricted nilpotence
  length. Only asking for small extensions would require a separate equivalence;
  the Lean does not make that replacement.
- Disconnected stacks and atlases, non-quasi-compact stacks, and all
  characteristics are allowed. Smoothness is local on the atlas as in the source.
- Test algebras live in the same universe as R and k, not an independently smaller
  universe. Stack object and arrow universes remain independent.

Searches made:

- `msearch.py ... leanfinder "An algebraic stack is smooth at a residue field point
  if and only if its marked Artinian deformations lift across all surjections"`:
  eight hits, all scheme/ring smoothness; no algebraic-stack criterion.
- `msearch.py ... loogle "AlgebraicStack, CategoryTheory.IsStack, IsArtinianRing"`:
  no hits; unknown identifier AlgebraicStack.
- `msearch.py ... grep "AlgebraicStack|IsAlgebraicStack|Artinian.*[Dd]eformation"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Algebraic stack smooth point marked Artinian
  deformations surjections"`: eight hits, on ring or scheme formal smoothness;
  none is the stack criterion.
- `rg -n` for algebraic-stack, marked-deformation, smooth-locus and finite-type
  names in `lean/Sheaf` located the four reused definition modules and the
  existing finite-residue versal-ring statement, whose atlas hypothesis provides
  the same local finite-type interface. No existing statement gives this iff.
- Searches of `lean/WeilConjectures` for the item id and for stack smooth-locus
  names found no matching statement; the smooth-locus results concern schemes.
- A declaration-name search for `stack_artinian_smoothness_criterion` in Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf` found no collision.
- DAG definition nodes and their Lean records were read for all notions reused.
  No repair note for this item was present in `coord/repair-notes`.

Validation: the required `scompile.py O4 lem-sfb-stack-artinian-smoothness-criterion`
accepted the statement at its sandbox and library module names with no diagnostics.
The subsequent delivery dry run recompiles the final file including the explicit
algebraic-space import. Expected `sorry` is the only postponed proof in this delivery.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
