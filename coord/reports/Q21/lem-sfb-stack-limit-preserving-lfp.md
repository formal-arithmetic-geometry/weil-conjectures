## Worker report

The module `Sheaf.AlgebraicGeometry.StackLimitPreservingLfp` states
`CategoryTheory.locallyOfFinitePresentation_iff_isLimitPreserving`. Its sole theorem
has proof `sorry`; there are no definitions or auxiliary theorem obligations.
The node statement, proof and proof dependencies are unchanged. The only node changes
are its Lean record and adding the two already landed definition nodes
`def-sfb-algebraic-moduli-stack` and `def-sfb-fibred-groupoid-limit-preserving` to
`stmt_deps`, as permitted by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES).
No new nodes and no dependency repairs are needed.

I read Stacks `stacks-limits.tex`, the full lemma
`lemma-locally-finite-presentation-limit-preserving` (0CMX) and proposition
`proposition-characterize-locally-finite-presentation` (0CMY), including their
proofs. The theorem is precisely 0CMY for the structural morphism to a scheme.
The forward implication's docstring follows all five node proof steps, including
finite coverings, affine pair/triple overlaps, source/target equations, cocycle
and arrow-compatibility equations, and eventual equality.

Hypothesis and clause correspondence:

- The arbitrary scheme S is `{S : Scheme.{u}}`. Schemes and their morphisms use
  Mathlib's recorded `AlgebraicGeometry.Scheme` and `Scheme.Hom` (def-pc-scheme).
- The category over S-schemes is `(F : BasedCategory.{v, w} (Over S))`.
  `hF : IsAlgebraicModuliStack F` is exactly the algebraic-stack assumption.
  Expanding the existing definition gives `IsModuliStack F`,
  `HasAlgebraicSpaceDiagonal F`, and an existential smooth surjective scheme atlas.
  `IsModuliStack` includes `IsFibredInGroupoids` (cartesian lifts and every arrow
  strongly cartesian), and effective étale descent with unique gluing of arrows.
  Thus fibres are groupoids; no coarse isomorphism-class replacement occurs.
- Diagonal representability is the existing algebraic-space representation of
  every two-scheme 2-fibre product. The atlas uses `HasSpaceBaseChange`, which
  specifies an equivalence over the actual test scheme and the actual projection.
  `SpaceMapIsSmooth` tests scheme smoothness on étale charts, and
  `SpaceMapIsSurjective` tests covering of all target points by those charts.
  These definitions use `AlgebraicGeometry.AlgebraicSpace`, the recorded
  fppf-sheaf/representable-diagonal/étale-atlas notion of def-trf-algebraic-space.
- Local finite presentation of F over S is exactly the left side:
  `∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
  IsSmoothModuliAtlas F U a ∧ LocallyOfFinitePresentation U.hom`.
  The structural morphism of the smooth atlas, not the atlas morphism itself,
  is required locally finitely presented. This is the same atlas formulation
  used by `StackInfinitesimalSmoothCriterion` and `RepresentableSourceAlgebraic`.
  No extra quasi-compactness, quasi-separatedness, separatedness, or finite type
  condition is imposed on the stack or on S.
- The iff is Lean `↔`; its right side is the existing general-base predicate
  `FibredGroupoidLimit.IsLimitPreserving F`.
- Every small directed inverse system is quantified in that predicate as
  `(I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`,
  `(D : Iᵒᵖ ⥤ Over S) (c : Cone D)`. All stage schemes are affine;
  `Nonempty (IsLimit c)` is the actual limit universal property.
  Transitions are S-morphisms between affine schemes and hence affine.
  The affine limit assumption in the existing predicate excludes no system:
  inverse limits of affine schemes are affine. Nonempty directed indices are
  the Stacks convention, not arbitrary empty diagrams.
- Essential surjectivity is `FibredGroupoidLimit.ObjectsDescend F`:
  every object in `Functor.Fiber F.p c.pt` has a stage object and an arrow over
  the cone projection. Since all arrows are cartesian this gives the required
  isomorphism to its pullback.
- Fullness is `FibredGroupoidLimit.ArrowsDescend F`: starting from specified
  pullback identifications for two objects at the same stage, an arbitrary fibre
  arrow at the limit has a common later-stage arrow. The two factorization
  equations preserve the given identifications, and the last square identifies
  the actual limit arrow. For objects initially at different stages, directedness
  and cartesian pullback supply a common stage, exactly as in the node's wording.
- Faithfulness is `FibredGroupoidLimit.ArrowEqualitiesDescend F`: if two actual
  stage arrows agree after a specified limit lift, there is a later-stage lift
  on which they agree. No equality of merely isomorphism classes is used.
- The size convention is explicit universes `u v w`; the index universe is `u`,
  matching the scheme universe. Object and morphism universes of the total
  category remain independent, with no additional equality assumption.
- The statement's explanatory vocabulary about open substacks, flatness and
  chartwise properties gives no extra hypothesis or conclusion for this theorem.
  The used smooth and locally-finitely-presented properties are the recorded
  Mathlib classes; the recorded Flat module is imported as well. No new definition
  of these notions or of open substacks is introduced.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` (publicly imported by
  the preceding module): `IsFibredInGroupoids`, `IsModuliStack`,
  `HasAlgebraicSpaceDiagonal`, `HasSpaceBaseChange`, `SpaceMapIsSurjective`,
  `discreteModuli`, and Mathlib's `BasedCategory`/`BasedFunctor`.
- `Sheaf.AlgebraicGeometry.FibredGroupoidLimitPreserving`: its full seven-declaration
  interface was read, including all three descent predicates and their conjunction.
- The size-convention node is explicitly a convention record with no declaration.

Proof dependencies already stated are imported without `public`:
`Mathlib.AlgebraicGeometry.Sites.Fpqc` (`Scheme.fppfTopology`),
`Sheaf.AlgebraicGeometry.FppfAffineRefinement`
(`Scheme.exists_finite_fppf_affine_open_refinement`),
`Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent`
(`isFppfModuliStack_of_etale_smooth_atlas`), and
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`
(`stack_chartwise_smooth_etale_calculus` and its companion clauses).
Their signatures/docstrings were read. The other four proof dependencies
`lem-sfb-lfp-space-scheme-limit-test`, `lem-sfb-representable-lfp-object-limit-test`,
`lem-sfb-smooth-space-cover-etale-sections`, and
`lem-sfb-standard-fppf-cover-limit-descent` have no recorded Lean declaration in
this checkout and are not needed to type this statement; they remain named in
its proof docstring and DAG proof plan, with no invented modules or imports.

Edge cases checked before writing: arbitrary nonaffine base S; singleton and
non-antisymmetric directed preorders; nonempty directed systems whose affine
limit is empty (e.g. zero ring limit); empty schemes and the empty stack (the
empty scheme is an allowed atlas); nontrivial automorphisms and distinct arrows
which become equal later; unbounded/non-quasi-compact stacks; independent total
object/morphism universes. No finite-presentation assumption is made on the
stage structural maps. No hypothesis is hollow. No statement correction or
STATEMENT-DISPUTED issue was found.

Searches actually run (2026-10-24):

- msearch leanfinder, `An algebraic stack over a scheme is locally of finite
  presentation if and only if its groupoid valued functor preserves directed
  limits of affine schemes`: eight hits, all scheme finite-presentation
  definitions/lemmas, no algebraic-stack theorem.
- msearch leanfinder, `Algebraic stack locally of finite presentation limit
  preserving groupoids`: eight hits, again scheme morphism results only.
- msearch loogle, `AlgebraicGeometry.LocallyOfFinitePresentation,
  CategoryTheory.BasedCategory`: zero hits (run twice).
- msearch grep, `AlgebraicStack|IsAlgebraicStack|LimitPreserving`: zero Mathlib
  hits (run twice).
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf/AlgebraicGeometry` for
  `IsAlgebraicModuliStack|IsSmoothModuliAtlas|LimitPreserv|[Ll]imit.*[Mm]oduli|[Mm]oduli.*[Ll]imit`
  found the existing stack and general-base limit-preservation definitions,
  plus Artin predicates over special bases; no copy of this iff theorem.
- Direct rg of `lem-sfb-stack-limit-preserving-lfp` in `lean/WeilConjectures`
  returned no hits. Direct rg for both candidate theorem names in Mathlib,
  `lean/Sheaf`, `lean/WeilConjectures`, and `dag/lean_names_upstream.json`
  returned no hits.
- A structured read of DAG Lean records identified exactly the existing owners
  `def-sfb-algebraic-moduli-stack` and `def-sfb-fibred-groupoid-limit-preserving`.
  Their definitions are reused, not duplicated.

Validation: prescribed `scompile.py Q21 lem-sfb-stack-limit-preserving-lfp` compiled
both the sandbox probe and the library module cleanly (3.4 s and 3.0 s), with no
warnings or errors. `set_option autoImplicit false` and explicit universes enforce
that all variables are bound. Independent review is left to the maintainer as
specified by the dispatch brief; no worker second reading is claimed.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
