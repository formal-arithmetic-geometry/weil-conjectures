## Worker report

The module `Sheaf.AlgebraicGeometry.StackUniversallyInjectivePointLift` states
`CategoryTheory.stack_universallyInjective_point_lift`, exactly the same-field lifting
assertion of Stacks Project, Morphisms of Stacks, Tag 0DTM
(`literature/stacks-project/stacks-morphisms.tex`, lemma-universally-injective-point,
statement and proof read). Its only theorem proof is `sorry`. The docstring gives all
six accepted DAG proof steps and names their dependencies.

The auxiliary definition `CategoryTheory.moduliFieldFiberPoint` is the canonical point
class of a fibre object, not another point equivalence relation: it applies `Quot.mk`
to the existing `ModuliFieldRelation`. The equality in `Functor.Fiber` supplies the
field-scheme isomorphism via `(Over.forget S).mapIso (eqToIso x.property)`. Its data
are explicit, with no choice and no postponed proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. Explicit universes `u v w`, with stack
  categories `BasedCategory.{max u v, max (u + 1) w} (Over S)`, implement the size
  convention and allow scheme-valued tests. The same bounds are used in the landed
  universal-injectivity criteria; arbitrary larger bounds are available through v,w.
- The stacks X,Y are categories over `Over S`, with hypotheses
  `hX : IsAlgebraicModuliStack X` and `hY : IsAlgebraicModuliStack Y`.
  This existing predicate includes étale stack descent, algebraic-space diagonal,
  and a representable smooth surjective scheme atlas, with smoothness tested on
  étale scheme charts. Neither stack is assumed DM, reduced, separated, finite type,
  nonempty, or defined over a field.
- The morphism over S is `f : BasedFunctor X Y`.
- Universal injectivity is written out as `hf`: for every algebraic stack Z and
  `g : BasedFunctor Z Y`, the point map of `moduliTwoFiberFst g f` is injective.
  The fibre product is ordered Z ×_Y X so that this existing first projection is
  exactly the projection to Z, canonically the same base change as X ×_Y Z → Z.
- The algebraically closed field is `(K : Type u) [Field K] [IsAlgClosed K]`.
  Its specified S-structure is `(a : Spec (.of K) ⟶ S)`.
- The given object is `y : Functor.Fiber Y.p (Over.mk a)`, retaining its actual
  field and S-structure rather than an arbitrary representative of its point.
- The image condition is `hy : moduliFieldFiberPoint a y ∈ Set.range (moduliPointMap f)`.
  `moduliPointMap` is the existing map on field-object quotient classes. This does
  not assume a lift over K, only membership of the underlying point in the image.
- The conclusion `∃ x : Functor.Fiber X.p (Over.mk a), Nonempty
  ((moduliFiberMap f (Over.mk a)).obj x ≅ y)` gives an actual object over the same
  specified `Spec K`, and an isomorphism to the given y in that fibre category.
  There is no extension-field existential, no uniqueness or faithfulness claim,
  and no requirement that an isomorphism be unique.
- The underlying point topology mentioned in the node does not occur in this
  set-theoretic image/injectivity assertion. Its point set is the existing quotient;
  there is no need to choose a topology or an atlas in this module.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, and `Over`; `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, used by
  the chartwise smooth-atlas predicate; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (all polynomials split, equivalent to the node's root formulation).
  The recorded `AlgebraicClosure` construction was also read in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`; no closure is chosen in the statement.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `IsModuliStack`,
  `HasAlgebraicSpaceDiagonal`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `moduliFiberMap`, and `SpaceMapIsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, `IsRepresentable`,
  `IsEtale`, and `IsSurjective`, as used in the stack predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.SpaceMapIsSmooth`, `IsSmoothModuliAtlas`,
  `IsAlgebraicModuliStack` (their full source signatures and docstrings were read).
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.ModuliFieldObject`, `ModuliFieldRelation`, `ModuliPoints`,
  `moduliFieldMap`, `moduliPointMap`. These definitions are polymorphic in based
  categories, with no DM hypothesis, so they apply to the algebraic stacks here.
- `Mathlib.CategoryTheory.FiberedCategory.Fiber`: `CategoryTheory.Functor.Fiber`
  and its category, whose morphisms lie over the identity on the specified base.

Added the already landed owning nodes `def-sfb-algebraic-moduli-stack` and
`def-sfb-dm-stack-morphism-properties` to stmt_deps, as authorized by brief-stage2 §5
(STMT_DEPS MAY GAIN LANDED NODES). Their interfaces already give the required notions;
there are no new nodes, dependency modules, or statement corrections. All existing
fields other than lean and these additions to stmt_deps remain unchanged.

Proof-only imports include every recorded proof-dependency module (Mathlib modules
for Mathlib matches). The three proof prerequisites with no current Lean attachment
are `lem-sfb-stack-locally-closed-finite-type-point`,
`lem-sfb-stack-diagonal-space-source-representability`, and
`lem-sfb-representable-stack-point-surjectivity`; they are not needed to type this
statement and are named in the proof docstring for subsequent proof work.

Edge cases checked before writing:

- Empty X: the point-image hypothesis is false, so no spurious existence claim.
- Empty Y or empty S: there is no input y or structural map a, as appropriate.
- Identity map: any y itself lifts, retaining its automorphisms.
- Open immersion: the image condition is essential and is retained.
- A gerbe over an algebraically closed field: the conclusion allows stabilizers and
  multiple isomorphisms; it does not assert a unique object or faithful fibre functor.
- Nonreduced, disconnected, non-Noetherian stacks and positive characteristic:
  no extra restriction is imposed. K need not be algebraic over a smaller field.
- An image witnessed only after a transcendental field extension is admitted by hy;
  the conclusion still uses precisely K, which is the substance of Tag 0DTM.
- Universal injectivity is tested on algebraic stacks, not only schemes or field
  objects. The universe maxima keep all scheme tests in the bound and agree with
  the existing `stack_universalInjectivity_criteria` interface.

Searches for an existing statement or notion (2026-10-24):

- `msearch.py ... leanfinder`: "A universally injective morphism of algebraic stacks
  lifts a geometric point in its image over the same algebraically closed field".
  Eight hits, all scheme results: `AlgebraicGeometry.UniversallyInjective`,
  `Scheme.Hom.injective`, `universallyInjective_eq_diagonal`, etc.; no stack lift.
- `msearch.py ... leansearch`: "A universally injective map of algebraic stacks
  lifts an algebraically closed field object in its topological image over the same
  field". Eight scheme-only hits; no matching stack statement.
- `msearch.py ... loogle`: `"UniversallyInjective", "IsAlgClosed"`: zero hits.
- `msearch.py ... grep`: `universally.injective.point|AlgebraicStack|ModuliPoints`
  in Mathlib/AlgebraicGeometry: zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `universally.injective.point`: only the source reference in
  `SpaceTwoFieldScalarAlgebraicity.lean`; that statement concerns scalar algebraicity,
  not lifting. Searches for `UniversallyInjective`, stack point maps, and algebraic
  stack predicates located the existing interfaces used above and the distinct
  `StackUniversalInjectivityCriteria.lean` theorem. No duplicate lift theorem.
- `rg` for fibre/field-to-point helper names in both project trees found no existing
  canonical `Functor.Fiber` to `ModuliPoints` helper; the one supplied here only
  packages the quotient constructor. Searches and reads of DAG records identified
  the owning definition nodes rather than introducing a duplicate definition node.

No STATEMENT-DISPUTED issue or node fault was found. The source agrees with the node.

## Second reading by Q110

The dispatcher explicitly prohibits starting other agents. This is a separate
in-thread rereading, not a claim of independent authorship; the maintainer's independent
review remains the independent check described in the assignment.

Reopened the node's statement alongside the final Lean signature and read the source
0DTM statement again. Checked S, algebraicity of both stacks, f over S, every-algebraic-
stack base-change injectivity, the algebraically closed K, its fixed S-structure a,
y in the strict fibre, and its underlying quotient-class image condition one by one.
The conclusion binds x in the fibre over that identical a and asks for an isomorphism
in Y's same fibre; it neither changes field nor replaces the groupoid by a set. In
particular, the use of `moduliTwoFiberFst g f` was checked against its definition:
it projects the Z-first product to Z. The helper was unfolded and its field-scheme
witness checked against the equality stored by `Functor.Fiber`; its point relation
is the existing one and carries no hidden theorem hypothesis. No statement mismatch
was found. The two added stmt_deps point at landed definitions already read in full.
No mathematical statement was changed during this reading.
