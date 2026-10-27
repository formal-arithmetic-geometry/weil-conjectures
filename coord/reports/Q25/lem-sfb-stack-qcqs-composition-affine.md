## Worker report

The module `Sheaf.AlgebraicGeometry.StackQcqsCompositionAffine` states the two clauses
of `lem-sfb-stack-qcqs-composition-affine`, with only `sorry` proofs and no new definitions.
Its declarations are `CategoryTheory.algebraicModuliMap_qcqs_comp` and
`CategoryTheory.algebraicModuliMap_qcqs_of_affine`.

Clause-by-clause correspondence:

- The field is `{k : Type u} [Field k]`. Every stack is a `BasedCategory` over
  `Over (Spec (.of k))`, so every morphism is over the given field.
- The three algebraic stacks in the first clause are `X`, `Y`, and `Z`, with the
  respective proofs `hX`, `hY`, and `hZ : IsAlgebraicModuliStack ...`.
  Their morphisms are `f : BasedFunctor X Y` and `g : BasedFunctor Y Z`.
- The two quasi-compactness hypotheses are `hfqc` and `hgqc`, using exactly
  `IsQuasiCompactAlgebraicModuliMap`; the quasi-separatedness hypotheses are
  `hfqs` and `hgqs`, using exactly `IsQuasiSeparatedAlgebraicModuliMap`.
- The composite is `f.comp g`, whose underlying functor is `f.toFunctor ⋙ g.toFunctor`,
  hence it is the node's `g ∘ f`. The conclusion is the conjunction of the same
  quasi-compactness and quasi-separatedness predicates for this composite.
- The affine clause has independent stacks `A`, `B`, proofs `hA`, `hB` of algebraicity,
  and `q : BasedFunctor A B`. Its only additional hypothesis is
  `hq : ModuliSchemeTest @IsAffineHom q`.
- Unfolding that existing predicate quantifies over every scheme `T` over `k` and
  every `t : BasedFunctor (discreteModuli (yoneda.obj T)) B`. It supplies a scheme
  `R`, a scheme morphism `p : R ⟶ T`, and an equivalence from the represented scheme
  to `moduliTwoFiberProduct t q`. `IsSchemeModuliBaseChange e p` includes the vertical
  2-isomorphism identifying its projection with `discreteModuliMap (yoneda.map p)`.
  Thus it represents the actual 2-base change and its projection, rather than an
  arbitrary morphism on an equivalent source. `IsAffineHom p.left` is literally
  affineness of the inverse image of every affine open subset of `T.left`.
- The affine conclusion is exactly quasi-compactness and quasi-separatedness of `q`.
  Its quasi-compactness test universes may additionally be enlarged by `v₃`, `w₃`.
- No finite-type, Noetherian, Deligne--Mumford, or absolute-diagonal hypotheses occur
  in either declaration. The imported module's DM-related name does not impose a
  DM hypothesis: the actual definition of `ModuliSchemeTest` has arbitrary based
  categories as endpoints.

Universes are explicitly bound and `autoImplicit` is false. The endpoint hom/object
universes `(v₁,w₁)`, `(v₂,w₂)`, `(v₃,w₃)` are independent. Composition uses the
recorded quasi-compactness predicate at additional test levels `(0,0)`, i.e. its
site/endpoint maximum bounds, exactly the convention used by the existing
`IsAdequatelyAffineMorphism` consumer. This does not make the tests smaller than
the scheme site or impose an equality on endpoint universes. Arbitrary larger
quasi-compact algebraic-stack tests can be checked after their smooth scheme atlases;
therefore using the recorded bounded universe does not add a geometric restriction.

Dependency declarations read and reused:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sfb-algebraic-moduli-stack`: `CategoryTheory.IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, and `SpaceMapIsSmooth`, in
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`.
- `def-sfb-stack-qcqs-morphism`: `CategoryTheory.IsQuasiCompactAlgebraicModuliMap`,
  `IsQuasiSeparatedAlgebraicModuliMap`, `IsQuasiCompactModuli`, and the underlying
  `AlgebraicGeometry.AlgebraicSpace` predicates in
  `Sheaf.AlgebraicGeometry.StackQcqsMorphism`.
- Added the already landed `def-sfb-dm-stack-morphism-properties` to `stmt_deps`
  solely to reuse `CategoryTheory.ModuliSchemeTest`, in
  `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`. Its actual scheme-projection
  comparison is `CategoryTheory.IsSchemeModuliBaseChange` in
  `Sheaf.AlgebraicGeometry.ModuliChartNormalization`; the 2-fibre products,
  `discreteModuli`, `ModuliTwoIso`, and scheme representation are the existing
  declarations in `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`.
  These are exposed by the public `StackQcqsMorphism` import. No dependency record
  is changed, no statement is corrected, and no helper or new node is needed.
- Affine scheme morphisms are Mathlib's `AlgebraicGeometry.IsAffineHom`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`.

The already stated proof dependencies are imported privately: algebraic-stack
fibre products, algebraic-space fibre products and étale covers, affine morphism
permanence, closed immersions and their base change, and quasi-compact inverse
images. The recorded groupoid/stack definitions are already public dependencies.
The currently unstated calculus, representable scheme-test, representable pullback,
space quasi-separatedness, diagonal identities, and space affine-locality nodes
have no module to import; both proof docstrings retain all six natural-language
steps of the accepted proof and name these prerequisites for stage 3. No proof
prerequisite is needed as new data merely to state the present item.

Source checks: read local `stacks-morphisms.tex` at the labels for 050W
(composition of quasi-compact maps), 050K (composition of separation axioms),
04YT (representable quasi-separatedness and diagonal quasi-compactness), and
0CHQ (affine means representable affine). Read Mathlib's definition of
`IsAffineHom` and the separated/quasi-compact consequences. These agree with the
node's intended scheme tests and impose no extra ambient finiteness condition.

Edge cases checked before writing:

- Empty source schemes/stacks and empty test schemes are allowed: no `Nonempty`
  or positive-dimension hypothesis was introduced.
- Identity and isomorphism morphisms, and identity composition, retain the actual
  projection comparison; affineness includes these cases.
- Fields of every characteristic are allowed, without algebraic closedness.
- Nonrepresentable qcqs maps, such as algebraic-stack maps with positive-dimensional
  stabilizers, are allowed in composition; only the affine clause requires scheme
  representability of its tests.
- Infinite-type affine maps are allowed; no finite presentation/type enters `hq`.
- Neither absolute stack diagonal is assumed quasi-compact or quasi-separated.
- Tests include schemes that are not affine, quasi-compact, or separated. In the
  affine clause affineness is relative to each such scheme, not affineness of the
  total test scheme itself.

Searches for an existing exact statement:

- `msearch.py leansearch`, query `composition of quasi compact quasi separated
  morphisms of algebraic stacks and affine morphisms`: eight scheme-morphism hits,
  including quasi-compact/quasi-separated composition and affine multiplicativity;
  none is the algebraic-stack statement.
- `msearch.py leanfinder`, query `Quasi compact quasi separated morphisms of
  algebraic stacks are closed under composition and affine morphisms are quasi
  compact quasi separated`: eight scheme-level permanence hits; no stack theorem.
- `msearch.py loogle`, query `CategoryTheory.IsQuasiCompactAlgebraicModuliMap,
  CategoryTheory.IsQuasiSeparatedAlgebraicModuliMap`: no hits, index reports the
  project identifier unknown. This was supplemented by direct project searches.
- `msearch.py grep`, query `quasiCompact_isStableUnderComposition|
  quasiSeparated_isStableUnderComposition|IsAffineHom`, subdirectory
  `AlgebraicGeometry/Morphisms`: 25 scheme-level hits, including the exact existing
  affine scheme definition, but no stack theorem.
- Direct `rg` in `lean/WeilConjectures` for the item id and both qcqs predicate names
  found no match. Direct `rg` in `lean/Sheaf` found the shared qcqs definitions and
  related permanence/adequacy consumers, but neither theorem being delivered.
  The final declaration names were also searched throughout project Lean and
  Mathlib, with no collisions.
- Direct inspection of the existing scheme-test definition and its node confirmed
  that `ModuliSchemeTest @IsAffineHom` is the required notion; it is reused instead
  of defining another affine-stack predicate.

Validation: the prescribed `scompile.py` compiled the sandbox probe and library
module separately against the live server build, cleanly (6.3 s and 3.3 s).
Both theorem proofs are exactly `by sorry`; no diagnostic commands remain.
No statement dispute or node fault was found.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
