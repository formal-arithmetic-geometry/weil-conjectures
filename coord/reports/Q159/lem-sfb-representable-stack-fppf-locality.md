## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableStackFppfLocality` states
`CategoryTheory.representable_stack_fppf_locality`, with its entire proof `sorry`.
The node's statement, proof, proof dependencies and source are unchanged. Its statement
requirements now explicitly cite the two landed nodes owning the four space predicates
and the new scheme-test interface. No theorem is proved in this delivery.

Clause-by-clause correspondence:

- A field k: `(k : Type u) [Field k]`. Every stack, space and scheme test is over
  `Spec (.of k)`, so these are k-objects with their structural maps, not unrelated
  absolute objects. Characteristic is unrestricted.
- Algebraic stacks Z and Y: independently sized `BasedCategory.{v₁,w₁}` and
  `BasedCategory.{v₂,w₂}`, with `hZ : IsAlgebraicModuliStack Z` and
  `hY : IsAlgebraicModuliStack Y`. This imports the recorded stack definition and
  retains etale descent, representable diagonal and a smooth surjective scheme atlas.
- The given morphism: `f : BasedFunctor Z Y`; its scheme-test representability is
  `hf : IsRepresentableByAlgebraicSpaces f` from the recorded groupoid framework.
- The algebraic-space cover: `W : AlgebraicSpace (Spec (.of k))` and the actual
  stack map `q : BasedFunctor (discreteModuli W.obj.obj) Y`.
- The surjective, flat, locally finitely presented hypothesis is `hq`. For every
  scheme test `(T,t)` it gives an algebraic-space presentation `(B,b)` with
  `HasSpaceBaseChange q T t B b`. `SpaceMapIsSurjective B T b` is the recorded
  joint-chart-point surjectivity condition. Every etale scheme chart `a` of B has
  `Flat (yoneda.preimage (a ≫ b)).left` and
  `LocallyOfFinitePresentation (yoneda.preimage (a ≫ b)).left`. These are exactly
  scheme-base-change chart tests. No quasi-compactness is imposed on q or its charts.
- Each property separately: `P : MorphismProperty (AlgebraicSpace (Spec (.of k)))`
  and the disjunction `hP` selecting exactly `MapIsAffine`, `MapIsFiniteType`,
  `MapIsQuasiFinite`, or `MapIsSeparated`. There is no simultaneous assumption
  of the other three properties.
- Affine: the existing `AlgebraicSpace.MapIsAffine` quantifies over affine scheme
  tests and exhibits an affine scheme representing the cartesian square. This is
  precisely the affine-source convention in the item, not affineness on source charts.
- Finite type: existing `MapIsFiniteType` is `MapIsQuasiCompact` and the universal
  compatible-etale-chart test of `LocallyOfFiniteType`.
- Quasi-finite: existing `MapIsQuasiFinite` is `MapIsFiniteType` and finiteness of
  the point classes of each canonical fibre over every algebraically closed field
  `Ω : Type u`, with `[Field Ω] [IsAlgClosed Ω]` and its structural map to the base.
- Separated: existing `MapIsSeparated` is scheme-test representability of the relative
  diagonal by `IsClosedImmersion`. No separatedness is imposed on the cover or base.
- Meaning of P(f): `ModuliAlgebraicSpaceTest P f` tests every scheme map into Y,
  presents its actual 2-base change by Z with specified projection p to that scheme,
  and applies P to that algebraic-space projection. The test scheme is the existing
  `schemeSpace T`, not a second construction of a scheme as an algebraic space.
- Arbitrary base change: the first conjunct quantifies over every independently sized
  algebraic stack Y' and every `g : BasedFunctor Y' Y`. It asserts representability
  of `moduliTwoFiberFst g f` and preservation of the P scheme tests. That projection
  is from the existing category of pairs with an isomorphism of their images.
- The specified Z_W: the second conjunct exhibits `(V,p)` with
  `HasSpaceTargetBaseChange f W q V p`. This means an equivalence of discrete V
  with the actual `moduliTwoFiberProduct q f`, and a `ModuliTwoIso` identifying
  its first projection with `discreteModuliMap p.hom.hom`. Thus p is the actual
  projection, not an arbitrary map from a bare isomorphic space.
- The locality assertion is exactly `ModuliAlgebraicSpaceTest P f ↔ P p` for this
  presentation. Existence of V is asserted rather than postulated as additional data.
  The space-property isomorphism invariance in the imported proof dependency makes
  this independent of presentation. No arbitrary canonical-map choice is introduced.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (through imported scheme/field foundations).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `discreteModuli`, `discreteModuliMap`, `BasedFunctor`, `ModuliTwoIso`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`, `SpaceMapIsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`; these reuse the representable-diagonal fppf-sheaf model.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine` and
  `MapIsQuasiFinite`. `Mathlib` dependencies of these predicates include
  `IsAffineHom`, `Field`, and `IsAlgClosed`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFiniteType`,
  `MapIsSeparated`, `MapIsLocally`; these use `LocallyOfFiniteType`,
  `MapIsQuasiCompact`, and `IsClosedImmersion` from the recorded dependency chain.
  The Mathlib locally-finite-type, affine, closed-immersion and algebraic-closure
  declarations and their source docstrings were opened and read.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace` (the actual Yoneda
  fppf sheaf) in the new helper definition.
- The new module `Sheaf.AlgebraicGeometry.RepresentableSpacePropertyTest`:
  `CategoryTheory.ModuliAlgebraicSpaceTest` and `HasSpaceTargetBaseChange`.

The stated proof dependencies are plain imports:
`AlgebraicSpaceFourPropertyFppfDescent`, `AlgebraicSpaceFibreProductsEtaleCovers`,
`AlgebraicStackFibreProducts`, `StackChartwiseSmoothEtaleCalculus`.
Their theorem signatures were read. `lem-sfb-representable-pullback-over-space` has
no Lean record in the read repository, so there is no recorded module to import for
this proof-only dependency; the natural-language proof keeps its use explicit.
It is not needed to type the statement. The new statement asserts the needed space
presentation as part of the conclusion.

Edge cases checked before writing:

- Empty Z is allowed; its pullbacks are empty and all four properties hold.
- Empty Y or W is allowed. Surjectivity of an empty W forces an empty target;
  the chart-test quantifiers have their usual empty-scheme meaning.
- A nonempty target cannot be covered by the empty space: the specified
  `SpaceMapIsSurjective` clause fails at any target test point.
- Identity cover and identity base change recover the original projection; no
  hypothesis excludes them. Non-surjective f and non-flat f are allowed.
- The fppf cover need not be quasi-compact: an infinite disjoint scheme cover is
  permitted. This matters because adding quasi-compactness would strengthen the item.
- Source charts of an affine map need not themselves be affine over the target:
  this is why `ModuliSpaceTest @IsAffineHom` would be incorrect. Similarly
  separatedness must test the diagonal of the whole map, not each source chart.
- The four predicates are alternatives, not a conjunction. Nonseparated finite-type
  maps and non-quasi-finite affine maps remain permitted for their selected P.
- Scheme, field and coefficient universe u agree with the recorded space definitions;
  stack object and morphism universes are independent. No extra universe equality,
  smallness or essential-smallness assumption was imposed on the stack categories.
- The Tag 04XD proof's cover typo was checked: its covering object must be
  T ×_Y W, not T ×_Y V (take Z empty and Y=W=Spec k). The existing DAG proof already
  corrects this, and the Lean docstring follows that proof. No statement correction.

Searches for an existing statement or definition:

- msearch leanfinder, query "A representable morphism of algebraic stacks is affine
  finite type quasi finite or separated if and only if its base change along a
  surjective flat locally finitely presented map of algebraic spaces is": eight
  scheme/abstract-property results, no stack locality theorem.
- msearch loogle, query `"IsRepresentableByAlgebraicSpaces", "MorphismProperty"`:
  zero hits.
- msearch grep in Mathlib/AlgebraicGeometry, query
  `stack.*fppf|representable.*stack|MapIsQuasiFinite`: zero hits.
- msearch leansearch, query "Properties of representable morphisms of algebraic
  stacks local on the target for fppf covers": eight hits, including
  `IsLocalAtTarget`, `Functor.relativelyRepresentable`, and `targetAffineLocally`,
  none the stack theorem or a test of arbitrary algebraic-space properties.
- msearch leanfinder, query "A property of algebraic space morphisms defines a
  property of representable stack morphisms by testing every scheme base change":
  eight scheme-property hits, no matching interface.
- rg in lean/WeilConjectures for the item id and stack-fppf/property-test names:
  no declaration. rg in lean/Sheaf identified the exact four space predicates,
  existing source-chart `ModuliSpaceTest`, scheme-only `ModuliSchemeTest`, and
  space-only descent results. None has the statement here.
- rg in dag/nodes, lean/Sheaf and lean/WeilConjectures for
  `ModuliAlgebraicSpaceTest|HasSpaceTargetBaseChange` gave no definition.
  A conceptual DAG search returned the space fpqc affine criterion; it is a space
  descent theorem, not a stack property-test definition. blueprint_refs.py search
  "scheme base change" and "algebraic space property" each returned zero matches.
- The mandated CompactObject example is withdrawn in this checkout; its node records
  the upstream `WeilConjectures.CategoryTheory.CompactObject`, whose definition and
  source header were read for the example convention.

Validation: both delivered modules were compiled separately with scompile.py,
including the helper before its consumer, with no errors or warnings. No local
Lean invocation or global build was run.

## New nodes

`def-sfb-representable-space-property-test` defines the scheme-base-change extension
of an algebraic-space morphism property and its algebraic-space target presentation.
Its source is Section 04XB of stacks-properties.tex, the definition preceding 04XC
and the projection convention of 04XC/04XD. Its data consists only of the existing
2-fibre product, specified projection, equivalence predicate, and the existing
scheme-as-space object. Definitions are fully written with no postponed proof.
It is needed because the existing source-chart interface cannot express affine or
separated morphisms. The LeanSearch, LeanFinder, Loogle, Mathlib grep, project grep,
DAG and blueprint searches above found no duplicate. All actual search outputs are
recorded in its mathlib_searches. The theorem cites this new node and the two existing
space-property definition nodes directly. There are no dependency-record repairs.

## Second reading by Q159

A separate pass reopened the node JSON, both module files, the recorded stack/space
interfaces, and Stacks 04XC/04XD. This is a worker self-check; no second agent was
started, as the dispatcher brief explicitly prohibits it. Independent delivery review
is the maintainer's, as specified in that brief.

The pass checked each binder against the field, algebraic-stack, representability,
space-cover and three covering-property hypotheses; the above clause list gives the
exact Lean for each. It checked each of the four selected space definitions against
the item's last sentence, then checked the base-change and iff conjuncts and both
projection comparisons. In particular, `HasSpaceTargetBaseChange` remembers the map
to W, and `ModuliAlgebraicSpaceTest` applies P to Z → T itself. The existing
source-chart predicate was deliberately not reused for these non-source-local
properties. The test is an existential presentation for each test scheme, as in the
recorded representability predicate; it does not choose any unspecified data from a
sorry theorem. The comparison is an equivalence, not a mere bijection of objects.
All universes and implicit variables are explicitly bound. No mismatches requiring a
statement correction were found. The only proof placeholder is the item's named
theorem, with the DAG proof written step by step in its docstring.
