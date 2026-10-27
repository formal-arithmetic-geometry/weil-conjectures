## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCoherentTangentFinite` states
`AlgebraicGeometry.AlgebraicSpace.CoherentModuli.Deformation.coherent_tangent_finite`.
Its sole postponed proof is this theorem, with all eight accepted DAG proof steps in
its docstring. All helper definitions have real data. The existing coherent-family
category is reused, not reconstructed. The node changes only in `lean`; its statement,
statement dependencies, proof and proof dependencies are unchanged.

Source read: `literature/stacks-project/quot.tex`, Situation `situation-coherent`
(Tag 08KB), and `lemma-coherent-tangent-space` (Tag 08W8), including the entire proof.
The source's possible use of the proper-space Ext theorem on a nonproper ambient
space is already repaired in the accepted node proof; this delivery retains that
proper-support proof route, rather than assuming X or its fibre proper.

Hypothesis and clause correspondence:

- The scheme S and algebraic spaces X,B are `{S : Scheme.{u}}` and
  `{X B : AlgebraicSpace S}`. The field is `{k : Type u} [Field k]`; all universe
  levels and variables are explicitly bound, with both auto-implicit options disabled.
- The morphism is `f : X ⟶ B`, with `hfp : ProperQuotFinitePresentation f`.
  The recorded definition expands to local finite presentation, quasi-compactness,
  and quasi-compactness of the diagonal. No separatedness or ambient flatness is added.
- For an S-scheme T, the category C(T) is precisely the fibre of the existing
  `CoherentModuli.category f`. Its objects retain `ProperQuotTest B` (T together
  with b:T→B) and the actual module on the sheaf fibre product `properQuotFibre f T`.
  `CoherentModuli.quasiCoherent` and `.finitePresentation` are the recorded module
  predicates, not independently invented conditions.
- The flatness clause is `CoherentModuli.flat`: `Scheme.Modules.IsFlatOver` on
  every actual scheme-chart restriction. For the quasi-coherent modules in question,
  this is precisely the stalkwise relative flatness convention in the node.
- Proper support is `CoherentModuli.properSupport`: a closed immersion i:Z→X_T,
  proper composite to T, and a finite type quasi-coherent G with i_*G ≅ M.
  Thus it is the node's existential carrier condition, not properness of X_T.
- Arrows and their composition are `CoherentModuli.Hom`, `.identity`, `.composition`
  and `.category`: maps over B and actual tensor-pullback isomorphisms, with the
  already normalized tensor identity and composition comparisons.
- Local Noetherianity is `[IsLocallyNoetherian S]`, the Mathlib affine-local property.
- Local finite presentation of B→S is
  `hB : ∀ U : B.EtaleSite, LocallyOfFinitePresentation U.obj.left.hom`.
  Here U.obj.left is the actual S-scheme in the chart, so its `.hom` is U→S.
  This is the scheme-target chart test for B→S. Testing all etale charts agrees
  with the existing morphism-property convention; it does not require B to be a scheme.
- A finite type field over S is `a : Spec (.of k) ⟶ S` with
  `[LocallyOfFiniteType a] [QuasiCompact a]`, exactly the finite type convention.
- The arbitrary x₀ is
  `x : Functor.Fiber (CoherentModuli.category f).p (Over.mk a)`.
- A marked deformation over k⊕V is `Marked f a x V`: an object Y over the actual
  `ProperCurveFamily.directionBase k a V` and an arrow from x over its actual
  `directionReduction`. Every coherent-family arrow is a cartesian tensor-pullback
  isomorphism; such an arrow is precisely the marking of the reduction by x.
  The structured-arrow category requires its arrows to commute with that marking.
- `Classes` quotients by the actual isomorphism setoid of the marked category;
  `Tangent f a x` takes V=k, hence the actual dual numbers k[ε]/(ε²).
  The conclusion supplies `AddCommGroup`, `Module k` and `FiniteDimensional k`
  on this exact set, not on an unspecified isomorphic vector space.
- `IsZeroClass` characterizes the constant marked pullback by a cartesian arrow
  back to x over `dualProjection` splitting the marking. The zero equivalence
  in the theorem fixes the origin.
- `IsScalarClass` uses the actual `directionMap` for c times the identity of k.
  `PullsBack` keeps both the cartesian module arrow and the equality on markings.
  The theorem identifies this relation with multiplication by c.
- `IsSumClass` uses the actual k⊕(k×k) test, its two coordinate projections to k,
  and the sum of those projections. A single marked coherent object restricting
  to both inputs is exactly the gluing over the marked common special fibre;
  the last pullback gives the sum. The theorem identifies this relation with addition.
- `TrivialLift` retains the actual marked pullback along k→k[ε] and its cartesian
  projection. The theorem asserts its existence, not a data choice from a sorry.
  Any two such cartesian lifts are uniquely isomorphic compatibly with projection;
  the existential model therefore represents precisely the canonical trivial pullback.
- `InfAut f a x Y` consists of automorphisms of that trivial lift lying over the
  identity of the dual-number base and commuting with the marking. It imposes
  no requirement to preserve the projection back to x, which would incorrectly
  discard infinitesimal automorphisms.
- The conclusion supplies a finite-dimensional k-vector-space structure on this
  exact automorphism set. Its zero is the identity, and its addition is composition.
  `IsAutScalar` is cartesian transport along scaling on the trivial lift: the
  arrow q over scaling is fixed by its projection to x, and qg=hq specifies the
  pulled-back automorphism. The theorem identifies this with scalar multiplication.

Dependency declarations read and used (module, declaration):

- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`, `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, structure sheaf and modules. Its representability,
  etaleness, surjectivity, diagonal and atlas definitions were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`; actual sheaf pullbacks are retained.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`, `AlgebraicSpace.QCoh`,
  based on Mathlib's `SheafOfModules.IsQuasicoherent`, also used by CoherentModuli.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`,
  `AlgebraicSpace.moduleDirectImage`, `.moduleTensorPullback` and its adjunction.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`,
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver` (full affine-open signature and docstring).
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`, `ProperQuotTest`,
  `properQuotFibre`, `properQuotFibreMap`, and `ProperQuotFinitePresentation`.
  The full signature of `ProperQuotient` was also checked for the three module conditions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`, `MapIsLocally`,
  `MapIsLocallyOfFinitePresentation`, `MapIsProper`, and the related chart properties.
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`; and
  `Mathlib.AlgebraicGeometry.Noetherian`, `IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `LocallyOfFinitePresentation`.
- `Mathlib.Algebra.Field.Defs`, `Field` (the field node is a Mathlib leaf).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `QuasiCompact`.
- `def-weil-size-convention` is metatheoretic, with no declaration to import;
  explicit universe u on schemes, fields, bases and directions supplies its role.

Additional existing interfaces reused:
`Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral`, `CoherentModuli` and
`CoherentModuli.category`, including its entire object, arrow and composition definitions;
`Sheaf.AlgebraicGeometry.MarkedCurveDeformations`, `ProperCurveFamily.directionBase`,
`directionReduction` and `directionMap`, together with the pre-existing `dualProjection`.
The former is imported only for its concrete category; its theorem
`coherent_stack_general` is never used. Its eventual proof-only import of this module
must be omitted because it would close an import cycle, as allowed by stage-2 rule 7.
There is no current import cycle. Extracting that already-published category into a
separate foundational module would be a maintainer-owned library refactor, not a reason
to duplicate the notion in this worker's statement.

The recorded affine-base `StackDeformation.Marked`, `Classes`, `Tangent`, and all
operation relations in `MarkedStackDeformations.lean` were read in full. They require
S=Spec R and finite type k/R. This node allows any locally Noetherian S, so those
specialized types cannot be applied globally without restricting S to be affine.
The helpers here only render this item's own marked coherent-family objects over its
actual S, using the same structured-arrow and isomorphism-quotient constructions;
they introduce no separate independent mathematical notion requiring a new DAG node.

Proof imports: every available recorded proof-dependency module is imported, directly
or through its statement import. As of this delivery, no Lean module is recorded for
`lem-sfb-space-coherent-pushout`, `lem-sfb-space-proper-support-module-ext-finite`,
`lem-sfb-space-module-flat-chart-test`, or `lem-sfb-infinitesimal-pushout-affine-charts`.
These are proof prerequisites only, so their absence does not affect this statement.
The ring finite-presentation base-change/composition node has a Mathlib match rather
than a project module; those declarations arrive via the finite-presentation imports.

Edge cases checked before writing and again after compilation:

- M₀=0: proper support can be empty, Inf is zero, while the tangent may still include
  movement of b₀ in B; the statement retains this movement.
- X empty: only the zero module remains, but arbitrary base-map deformations remain.
- Empty S or B: no field-valued x exists, so no unsupported object is asserted.
- Nonproper X and nonseparated f: no ambient properness or separatedness assumption.
- Positive characteristic, inseparable k over the base, and non-algebraically-closed k:
  no characteristic, separability or closure restriction occurs.
- Scalar c=0: cartesianness, rather than cancellation of an invertible scheme map,
  specifies the pulled-back automorphism; tangent zero is the constant marked lift.
- The full k×k gluing test is included; addition is not chosen arbitrarily.
- Automorphisms must not fix the projection back to x; that condition is deliberately
  present only on the canonical scaling arrow, not on InfAut.
- Nonaffine locally Noetherian S remains covered by the actual arbitrary-S interfaces.

Searches for reuse (all prescribed tools):

- `msearch.py ... leanfinder "Finite dimensional tangent and infinitesimal automorphism
  spaces for flat finitely presented coherent modules with proper support on an algebraic
  space"`: eight hits, for algebraic H1 cotangent modules, differentials, formal
  unramifiedness and smoothness; none is the present deformation finiteness assertion.
- `msearch.py ... loogle "FiniteDimensional, Ext"`: zero hits.
- `msearch.py ... grep "coherent.*tangent|infinitesimal.*automorphism|CoherentModuli"`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` for these names/concepts and the exact blueprint id:
  no matching theorem; the only tangential result is the scheme tangent-bundle material.
- `rg` in `lean/Sheaf` found the existing `CoherentModuli` category and the affine-base
  marked-stack interfaces, which are reused or consulted as described above. No
  coherent-family tangent-finiteness theorem exists.
- `tools/blueprint_refs.py search 'marked coherent'`: zero blueprint node matches.
  `ancestor lem-sfb-space-coherent-tangent-finite` reports ancestor None, as in the item.
- No new definition node is needed and no source-based statement correction was made.

Validation: prescribed `scompile.py Q136 lem-sfb-space-coherent-tangent-finite` compiled
this module both in its sandbox and as its library module, against the live published
library. Both succeeded in under five seconds with no errors or unexpected warnings.
The helper data contain no sorry; the only theorem is intentionally sorry-only.

## Second reading by Q136

Fresh reading of the node, source and completed module checked the correspondence above.
The marking must be retained through the quotient, so `isIsomorphicSetoid` is taken on
the structured-arrow subcategory rather than on unmarked modules. The automorphism
space fixes the dual-number base and marked special fibre but not the projection to x.
The scalar operation on automorphisms is characterized through the cartesian scaling
arrow even when c=0. All three tangent operation relations use actual base changes.
The B→S hypothesis reads the structure maps of all etale charts, so it neither assumes
a scheme B nor reduces the arbitrary scheme S to an affine one. The statement includes
both required finite-dimensional spaces and does not assume properness of X or
separatedness of f. No statement mismatch or disputed claim was found.

This is the worker's fresh second pass, not an independent second agent: the dispatcher
explicitly prohibits starting another agent and provides the maintainer's independent
review of this delivery. No independent review is claimed here.
