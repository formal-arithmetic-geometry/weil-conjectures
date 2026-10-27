## Worker report

The module `Sheaf.Paper.InternalScalarMateProjection` states
`AlgebraicGeometry.ProEtale.QuotientChange.internal_scalar_mate_projection`.
Its sole theorem has proof `sorry`. All fifteen helper definitions have real
construction data. The node's natural-language statement and proof are unchanged.

Hypotheses and objects, clause by clause:

- Arbitrary commutative condensed rings are `Λ Λ' : Sheaf (coherentTopology
  Profinite.{u}) Ab.{u + 1}`, each with `MonObj` and `IsCommMonObj`. This is the
  unbundled presentation of `Profinite.CondensedRing`; `a : Λ ⟶ Λ'` with
  `[IsMonHom a]` is the arbitrary ring map. There is no flatness assumption.
- `{X Y : Scheme.{u}} (f : X ⟶ Y)` is any scheme morphism. The recorded small
  pro-etale sites have object universe `u + 1`, Hom universe `u`. They are never
  replaced by the large site or by equal object/Hom universes.
- `Modules Λ T`, `Modules Λ' T` use the recorded `condensedRingObj`, so the rings
  are precisely the pullbacks from the point, not constant coefficient sheaves.
  `DerivedCategory` is the ordinary unbounded localization. The tensors are
  `CondensedRing.derivedTensor`, with no completion or bounded restriction.
- `D a T`, `V a T`, `L Λ f`, `F Λ f`, and `adj Λ f` are the recorded scalar and
  geometric functors and adjunctions, including their actual counits. `B a T`
  is the restricted regular S-module in degree zero.
- `(tX : TensorNormalization a X)`, `(tY : TensorNormalization a Y)`, together
  with `hX`, `hY : TensorNormalized ...`, are the node's normalized e maps.
  `(lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)` and
  `hlam : PullNormalized a f lam` are its normalized lambda. These are arbitrary
  normalized choices, not freshly chosen isomorphisms. The existence theorem
  `internal_scalar_pullback_normalization` supplies exactly such data.
- `scalarRestrictionPull` is b: the localization of the existing
  `comapUpperStarIso`, conjugated by the canonical exact-pullback derived
  comparisons. `scalarRestrictionPush` is its inverse's geometric right mate
  under `adj Λ' f` and `adj Λ f`; thus its adjunct compatibility is built in.
  The first conjunct states `IsIso` of this canonical d, as in the dependency
  theorem. No assumption of invertibility is added.
- `scalarCoefficientUnit` identifies the restriction of the regular S tensor
  unit with `B`. `scalarCoefficientPull` is c: use b inverse on that regular
  unit and the published `leftDerivedUpperStarUnitIso`. This is the cartesian
  coefficient map induced by alpha_f, including its localization factors.
- `scalarTensorPull` is literally the component of
  `CondensedRing.leftDerivedUpperStarTensor`. Its explicit endpoint type only
  exposes the scalar interface's L name; it retains the canonical derived
  counit normalization.
- The first displayed node equation is `ScalarMatePullEquation`, expanded by
  `scalarPullLeft` and `scalarPullRight`. Lean composes left to right:
  b inverse, V(lambda), e_X equals L(e_Y), delta, and tensoring by c.
- `rho a f lam` is the existing direct-image mate. The second displayed node
  equation is the universally quantified K equality in the theorem: V(rho),
  d at D_X K, F(e_X) equals e_Y at F K followed by `scalarProjection`.
  The latter is literally `moduleObjectProjectionMap Λ f K (B a Y)` followed
  by F applied to tensoring with c. It is not an arbitrary map of its endpoints.
- `ScalarMateSectionEquation` gives the same equality after the fixed derived
  section equivalence. `scalarSectionLeft` includes that functor's application,
  its fixed direct-image comparison and its tensor comparison.
  `scalarSectionRight` uses e_Y, its tensor/direct-image comparisons and
  `scalarSectionProjection`. The last map is the actual
  `ModuleRingedComparison.derivedAdjunction` transpose of
  `tensorPullComparison` followed by tensor of its actual counit with c.
  The ringed delta is the existing uniquely representative-normalized one.
- The following K clause states exactly `IsIso (rho.app K) ↔
  IsIso (scalarProjection ... K)`. It does not assert either is always invertible.
- The last clause is naturality of the specified projection in every derived
  map `q : K ⟶ K'`. The mate is already a `NatTrans` (`rho`), e, b and d are
  natural transformations/isomorphisms, delta is a bifunctor transformation,
  and the section comparisons are natural isomorphisms. Consequently the
  displayed equations are identities of natural families, including arbitrary
  derived morphisms, not only maps represented by single chain maps.
- The section `[∀ T, HasDerivedCategory.{u + 1} ...]` parameter chooses a
  localization of each recorded section-module category. It is the same size
  parameter as in the recorded normalization theorem; it adds no geometric,
  coefficient, exactness, flatness, or finiteness restriction.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `coefficientPullbackIso`,
  `condensedPullbackHom`, and the commutativity instances.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `moduleObjectDerivedPullback`, `moduleObjectDerivedPushforward`;
  its public upstream module: `derivedUpperStarLowerStarAdjunction`,
  `leftDerivedUpperStarIsoMapDerivedCategory`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  the ordinary relative `derivedTensor` and recorded derived tensor/Hom structure.
- `Sheaf.Paper.InternalDerivedScalarComparisons`: `Modules`, `D`, `L`, `F`,
  `adj`, `V₀`, `V`, `B`, `TensorNormalization`, `TensorNormalized`,
  `PullNormalized`, `rho`.
- `Sheaf.Paper.InternalScalarPullbackNormalization`:
  `internal_scalar_pullback_normalization`, `scalarSectionPullComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingSheafChangeAdjunction`, including conservativity and the exact
  adjunct compatibility of the canonical restriction comparisons.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionModuleEquivalence`, via the fixed `ModuleRingedComparison` operations.
- `Sheaf.Paper.ModuleObjectProjectionMap`: `moduleObjectProjectionMap` and
  its real `moduleObjectProjectionData` (the published right-adjoint projection).
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` publicly retains the
  arbitrary ring-sheaf `proEtaleRingDerivedPullback`, `...DirectImage`,
  `...Adjunction` constructions required by the node.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `ringedTopoiCanonicalDerivedTensorPullback` and its representative condition.
- The two added, already landed statement dependencies
  `def-pd-section-derived-realization` and `def-pd-section-derived-tensor-data`
  own the exact section derived equivalence, operations, adjunction, tensor,
  tensorComparison and tensorPullComparison used in the section clause.
  Their modules are publicly imported. No dependency record is repaired.
- All recorded proof-dependency modules are imported; no import cycle is closed.

Edge cases checked against the formulas: f identity, a identity, zero K, empty
scheme, zero target ring, nonflat Z to Z/2 on a point, and unbounded complexes.
The proof's auxiliary K-flat resolution of S is retained: S itself is never
assumed flat or K-flat. Identity coefficient change gives the usual unit
projection; zero cases give zero arrows; nonflat coefficients are handled by
D and the computation-normalized e and lambda. No properness, flatness,
boundedness, or completeness hypothesis is present.

Searches (also recorded in sandbox `searches.jsonl`):

- LeanFinder through msearch.py: “Restriction of an internal derived scalar
  extension pullback mate is the canonical projection formula map”. Eight
  ModuleCat extend/restrict adjunction hits; none states the node.
- Loogle through msearch.py: `CategoryTheory.mateEquiv`. Twelve generic mate
  and pasting results; reuse `mateEquiv`, no matching geometric statement.
  An earlier `Adjunction.rightAdjointProjectionMap, mateEquiv` query reported
  unknown first name; the actual project declaration was then read directly.
- Mathlib grep through msearch.py: `scalar.*[Mm]ate|[Mm]ate.*[Pp]rojection`
  and `scalar.*mate|mate.*projection` in CategoryTheory: no hits.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for this node id and
  declaration: no existing match. The nearby
  `Sheaf.Paper.InternalScalarProjectionMate.internal_scalar_projection_mate`
  was read in full: it assumes exact/flat scalar extension and uses the
  opposite tensor ordering; it is not this arbitrary-coefficient theorem.
  `ChangeOfCoefficients` provides the exact ordinary restriction/pullback
  comparison reused here, but its derived push comparison assumes flatness.

Source checked: current blueprint integral proof paragraphs (1), (3), and local
Stacks `sites-cohomology.tex`, lemma-pullback-tensor-product (07A4),
equation-projection-formula-map (0B56), lemma-projection-formula (0944), and
the adjunction lemma. The node's seven-step proof is included in the theorem
docstring. No statement correction, new node, or disputed statement is needed.

Compilation: prescribed scompile.py, 60 seconds per file. After explicit map
endpoint annotations and controlled unfolding of the existing interface names,
both sandbox and library modes compile in approximately eight seconds. All
variables/universes are explicit (`autoImplicit false`). No diagnostic commands,
new axioms, proved theorems, or data holes remain.

## Second reading by Q08

The dispatcher explicitly forbids starting other agents; this is a second pass
by the same worker, not a claim of an independent reviewer. The maintainer's
independent review remains required. With the node and module open, I checked
both composition orders and endpoints: the first equation starts in L V D M
and ends in L M tensor S_X; the second starts in V D F K and ends in
F(K tensor S_X). The section equation has those same endpoints after the fixed
section functor and its explicitly displayed comparisons. I checked that the
projection uses the recorded moduleObjectProjectionMap literally, that the
ringed projection uses the specified counit adjunct, and that the iff concerns
the specified maps. The initial draft's inferred tensor/projection endpoint
types triggered large unfolding; explicit types and transparency controls fixed
compilation without changing objects or adding mathematical assumptions. The
helper documentation was corrected to describe the literal projection composite.
All helper declarations are listed in lean.declarations. The extra landed
section-definition owners are now direct statement dependencies. No mathematical
mismatch or unresolved node fault was found in this pass.

## Repair of return L

The returned head 4c2e0f7a3486 declared scalarSectionPushComparison, which is
already declared in Sheaf.Paper.ScalarGeometricExchangeRectangle on the current
base. The saved packet first passed deliver2.py --no-push (c5c312a042e), but
that mechanical check does not remove the independent review defect. I read
both definitions: both unfold F and moduleObjectDerivedPushforward and return
ModuleRingedComparison.derivedPushComparison. The existing declaration uses
derivedFunctor, the functor of the same fixed derivedEquivalence, and takes
the coefficient ring explicitly. Thus it is exactly the same comparison.

The repaired module publicly imports Sheaf.Paper.ScalarGeometricExchangeRectangle,
deletes its local scalarSectionPushComparison, and uses the imported comparison
as scalarSectionPushComparison Λ f in scalarSectionLeft and scalarSectionRight.
The removed declaration is also deleted from lean.declarations. No replacement
name, new definition, theorem, node, or mathematical hypothesis is introduced.
The theorem signature, both section equation endpoints, and every clause are
unchanged. The existing comparison requires only the already present section
derived-category structure for Λ; it adds no such requirement for Λ'.

Second reading of this repair: the two section arrows now use the same published
comparison with the same direction. All fifteen retained helper definitions have
real data; the theorem remains the only sorry. A direct namespace search confirms
the deleted declaration has a single owner in ScalarGeometricExchangeRectangle.

Repair validation: scompile.py compiled the repaired module in both sandbox and
library modes with no diagnostics. The verbatim signature agrees with lean.statement;
lean.declarations lists exactly the sixteen remaining declarations (fifteen helpers
and the theorem). The two prior added section-definition dependencies are retained.
