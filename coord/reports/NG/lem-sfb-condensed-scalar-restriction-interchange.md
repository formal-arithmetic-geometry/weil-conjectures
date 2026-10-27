## Worker report

The module `Sheaf.CategoryTheory.CondensedScalarRestrictionInterchange` states the
scalar-adjunction conjugacy and the two common-transpose identities for the recorded
unbounded condensed invariant functors. All five theorem proofs are `sorry`;
definitions have real data. No existing node field other than `lean` changes.
There are no new nodes or dependency modules.

Sources read: the entire item and its seven proof steps; every statement dependency's
statement and binding, with the bound declarations and their docstrings; the current
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3); and Stacks
`sites-cohomology.tex`, labels `lemma-derived-pullback-composition` (0D6D),
`lemma-derived-pushforward-composition` (0D6E), and
`lemma-adjoints-push-pull-compatibility` (0FPI). The blueprint paragraph gives the
coefficient/direct-image context, while the precise auxiliary claim is the
agent-formulated node. Its source already says that an exact external reference is wanted;
this delivery does not claim that the blueprint itself spells out the auxiliary lemma.

Hypotheses and clauses, individually:

- The coherent profinite site and coefficient bound are exactly those of
  `CondensedBar.Ring.{u}`: commutative ring objects in
  `Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1}`. The site is not replaced
  by the category of discrete groups or continuous topological modules. The explicit
  `universe u` implements `def-weil-size-convention`, which is a convention node.
- R and R' are `A A' : CondensedBar.Ring.{u}`, so both are arbitrary commutative
  condensed rings. Their internal module categories are the existing `Modules A`
  and `Modules A'`, transparent specializations of Mathlib `CategoryTheory.Mod`.
- J and H are `G H : Type u` with `Group`, `TopologicalSpace` and `IsTopologicalGroup`.
  No compactness, Hausdorffness or profiniteness assumption is imposed on either group.
  `Equivariant A G` is the recorded action on every C(S,G), natural in profinite S.
- The ordinary unbounded derived categories are `DerivedCategory.{u+1}` of those
  module/action categories. No boundedness or cohomology-degree restriction occurs.
- T, Gamma, L, F and their normalized adjunction are exactly the imported `trivial`,
  `invariants`, `trivialDerived`, `derived`, and `adjunction`. Their units and counits
  are used directly; no replacement adjunction is chosen for invariant functors.
- The coefficient ring map is any `a : A ⟶ A'`. The scalar restrictions s_0 and s_G
  are exactly `scalarBase a` and `scalarDerived a G`; U and U' are
  `groupDerived A v` and `groupDerived A' v` for `v : H →ₜ* G`.
- The named E_0 and E_G in the node are rendered by arbitrary models `E₀`, `E`, with
  their specified scalar-extension adjunctions `e₀ : E₀ ⊣ scalarBase a` and
  `e : E ⊣ scalarDerived a G`. This is a model-independent rendering of the adjoints
  already introduced in the node, not an additional exactness, injectivity or flatness
  hypothesis. In particular one can instantiate E_0 with the recorded
  `Mod.derivedExtendMapDerivedCategoryAdjunction`; adjunction-compatible uniqueness
  transports the formula to any chosen K-flat model.
- The identity on underlying sheaves in the scalar/trivial square is not replaced by
  an arbitrary isomorphism. `scalarTrivialExist` uniquely specifies its forward map
  by `(e.hom.app M).val ≫ scalarAction.underlying.hom.app (trivial.obj M) = 𝟙 _`.
  `scalarTrivial` selects from that unique characterization. `scalarTrivialDerived`
  localizes it using the existing exact-composition identifications.
- The left comparison E_G L_G → L'_G E_0 is `scalarPullbackComparison a e₀ e`, the
  actual `mateEquiv` inverse of that exact scalar/trivial identity.
  `scalarPullbackComparison_isIso` states its invertibility. This uses the explicit
  normalized balancing formula for the canonical ringed pullback comparison, as in
  the item's proof step 2: on flat-term K-flat representatives both preserve insertion
  x ↦ 1 tensor x. The docstring supplies the identification with the composition
  comparisons c_{f,g} of the ringed square. `scalarPullbackIso` uses the theorem only
  to add the inverse proof to this already specified map.
- The conjugacy clause is `scalarComparison_conjugate`: conjugation for
  `(adjunction A G).comp e` and `e₀.comp (adjunction A' G)` of the inverse left
  comparison is exactly the existing `scalarComparison a`. The inverse is necessary
  because Mathlib `conjugateIsoEquiv` reverses the direction of left comparisons.
- The fixed-section submodule equality, with its inclusion, is exactly the imported
  `scalarInvariantsExist`/`scalarInvariants` equation; it is not redeclared. The
  explicit equation on every complex is exactly `scalarComparisonExist` in
  `Sheaf.CategoryTheory.CondensedDerivedInvariants`, including all
  `mapDerivedCategoryFactors` identifications. Its unique witness is the d used here.
- Shift compatibility is already `scalarComparisonShift` of that same dependency.
  This uses the fixed integer shift structures of `scalarDerived`, `scalarBase` and
  `derived`. Naturality at a triangle's last arrow plus this shift square is precisely
  compatibility with its image connecting arrows. These clauses are reused rather
  than duplicated in this module.
- The b_u over each coefficient is the existing `groupMap`; its mate and counit
  normalization are `groupMap_mate` from the stated dependency.
- For arbitrary N, N' and f the coefficient map is the existing `coefficientMap a f`.
  The first composite in `scalarRestrictionInterchange_transposes` uses
  `groupDerived.map f ≫ scalarGroupDerived.hom.app N'`, retaining the localized
  underlying identity Us_J = s_H U'. The second composite is
  `coefficientMap a f ≫ scalarBase.map (groupMap A' v).app N'`.
- The equality of those composites is already stated verbatim by `coefficientSquare`
  in `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`, whose node cites this
  item as a proof dependency. That module is not imported, to avoid the dependency
  cycle, and its equality is not duplicated. The new theorem gives the stronger
  requested information of the specified common transpose for each side.
- `scalarInvariantTranspose` is L_G(z), followed by chi and s_G(epsilon'_G).
  `scalarInvariantTranspose_composite` identifies it with precisely the composite
  Hom bijection in the statement: transpose across e_0, then the primed invariant
  adjunction, precompose the left comparison, then transpose back across e_G.
- Both conjuncts of `scalarRestrictionInterchange_transposes` equal
  `restrictionTrivialDerived.hom ≫ U.map epsilon_G ≫ U.map f ≫ scalarGroupDerived.hom`.
  Thus the common transpose is exactly U(epsilon_G);U(f), with both stipulated
  underlying identity transports visible, in the required derived action category.
  All equations are equations of derived arrows; no homology functor is applied.
- There is no flatness assumption on a and no preservation-of-injectives hypothesis
  for scalar or group restriction anywhere in the delivered signatures.

Dependency declarations used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, reexported by
  `Sheaf.CategoryTheory.CondensedActionModule`. Mathlib
  `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `ModObj`, and `Mod.comap`.
- `Sheaf.CategoryTheory.CondensedActionModule`: the recorded `ActionModule`, section
  actions, `trivial`, and the normalized `Invariants` datum. Their bundled coefficient
  specializations `Ring`, `Modules`, `Equivariant` are those publicly imported by
  `Sheaf.CategoryTheory.CondensedDerivedInvariants` from `CondensedEquivariantBarData`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`; `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, `mapDerivedCategoryFactors`.
- `Sheaf.CategoryTheory.CondensedDerivedInvariants`: `invariants`, `derived`,
  `trivialDerived`, `adjunction`, `groupDerived`, `groupMap`, `scalarAction`,
  `scalarDerived`, `scalarBase`, `scalarInvariants`, `scalarComparison`,
  `coefficientMap`, `scalarGroupDerived`, and the normalization/shift theorems above.
- `Sheaf.CategoryTheory.CondensedRestrictionMateNormalization`:
  `restrictionTrivialDerived` and `groupMap_mate`.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `Mod.derivedExtendMapDerivedCategoryAdjunction`, publicly available through the
  invariant dependency; it supplies the designated model of the base scalar adjoint.
- `Sheaf.CategoryTheory.ActionToposGeometricRestriction`:
  `InternalActionSite.GeometricRestriction`, its coefficient squares and its exact
  module pullbacks; `InternalActionSite.geometricRestriction` is the infrastructure
  theorem for the ringed interpretation used in proof step 2.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `RingedDerivedComparisons.ringedDerivedMonoidalComparisons` and the public
  `System`, `Composition`, and their normalized pullback/right comparisons.
- Mathlib `CategoryTheory.Adjunction.comp`, `mateEquiv`, `conjugateIsoEquiv`
  in `Adjunction.Basic`/`Adjunction.Mates` implement the three categorical-definition
  proof dependencies; `Shift.CommShift` supplies the composition/whiskering calculus.
- Proof-only imports: `Sheaf.Paper.KFlatScalarComparisonNormalization`,
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, and the three
  `Sheaf.SixFunctors.RingedDerivedAdjointLift`,
  `RingedDerivedCompositionComparison`, `RingedDerivedTwoIsoComparison` modules.
  The action-injective-infrastructure node has no recorded module; its structures
  needed to type these statements are already supplied by `CondensedDerivedInvariants`.

Edge cases checked before writing: trivial groups and identity group maps reduce the
mate and transpose formulas to the adjunction triangle identities; a zero object or
zero f gives zero on both sides; identity scalar maps specialize to the normalized
identity comparisons; nonflat coefficient quotients are allowed without any change
of hypotheses; arbitrary unbounded complexes remain in the domain. Empty profinite test
objects are included by the existing action and fixed-section definitions. Neither an
empty group (impossible for a Group) nor a choice of an index set is assumed. All variables
and the universe are explicit, with `set_option autoImplicit false`.

Searches actually run:

1. `msearch.py ... leanfinder` with query "Derived invariants commute with scalar
   restriction and group restriction, conjugate of extension of scalars comparison".
   Result: eight hits for ordinary `groupCohomology.H1InfRes_*`,
   `groupHomology.H1CoresCoinf_*`, and `Rep.invariantsFunctor_map_hom`; none is an
   unbounded condensed scalar/group comparison.
2. `msearch.py ... loogle 'Adjunction.conjugateEquiv'` returned zero hits with
   "unknown identifier". This was a namespace miss, not a claim that conjugation
   is absent; the recorded dependency and Mathlib source give the correct
   `CategoryTheory.conjugateEquiv` and `CategoryTheory.conjugateIsoEquiv`.
3. `msearch.py ... grep 'scalarComparison|coefficientMap|scalar.*[Ii]nterchange'`
   returned zero Mathlib hits.
4. `msearch.py ... leansearch` with query "Derived invariants of condensed modules
   commute with restriction of scalars and restriction of group actions" returned
   eight hits: `ModuleCat.restrictScalars`, `RestrictScalars`,
   `ContinuousCohomology.invariants`, and ordinary scalar restriction constructions.
   These are not the internal condensed categories of the item.
5. Direct `rg` searches for scalar/trivial, scalar/conjugate, scalar/mate, and
   `coefficientSquare` across `lean/WeilConjectures` and `lean/Sheaf` located the
   dependency scalarComparison, scalarComparisonShift, scalarGroupDerived, and the
   downstream coefficientSquare. The delivered file reuses those constructions.
6. `grep -rn 'lem-sfb-condensed-scalar-restriction-interchange'
   lean/WeilConjectures` found no attachment. A search for the new declaration names
   in `dag/lean_names_upstream.json`, Mathlib's category theory, and upstream category
   theory found no existing names.

Validation: the complete module compiled via `scompile.py` against the current published
server library, both under its sandbox name and its delivered module name, with no errors
or warnings. The prescribed deliver2.py --no-push dry run passed preflight and compilation
(commit f4fdea832ba); final delivery uses the same checked module and node record.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
