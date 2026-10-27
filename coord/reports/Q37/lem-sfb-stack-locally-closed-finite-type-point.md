## Worker report

The module `Sheaf.AlgebraicGeometry.StackLocallyClosedFiniteTypePoint` defines
`CategoryTheory.finiteTypeModuliPoints` and states
`CategoryTheory.stack_locallyClosed_inter_finiteTypePoints_nonempty` with `sorry`.
The node's statement and all its other fields are unchanged; only `lean` is attached.
The finite-type point set is a helper explicitly belonging to the item's own statement,
not a separate notion imported from an unstated node. Its definition has real data and
no postponed proof. There is one postponed theorem, exactly the item.

Source read: Stacks `stacks-morphisms.tex`, section-points-finite-type, Tag 06FX
(lemma-point-finite-type), Tag 06FY (definition-finite-type-point), and Tag 06G2
(lemma-enough-finite-type-points), first assertion. The definition follows condition (1)
of 06FX, rather than replacing it by closedness of the point. The theorem docstring
carries all three accepted DAG proof steps, including the arbitrary-scheme application
and the field-extension lifting argument. The latest blueprint was searched for
06G2/06FY/06FX and finite type points; it has no duplicate formulation of this lemma.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; there is no condition on S.
- The arbitrary algebraic stack over S is
  `(F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)`.
  The recorded predicate means a stack fibred in groupoids, an algebraic-space diagonal,
  and existence of a smooth surjective scheme atlas. Its definition and the definitions
  of `IsModuliStack`, `HasAlgebraicSpaceDiagonal`, and `IsSmoothModuliAtlas` were read.
  Neither a chosen atlas nor a Deligne--Mumford hypothesis is added.
- Its point set is the existing `ModuliPoints F`: the quotient of actual field objects
  by arrows over field extensions, taking equivalence closure. The topology instance is
  `moduliPointTopologicalSpace`, from the recorded topology dependency. It is the final
  topology for all smooth surjective scheme atlases, not an arbitrary topology supplied
  as an additional hypothesis.
- The finite-type representative is quantified as `(K : Type u) (_ : Field K)` together
  with `(b : Spec (.of K) ⟶ S)` and the actual morphism
  `(a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) F)`.
  BasedFunctor is the existing morphism convention for fibred groupoids. Maps from a
  represented scheme into a CFG are the 2-Yoneda formulation of objects over that scheme.
- Local finite type of this representative is
  `ModuliSpaceTest @LocallyOfFiniteType a`. This existing predicate requires an actual
  algebraic-space presentation of every scheme 2-base change and local finite type of
  its projection on every etale scheme chart. For a morphism from a scheme to an
  algebraic stack representability follows from the diagonal, so this is not an extra
  representability restriction. Etale charts of the resulting algebraic spaces give
  the same property as the node's smooth-chart convention, by smooth locality of local
  finite type. The general chartwise calculus uses precisely this predicate; the
  DM-only `IsLocallyFiniteTypeModuliMap` is deliberately not used.
- Membership in the represented point class is
  `x ∈ Set.range (moduliSchemePointMap a)`. The source of this map is the usual scheme
  point set of Spec K, which has exactly one point. Thus the range is precisely the
  class of a; it does not quantify an unrelated point or an arbitrary map on point sets.
  The range also avoids any choice of a prime or any new representative construction.
- The subset is `(Z : Set (ModuliPoints F))`; `(hZ : IsLocallyClosed Z)` uses Mathlib's
  definition `∃ U C, IsOpen U ∧ IsClosed C ∧ Z = U ∩ C`, exactly the stated convention.
- `hne : Z.Nonempty` is equivalent to the node's `Z ≠ ∅`. The conclusion
  `(Z ∩ finiteTypeModuliPoints F).Nonempty` is exactly the required nonempty intersection.
- There are no Jacobson, Noetherian, quasi-compactness, separatedness, characteristic,
  finite-type-over-S, or field-finiteness hypotheses. The independent `v,w` universes of
  the total category remain unrestricted; fields and test schemes use the existing
  `Scheme.{u}` convention throughout.

Dependency declarations used (full signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, and `Spec.map`; schemes and morphisms are used unchanged.
- `Mathlib.Algebra.Field.Defs`: `Field`, reached by the public imports; its signature
  extends `CommRing` and `DivisionRing`, and excludes the zero ring.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, the all-affine-pairs finite generation test.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, the recorded
  scheme notion in the atlas predicates.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `IsFibredInGroupoids`, `ModuliTwoIso`, `moduliTwoFiberProduct`, `HasSpaceBaseChange`,
  `IsModuliStack`, `HasAlgebraicSpaceDiagonal`, and the representability conventions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsEtale`, used by the chart test and algebraic-stack predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack` and
  `IsSmoothModuliAtlas`, reached through the topology dependency.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliFieldObject`,
  `ModuliFieldRelation`, `ModuliPoints`, `moduliPointMap`, and `ModuliSpaceTest`;
  these general definitions are reached through the topology dependency.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`: `moduliSchemePointMap`,
  `moduliPointTopologicalSpace`, and `stackPointTopology_flat_lfp_open`.
- Proof import `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `stack_chartwise_smooth_etale_calculus`, `stack_chartwise_comp`,
  `stack_chartwise_implications`, and `IsSurjectiveModuliMap`.
  The proof dependency `lem-sfb-finite-type-points-detect-open` has no Lean record,
  mathlib match, or upstream declaration in the current node, so there is no module
  to import for that proof step yet. This does not affect the statement's interface.

Edge cases checked before writing:

- Empty S or empty stack: no nonempty Z exists; the implication is vacuous.
- Empty Z is not excluded from the subset binder; it simply cannot satisfy hne.
- A field spectrum: the identity is locally finite type, and its unique point lies in
  the defined set. Arbitrary field spectra over an arbitrary base remain available.
- A non-Jacobson scheme, including a DVR: locally closed generic points can be finite
  type without being closed in the whole scheme. No `closedPoints` predicate is used.
- A stack such as BG_m is permitted: a smooth atlas suffices, without etale atlas or
  trivial stabilizers. The field representative is representable by algebraic spaces,
  even though the stack's structure morphism need not be representable.
- Non-Noetherian, non-quasi-compact atlases: local finite type tests every chart and does
  not impose a finite cover or quasi-compactness on the representative.
- Fields have no characteristic restriction. Universe choices do not place test schemes
  in a universe below the base scheme.

Searches for an existing statement/definition (all prescribed msearch commands ran):

- LeanFinder: "Every nonempty locally closed subset of an algebraic stack contains a
  finite type point". Eight hits: scheme local finite type, Jacobson closed points, and
  generic scheme topology. None defines this stack finite-type point set or states 06G2.
- Loogle: "IsLocallyClosed, LocallyOfFiniteType". Zero hits; the service reports the
  unqualified identifier `LocallyOfFiniteType` unknown.
- LeanSearch: "finite type points of an algebraic stack meet every nonempty locally
  closed subset". Eight hits, including `nonempty_inter_closedPoints` and
  `jacobsonSpace_iff_locallyClosed`, both requiring a Jacobson space; not this statement.
- msearch grep: `ModuliFiniteType|finiteTypePoint|finite_type_point|AlgebraicStack`.
  Zero Mathlib hits. Direct rg in Mathlib finds the existing scheme local-finite-type
  and topology definitions, which are reused.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for those names and locally-closed
  finite-type formulations: no duplicate. The nearby derived-stratum lemmas concern
  finite-type scheme morphisms, not finite-type points of stacks.
- The required `grep -rn` of the item id in `lean/WeilConjectures` returns no hits.
- The proposed names `finiteTypeModuliPoints` and
  `stack_locallyClosed_inter_finiteTypePoints_nonempty` do not occur in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, or `dag/lean_names_upstream.json`.
- DAG searches for finite-type points locate this item's definition, the scheme lemma,
  the residual-substack lemma, and the smooth-closed-chart characterization; no separate
  recorded definition of this stack finite-type point set is available.

No statement correction, disputed statement, new definition node, or dependency repair
is needed. The example Sheaf CompactObject module is withdrawn in the current checkout;
its node now points to the upstream CompactObject module, which was also read.

Validation: the module passes scompile.py in both sandbox and library contexts
(14.8 s and 3.4 s). No errors or non-sorry warnings were returned. All variables and
universes are explicit, with `autoImplicit false`. No diagnostic commands remain.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
