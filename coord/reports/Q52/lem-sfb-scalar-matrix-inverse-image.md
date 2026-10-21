## Worker report

The new module `Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage` states
`AlgebraicGeometry.ProEtale.scalarMatrix_inverseImage` with its whole proof `sorry`.
Its two helper definitions construct the canonical regular-module comparison and its
finite-biproduct extensions with real data. No theorem is proved in this delivery.
The node is changed only in `lean`; no new nodes, dependency repairs, or statement
correction are needed.

Source read: the main-20261015 blueprint's
`sec-six-functors-basics/sk-prop-proper-base-change-unbounded/` 
`sk-prop-proper-base-change-unbounded-pullback.proof.md`, paragraph “Constructible
complexes”, especially “via the local coefficient models on strata”. The item's
six-step proof makes the scalar and universal-property argument explicit; every step
is retained in the theorem docstring. The source establishes preservation for arbitrary
pullback through these local models, with no restriction on the scheme morphism.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A general commutative condensed ring is bound by
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]`. This is the unbundled form of `Profinite.CondensedRing`,
  the existing `Mon` encoding; it does not assume a presentation by a topological ring.
- The scalar ring R = Λ(*) is the existing `scalarRingObj Λ`. An element is encoded
  by `𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ`, i.e. a homomorphism ℤ → R, determined
  uniquely by its value at 1. No scalar sections are chosen on U or V.
- Schemes and the arbitrary morphism h : V → U are `{V U : Scheme.{u}} (h : V ⟶ U)`.
  There are no finiteness, separatedness, nonemptiness, or étaleness hypotheses.
- Their small pro-étale sites and coefficient rings are the existing
  `Scheme.ProEt.topology U`, `Scheme.ProEt.topology V` and `condensedRingObj Λ U/V`.
  The coefficient-category universe is u+1 while the scheme universe is u.
- The canonical α_h is `condensedPullbackHom Λ h`, the component of the canonical
  `upperStarFromPointComp`, with its existing `IsMonHom` and `IsIso` instances.
  The module pullback is exactly `CondensedRing.upperStar Λ h`, defined by transport
  and extension of scalars along this forward coefficient map.
- Nonnegative m and n are `{m n : ℕ}`. The matrix is
  `A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)`.
  This is the dependency's column-then-row convention: A j i is the node's a_ij.
  It parametrizes exactly all n-by-m scalar matrices, including empty matrices.
- A_U and A_V are `scalarMatrix Λ U A` and `scalarMatrix Λ V A` with literally
  the same A. Their dependency definition uses `scalarSection`, hence the canonical
  scalar maps, and `Mod.regularLift` as the entrywise multiplication map.
- Finite free modules are `Mod.finiteFree (condensedRingObj Λ U/V) r`, the existing
  finite biproducts of regular modules from `ModuleObjects.Free`.
- The regular comparison is `scalarMatrixRegularPullbackIso Λ h`. It applies
  extension of scalars to the inverse of the existing `Functor.mapModUnitIso`,
  identifying transported regular modules, and then uses `Mod.regularExtensionIso`.
  The latter is constructed from the extension/restriction adjunction and sends
  b ⊗ x to b α_h(x). Thus this is the node's specified comparison, with no arbitrary
  isomorphism or existence choice.
- Its finite-coproduct extensions e_r are `scalarMatrixFreePullbackIso Λ h r`:
  the existing `Functor.mapBiproduct` followed by `biproduct.mapIso` of r copies of
  the regular comparison. There are no local instances or private definitions.
- The first conjunct reads `H.map A_U ≫ e_n.hom = e_m.hom ≫ A_V`.
  Lean's `≫` is diagrammatic composition; this is precisely e_n ∘ H(A_U) = A_V ∘ e_m.
- The second conjunct supplies `∃ e : H.obj (cokernel A_U) ≅ cokernel A_V`.
  These cokernels are in the module-object categories, not the underlying sheaf category.
- The final equation is `H.map (cokernel.π A_U) ≫ e.hom = e_n.hom ≫ cokernel.π A_V`:
  exactly compatibility with the two cokernel projections. This equation determines
  the induced isomorphism uniquely, because the transported cokernel projection is epic.
  The existential statement therefore retains the canonical induced comparison.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`; its `Mon` encoding
  is unfolded in the input binders as the existing framework convention.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `Scheme.ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `isCommMonObj_condensedRingObj`, `coefficientPullbackIso`,
  `condensedPullbackHom`, and its ring-morphism/isomorphism instances. Its docstrings
  specify transport from the condensed point and the canonical comparison, not an
  arbitrary ring map.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`, its additivity and finite-colimit preservation, and
  `CondensedRing.upperStarLowerStarAdjunction`. Their full signatures and construction
  were read; no interface repair is needed.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`: `scalarSections`, `scalarRingObj`,
  `scalarCoefficientHom`, `scalarSection`, and `scalarMatrix`. In particular the scalar
  map is the inverse image of the constant-sheaf counit, and the matrix's first index
  is explicitly the input column.
- `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `Mod.finiteFree` and
  `Mod.IsFinitelyPresented`. The node `def-sfb-finitely-presented-module` has no lean
  record, but its closed upstream audit names this exact module and declaration.
- Supporting canonical constructions: `Functor.mapModUnitIso` from
  `WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal`,
  `Mod.regularExtensionIso` from `Sheaf.Paper.RegularExtensionComparison`, and
  Mathlib's `Functor.mapBiproduct`, `biproduct.mapIso`, and module-category `cokernel`.
- Proof-plan imports also retain `Sheaf.CategoryTheory.SheafTensor`,
  `Mathlib.CategoryTheory.Monoidal.Bimod` (the recorded `Bimod.rightUnitorBimod`),
  and `Mathlib.CategoryTheory.Adjunction.Limits` (left adjoints preserve colimits).
  Module transport and extension-of-scalars proof dependencies are supplied by their
  existing upstream modules imported transitively through the public interface above.

Edge cases checked before writing: rank zero is allowed on either side and both sides;
`Fin 0` gives an empty biproduct, whose comparison is still defined. For m=0 the
cokernel is the rank-n module; for n=0 it is zero. A zero matrix gives the same
comparison on the target. The zero coefficient ring gives zero regular modules and
zero cokernels without extra assumptions. Empty schemes and identity morphisms are
included, as are non-pro-étale morphisms. There is no characteristic, completeness,
Noetherian, finite-presentation-on-the-ring, or nonzero-ring restriction.

Searches actually run:

- `msearch.py`, leanfinder, “Pullback of scalar matrices between finite free condensed
  coefficient module sheaves preserves the matrix and its cokernel”: 8 hits, including
  `SheafOfModules.pullbackObjFreeIso`, its naturality/generator lemmas,
  `freeFunctorCompPullbackIso`, and `SheafOfModules.Presentation.map_π_eq`.
  These are supporting results for a different sheaf-module encoding and do not state
  the canonical condensed-point scalar square and cokernel comparison here.
- `msearch.py`, loogle, `SheafOfModules.pullbackObjFreeIso`: 5 hits consisting of that
  isomorphism and its naturality/generator lemmas; none is the required statement.
- `msearch.py`, grep, `pullbackObjFreeIso|mapBiproduct|cokernel.mapIso`, scoped to
  `Algebra/Category/ModuleCat/Sheaf`: 5 hits in `PullbackFree.lean`, likewise supporting
  free-sheaf results, with no exact match.
- `msearch.py`, leansearch, “Inverse image preserves finite scalar matrices and
  cokernels of condensed coefficient modules”: 8 hits, mostly general inverse-image
  predicates and submodule preimage lemmas, plus preservation of coimages. No exact match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for `scalarMatrix`,
  `regularExtensionIso`, upperStar/free combinations, and the item id found the existing
  scalar matrix in `FiniteConstantLocalModel`, the general `RegularExtensionComparison`,
  and applications to lisse/local free modules. It found no scalar-matrix inverse-image
  statement. The existing constructions are reused.
- The item-id search in `lean/WeilConjectures` had no hits. The names
  `scalarMatrixRegularPullbackIso`, `scalarMatrixFreePullbackIso`, and
  `scalarMatrix_inverseImage` had no hits in Mathlib, either project source root,
  or `dag/lean_names_upstream.json` before this delivery.

Validation: `scompile.py` compiled the file both as a sandbox module and under its
final library module name, cleanly (5.4 s and 5.0 s) after correcting an implicit
argument to `mapModUnitIso`. All universes and variables are explicitly bound;
`autoImplicit` is false. The sole postponed proof is the named main theorem, whose
matching DAG node and six-step proof docstring are supplied. No statement dispute
or node fault was found.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
