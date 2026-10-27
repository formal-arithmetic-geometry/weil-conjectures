## Worker report

Q119 states `AlgebraicGeometry.ProEtale.normed_locallyFree_geometric_matrix_test` in
`Sheaf.Paper.NormedLocallyFreeGeometricMatrixTest`. Its proof is `sorry`; the three helpers
construct the canonical finite-free pullback comparison, its action on arrows, and the
continuous matrix of the pulled-back arrow. Their data are fully specified composites,
not choices from undetermined existence. The theorem docstring gives the six-step proof.

Hypothesis-by-hypothesis and clause-by-clause reading:

- Compatible universes: `F : Type u`, `T : Scheme.{u}`, site objects in `u+1`, morphisms
  in `u`, abelian coefficients in `u+1`. The scheme and field can be enlarged together.
  Geometric test fields are in the scheme universe, containing algebraic closures of
  every residue field; no independent smaller test universe makes the hypothesis vacuous.
- The normed field and metric topology are `[NormedField F]`; total disconnectedness
  is `[TotallyDisconnectedSpace F]`. No completeness or nontrivial norm is assumed.
- `C_F(P)=C(P,F)` is the existing `condensedFieldCoefficientRingObj F`, which unfolds
  to `Profinite.continuousCoefficientRingObj F`. A module-mode scratch probe compiled
  `Profinite.continuousMapRingObjOfUniverse.{u,u} F = condensedFieldCoefficientRingObj F`
  with proof `rfl`. Thus this is the recorded continuous-map notion, with its existing
  pointwise ring structure, rather than a second definition.
- `F_T=p_T^*C_F` is `condensedRingObj (condensedFieldCoefficientRingObj F) T`.
- M,N are internal modules in `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) ...`.
- Finite constant local models are exactly `hM` and `hN`, using the existing predicate
  `HasFiniteConstantLocalModel`. The recorded `finiteConstantLocalModel_iff_exists_cover`
  identifies it with explicit scalar extensions of finitely presented scalar modules.
- `h : M ⟶ N` is a morphism in that internal-module category.
- `hy` quantifies over every `k : Type u` with `[Field k] [IsAlgClosed k]` and
  `y : Spec (.of k) ⟶ T`. The map is literally the underlying abelian sheaf component
  of `(CondensedRing.upperStar ... y).map h`, at
  `op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))`. This is global sections of the actual
  ringed module inverse image. `Function.Bijective` is equivalent to invertibility
  of its F-linear map: linearity for the constant-section F action already follows
  from the module morphism. No arbitrary evaluation functor is quantified over.
- Global conclusion: `IsIso h`.
- Common pro-etale cover: existential `𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage T`.
- Finite free local models: `n m : 𝒰.I₀ → ℕ` and isomorphisms `eM`, `eN` from the actual
  module inverse images to `Mod.finiteFree` over the intrinsic coefficient on `𝒰.X j`.
- The displayed arrow in those models is d, constrained by
  `d = (eM j).inv ≫ upperStar.map h ≫ (eN j).hom`.
- Its continuous rectangular matrix A is constrained to be the existing
  `continuousFieldPresentationMatrix` through the canonical
  `condensedFieldContinuousMapIso`. This construction reads each regular component
  on the unit section. Entries are `C(𝒰.X j,F)`, not arbitrary scalars.
- Geometric matrix evaluation: every `z : Spec k ⟶ 𝒰.X j`, x on its singleton spectrum,
  and row/column a,b satisfies `matrixTestPullbackMatrix F z d a b x = A a b (z x)`.
  The helper uses the actual inverse image in canonical transported standard bases.
  On the singleton spectrum these entries are precisely the constants `A(z(x))`.
- Inverse g goes between the same finite-free models in the reverse direction, with
  both `d ≫ g = 𝟙 _` and `g ≫ d = 𝟙 _`. B is its matrix in the same realization.
- For every pro-etale object V over `𝒰.X j`, the matrices of the actual pulled-back
  d and g equal A and B precomposed by `V.hom.base.hom`. Both pulled-back arrows satisfy
  both inverse identities. Thus the inverse is compatible with every restriction.
- `Nonempty (𝒰.X j) → ∃ e : m j = n j` imposes rank equality only on nonempty members.
  `Fin.cast e.symm` identifies rows of A and columns of B with `Fin (n j)`. The square
  A has nonzero determinant at every point, and the square B is exactly
  `det(A(x))⁻¹ • A(x).adjugate`. Each entry of B is already a continuous map; a finite
  family of continuous entries is a continuous matrix function.
- No noetherianity or stratification of T appears among the binders.

Dependency signatures and docstrings read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`: `Profinite.continuousMapRingObjOfUniverse`,
  its ring presheaf and ring sheaf; its coefficient encoding is checked above.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `condensedPullbackHom`, its invertible monoid comparison.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`, its extension-of-scalars definition and composition.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `finiteConstantLocalModel_iff_exists_cover`, `HasFiniteConstantLocalModelOnCover`,
  `finiteConstantScalarExtension`, and the imported shared `HasFiniteConstantLocalModel`
  from `Sheaf.Paper.CondensedConstantConstructibility`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are inline
  per the node record. Also read `Scheme.SpecToEquivOfField` and its full signature in
  Mathlib.AlgebraicGeometry.ResidueField.
- Added two already landed statement-dependency nodes (no new nodes):
  `def-weil-pbc-condensed-field-presentation-matrix`, declaration
  `AlgebraicGeometry.ProEtale.continuousFieldPresentationMatrix` in
  `Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix`, and
  `lem-weil-pbc-condensed-field-continuous-realization`, declaration
  `AlgebraicGeometry.ProEtale.condensedFieldContinuousMapIso` and its uniquely
  determining adjoint test equations in
  `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`.
- Canonical helper data use `Functor.mapBiproduct`, `biproduct.mapIso`,
  `Mod.extendScalarsIsoComapInv`, `Mod.regularIsoOfIsIso`. Their source signatures were
  read; the scalar-change signature was also checked by server `#check`.

Every recorded proof dependency with a module is imported plainly; Mathlib leaves
are imported by their actual modules. `lem-sfb-ringed-site-free-matrix-scalar-extension`
is unstated and has no module to import; the already landed continuous matrix
construction supplies the notion used to state this theorem. No proof is manufactured.

Edge cases: empty T permits the empty cover and zero sheaves; an empty member retains
possibly different displayed ranks because the equality/determinant clause is guarded
by Nonempty; rank zero gives determinant 1 and empty matrices; on nonempty members
zero source/target ranks must agree by the geometric hypothesis. Trivially normed and
incomplete fields are allowed. Ranks need not be uniformly bounded along the cover.

Searches performed using msearch.py:

- LeanFinder: `Geometric evaluation detects isomorphisms of locally finite free sheaves
  of continuous normed field coefficients`: eight hits including ordinary scheme-module
  and locally bijective sheaf tests, none states the requested continuous geometric test.
- LeanSearch: `A morphism of locally finite free sheaves of continuous functions is an
  isomorphism if its geometric fibre maps are invertible`: eight ordinary stalk/sheaf
  isomorphism hits; none for these pro-etale internal modules.
- Loogle `Continuous, Matrix.det`: `Continuous.matrix_det` and
  `Matrix.SpecialLinearGroup.continuous_apply`; matrix continuity tools, not this theorem.
- grep `continuous.*(matrix|adjugate)|[Ii]sIso.*geometric` in Mathlib Topology:
  continuous matrix tools, no full match.
- rg of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and upstream names for the four
  proposed declaration names: no duplicate. Concept searches found the existing matrix
  and continuous realization APIs, which are reused. `grep -rn` of this node id in
  WeilConjectures found no match. DAG searches located those APIs' existing nodes.

Source checked: HRS PDF, Example 3.1 and opening Section 3; latest blueprint finite
constant local-model definition and enclosing six-functor unit. No statement correction
or disputed assertion. No subagent was started, as expressly required by the dispatcher.

Validation: the exact Lean module passed scompile.py both as sandbox and under its
final module name, exit 0 and no warnings. Shared slot waiting accounts for the elapsed
1124.9 and 1032.8 seconds; no per-file limit was changed. The independent coefficient
identity probe also compiled. Delivery dry run passed at 29f4525a121. Between that dry
run and the push command the entire sandbox directory disappeared externally; the
push reported zero node files. This packet restores the exact compiled Lean file and
node record, with this rewritten report, and reruns the prescribed checks and delivery.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
